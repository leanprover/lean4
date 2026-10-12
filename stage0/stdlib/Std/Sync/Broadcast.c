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
lean_object* l_Std_Broadcast_Error_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Error_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Std_Broadcast_Error_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Std_Broadcast_Error_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Std_Broadcast_Error_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Error_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Std_Broadcast_Error_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Std_Broadcast_Error_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___redArg(lean_object* v_closed_24_){
_start:
{
lean_inc(v_closed_24_);
return v_closed_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___redArg___boxed(lean_object* v_closed_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_Broadcast_Error_closed_elim___redArg(v_closed_25_);
lean_dec(v_closed_25_);
return v_res_26_;
}
}
lean_object* l_Std_Broadcast_Error_closed_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_closed_30_){
_start:
{
lean_inc(v_closed_30_);
return v_closed_30_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Error_closed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_closed_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Std_Broadcast_Error_closed_elim(lean_box(0), v_t_28_, lean_box(0), v_closed_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_closed_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_closed_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Std_Broadcast_Error_closed_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_closed_35_);
lean_dec(v_closed_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___redArg(lean_object* v_alreadyClosed_38_){
_start:
{
lean_inc(v_alreadyClosed_38_);
return v_alreadyClosed_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___redArg___boxed(lean_object* v_alreadyClosed_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_Broadcast_Error_alreadyClosed_elim___redArg(v_alreadyClosed_39_);
lean_dec(v_alreadyClosed_39_);
return v_res_40_;
}
}
lean_object* l_Std_Broadcast_Error_alreadyClosed_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_alreadyClosed_44_){
_start:
{
lean_inc(v_alreadyClosed_44_);
return v_alreadyClosed_44_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Error_alreadyClosed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_alreadyClosed_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Std_Broadcast_Error_alreadyClosed_elim(lean_box(0), v_t_42_, lean_box(0), v_alreadyClosed_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_alreadyClosed_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_alreadyClosed_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Std_Broadcast_Error_alreadyClosed_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_alreadyClosed_49_);
lean_dec(v_alreadyClosed_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___redArg(lean_object* v_notSubscribed_52_){
_start:
{
lean_inc(v_notSubscribed_52_);
return v_notSubscribed_52_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___redArg___boxed(lean_object* v_notSubscribed_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_Broadcast_Error_notSubscribed_elim___redArg(v_notSubscribed_53_);
lean_dec(v_notSubscribed_53_);
return v_res_54_;
}
}
lean_object* l_Std_Broadcast_Error_notSubscribed_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_notSubscribed_58_){
_start:
{
lean_inc(v_notSubscribed_58_);
return v_notSubscribed_58_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Error_notSubscribed_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_notSubscribed_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Std_Broadcast_Error_notSubscribed_elim(lean_box(0), v_t_56_, lean_box(0), v_notSubscribed_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_notSubscribed_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_notSubscribed_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Std_Broadcast_Error_notSubscribed_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_notSubscribed_63_);
lean_dec(v_notSubscribed_63_);
return v_res_65_;
}
}
static lean_object* _init_l_Std_Broadcast_instReprError_repr___closed__6(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Std_Broadcast_instReprError_repr___closed__7(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
lean_object* l_Std_Broadcast_instReprError_repr(uint8_t v_x_79_, lean_object* v_prec_80_){
_start:
{
lean_object* v___y_82_; lean_object* v___y_89_; lean_object* v___y_96_; 
switch(v_x_79_)
{
case 0:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_prec_80_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_82_ = v___x_104_;
goto v___jp_81_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_82_ = v___x_105_;
goto v___jp_81_;
}
}
case 1:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1024u);
v___x_107_ = lean_nat_dec_le(v___x_106_, v_prec_80_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_89_ = v___x_108_;
goto v___jp_88_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_89_ = v___x_109_;
goto v___jp_88_;
}
}
default: 
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1024u);
v___x_111_ = lean_nat_dec_le(v___x_110_, v_prec_80_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__6, &l_Std_Broadcast_instReprError_repr___closed__6_once, _init_l_Std_Broadcast_instReprError_repr___closed__6);
v___y_96_ = v___x_112_;
goto v___jp_95_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Std_Broadcast_instReprError_repr___closed__7, &l_Std_Broadcast_instReprError_repr___closed__7_once, _init_l_Std_Broadcast_instReprError_repr___closed__7);
v___y_96_ = v___x_113_;
goto v___jp_95_;
}
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_83_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__1));
lean_inc(v___y_82_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___y_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
v___x_87_ = l_Repr_addAppParen(v___x_86_, v_prec_80_);
return v___x_87_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__3));
lean_inc(v___y_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___y_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_92_);
v___x_94_ = l_Repr_addAppParen(v___x_93_, v_prec_80_);
return v___x_94_;
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_97_ = ((lean_object*)(l_Std_Broadcast_instReprError_repr___closed__5));
lean_inc(v___y_96_);
v___x_98_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_98_, 0, v___y_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = 0;
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_99_);
v___x_101_ = l_Repr_addAppParen(v___x_100_, v_prec_80_);
return v___x_101_;
}
}
}
LEAN_EXPORT void l_Std_Broadcast_instReprError_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_79_ = stack[0].m_num;
lean_object* v_prec_80_ = stack[1].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Std_Broadcast_instReprError_repr(v_x_79_, v_prec_80_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instReprError_repr___boxed(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
uint8_t v_x_171__boxed_117_; lean_object* v_res_118_; 
v_x_171__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_Std_Broadcast_instReprError_repr(v_x_171__boxed_117_, v_prec_116_);
lean_dec(v_prec_116_);
return v_res_118_;
}
}
uint8_t l_Std_Broadcast_Error_ofNat(lean_object* v_n_121_){
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
LEAN_EXPORT void l_Std_Broadcast_Error_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_121_ = stack[0].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_Std_Broadcast_Error_ofNat(v_n_121_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Error_ofNat___boxed(lean_object* v_n_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Std_Broadcast_Error_ofNat(v_n_130_);
lean_dec(v_n_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
uint8_t l_Std_Broadcast_instDecidableEqError(uint8_t v_x_133_, uint8_t v_y_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_135_ = lean_box(v_x_133_);
v___x_136_ = lean_obj_tag_nat(v___x_135_);
lean_dec(v___x_135_);
v___x_137_ = lean_box(v_y_134_);
v___x_138_ = lean_obj_tag_nat(v___x_137_);
lean_dec(v___x_137_);
v___x_139_ = lean_nat_dec_eq(v___x_136_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Std_Broadcast_instDecidableEqError_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_133_ = stack[0].m_num;
uint8_t v_y_134_ = stack[1].m_num;
uint8_t v_res_140_;
v_res_140_ = l_Std_Broadcast_instDecidableEqError(v_x_133_, v_y_134_);
stack->m_num = v_res_140_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instDecidableEqError___boxed(lean_object* v_x_141_, lean_object* v_y_142_){
_start:
{
uint8_t v_x_23__boxed_143_; uint8_t v_y_24__boxed_144_; uint8_t v_res_145_; lean_object* v_r_146_; 
v_x_23__boxed_143_ = lean_unbox(v_x_141_);
v_y_24__boxed_144_ = lean_unbox(v_y_142_);
v_res_145_ = l_Std_Broadcast_instDecidableEqError(v_x_23__boxed_143_, v_y_24__boxed_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
uint64_t l_Std_Broadcast_instHashableError_hash(uint8_t v_x_147_){
_start:
{
switch(v_x_147_)
{
case 0:
{
uint64_t v___x_148_; 
v___x_148_ = 0ULL;
return v___x_148_;
}
case 1:
{
uint64_t v___x_149_; 
v___x_149_ = 1ULL;
return v___x_149_;
}
default: 
{
uint64_t v___x_150_; 
v___x_150_ = 2ULL;
return v___x_150_;
}
}
}
}
LEAN_EXPORT void l_Std_Broadcast_instHashableError_hash_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_147_ = stack[0].m_num;
uint64_t v_res_151_;
v_res_151_ = l_Std_Broadcast_instHashableError_hash(v_x_147_);
stack->m_num = v_res_151_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_instHashableError_hash___boxed(lean_object* v_x_152_){
_start:
{
uint8_t v_x_40__boxed_153_; uint64_t v_res_154_; lean_object* v_r_155_; 
v_x_40__boxed_153_ = lean_unbox(v_x_152_);
v_res_154_ = l_Std_Broadcast_instHashableError_hash(v_x_40__boxed_153_);
v_r_155_ = lean_box_uint64(v_res_154_);
return v_r_155_;
}
}
lean_object* l_Std_instToStringBroadcastError___lam__0(uint8_t v_x_161_){
_start:
{
switch(v_x_161_)
{
case 0:
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
return v___x_162_;
}
case 1:
{
lean_object* v___x_163_; 
v___x_163_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
return v___x_163_;
}
default: 
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
return v___x_164_;
}
}
}
}
LEAN_EXPORT void l_Std_instToStringBroadcastError___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_161_ = stack[0].m_num;
lean_object* v_res_165_;
v_res_165_ = l_Std_instToStringBroadcastError___lam__0(v_x_161_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Std_instToStringBroadcastError___lam__0___boxed(lean_object* v_x_166_){
_start:
{
uint8_t v_x_36__boxed_167_; lean_object* v_res_168_; 
v_x_36__boxed_167_ = lean_unbox(v_x_166_);
v_res_168_ = l_Std_instToStringBroadcastError___lam__0(v_x_36__boxed_167_);
return v_res_168_;
}
}
lean_object* l_Std_instMonadLiftBroadcastIO___lam__0(lean_object* v_00_u03b1_177_, lean_object* v_x_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_apply_1(v_x_178_, lean_box(0));
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_206_; 
v_a_189_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_206_ == 0)
{
v___x_191_ = v___x_180_;
v_isShared_192_ = v_isSharedCheck_206_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_180_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_206_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
uint8_t v___x_193_; 
v___x_193_ = lean_unbox(v_a_189_);
lean_dec(v_a_189_);
switch(v___x_193_)
{
case 0:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
case 1:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_198_);
v___x_200_ = v___x_191_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
default: 
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_202_);
v___x_204_ = v___x_191_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_instMonadLiftBroadcastIO___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_178_ = stack[1].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_Std_instMonadLiftBroadcastIO___lam__0(lean_box(0), v_x_178_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_Std_instMonadLiftBroadcastIO___lam__0___boxed(lean_object* v_00_u03b1_208_, lean_object* v_x_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_instMonadLiftBroadcastIO___lam__0(v_00_u03b1_208_, v_x_209_);
return v_res_211_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(lean_object* v_c_214_, uint8_t v_b_215_){
_start:
{
lean_object* v_promise_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_promise_217_ = lean_ctor_get(v_c_214_, 0);
v___x_218_ = lean_box(v_b_215_);
v___x_219_ = lean_io_promise_resolve(v___x_218_, v_promise_217_);
return v___x_219_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_214_ = stack[0].m_obj;
uint8_t v_b_215_ = stack[1].m_num;
lean_object* v_res_220_;
v_res_220_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_c_214_, v_b_215_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg___boxed(lean_object* v_c_221_, lean_object* v_b_222_, lean_object* v_a_223_){
_start:
{
uint8_t v_b_boxed_224_; lean_object* v_res_225_; 
v_b_boxed_224_ = lean_unbox(v_b_222_);
v_res_225_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_c_221_, v_b_boxed_224_);
lean_dec_ref(v_c_221_);
return v_res_225_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve(lean_object* v_00_u03b1_226_, lean_object* v_c_227_, uint8_t v_b_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_c_227_, v_b_228_);
return v___x_230_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_227_ = stack[1].m_obj;
uint8_t v_b_228_ = stack[2].m_num;
lean_object* v_res_231_;
v_res_231_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve(lean_box(0), v_c_227_, v_b_228_);
stack->m_obj
 = v_res_231_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___boxed(lean_object* v_00_u03b1_232_, lean_object* v_c_233_, lean_object* v_b_234_, lean_object* v_a_235_){
_start:
{
uint8_t v_b_boxed_236_; lean_object* v_res_237_; 
v_b_boxed_236_ = lean_unbox(v_b_234_);
v_res_237_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve(v_00_u03b1_232_, v_c_233_, v_b_boxed_236_);
lean_dec_ref(v_c_233_);
return v_res_237_;
}
}
lean_object* l_Std_instInhabitedSlot_default___redArg(){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = ((lean_object*)(l_Std_instInhabitedSlot_default___redArg___closed__0));
return v___x_242_;
}
}
LEAN_EXPORT void l_Std_instInhabitedSlot_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_243_;
v_res_243_ = l_Std_instInhabitedSlot_default___redArg();
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default___redArg___boxed(lean_object* v___dummy_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_instInhabitedSlot_default___redArg();
return v_res_245_;
}
}
static lean_object* _init_l_Std_instInhabitedSlot_default___closed__0(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Std_instInhabitedSlot_default___redArg();
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_instInhabitedSlot_default(lean_object* v_00_u03b1_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&l_Std_instInhabitedSlot_default___closed__0, &l_Std_instInhabitedSlot_default___closed__0_once, _init_l_Std_instInhabitedSlot_default___closed__0);
return v___x_248_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg(){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_obj_once(&l_Std_instInhabitedSlot_default___closed__0, &l_Std_instInhabitedSlot_default___closed__0_once, _init_l_Std_instInhabitedSlot_default___closed__0);
return v___x_250_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_251_;
v_res_251_ = l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg();
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg___boxed(lean_object* v___dummy_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot___redArg();
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instInhabitedSlot(lean_object* v_a_254_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = lean_obj_once(&l_Std_instInhabitedSlot_default___closed__0, &l_Std_instInhabitedSlot_default___closed__0_once, _init_l_Std_instInhabitedSlot_default___closed__0);
return v___x_255_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(9u);
v___x_270_ = lean_nat_to_int(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_unsigned_to_nat(7u);
v___x_278_ = lean_nat_to_int(v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(13u);
v___x_283_ = lean_nat_to_int(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_285_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__0));
v___x_286_ = lean_string_length(v___x_285_);
return v___x_286_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__17);
v___x_288_ = lean_nat_to_int(v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(lean_object* v_inst_293_, lean_object* v_x_294_){
_start:
{
lean_object* v_value_295_; lean_object* v_pos_296_; lean_object* v_remaining_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_value_295_ = lean_ctor_get(v_x_294_, 0);
lean_inc(v_value_295_);
v_pos_296_ = lean_ctor_get(v_x_294_, 1);
lean_inc(v_pos_296_);
v_remaining_297_ = lean_ctor_get(v_x_294_, 2);
lean_inc(v_remaining_297_);
lean_dec_ref(v_x_294_);
v___x_298_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__5));
v___x_299_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__6));
v___x_300_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__7);
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = l_Option_repr___redArg(v_inst_293_, v_value_295_, v___x_301_);
v___x_303_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_300_);
lean_ctor_set(v___x_303_, 1, v___x_302_);
v___x_304_ = 0;
v___x_305_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set_uint8(v___x_305_, sizeof(void*)*1, v___x_304_);
v___x_306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_299_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__9));
v___x_308_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_box(1);
v___x_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__11));
v___x_312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
v___x_313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_298_);
v___x_314_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__12);
v___x_315_ = l_Nat_reprFast(v_pos_296_);
v___x_316_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
v___x_317_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_314_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*1, v___x_304_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_313_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_307_);
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_309_);
v___x_322_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__14));
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_298_);
v___x_325_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__15);
v___x_326_ = l_Nat_reprFast(v_remaining_297_);
v___x_327_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_325_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*1, v___x_304_);
v___x_330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_324_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18, &l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18_once, _init_l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__18);
v___x_332_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__19));
v___x_333_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_330_);
v___x_334_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg___closed__20));
v___x_335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_331_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*1, v___x_304_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(lean_object* v_00_u03b1_338_, lean_object* v_inst_339_, lean_object* v_x_340_, lean_object* v_prec_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___redArg(v_inst_339_, v_x_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed(lean_object* v_00_u03b1_343_, lean_object* v_inst_344_, lean_object* v_x_345_, lean_object* v_prec_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr(v_00_u03b1_343_, v_inst_344_, v_x_345_, v_prec_346_);
lean_dec(v_prec_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot___redArg(lean_object* v_inst_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed), 4, 2);
lean_closure_set(v___x_349_, 0, lean_box(0));
lean_closure_set(v___x_349_, 1, v_inst_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_instReprSlot(lean_object* v_00_u03b1_350_, lean_object* v_inst_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_instReprSlot_repr___boxed), 4, 2);
lean_closure_set(v___x_352_, 0, lean_box(0));
lean_closure_set(v___x_352_, 1, v_inst_351_);
return v___x_352_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__10));
v___x_380_ = l_Lean_mkAtom(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__12);
v___x_382_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_383_ = lean_array_push(v___x_382_, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__16));
v___x_395_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_396_ = lean_array_push(v___x_395_, v___x_394_);
return v___x_396_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_397_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__17);
v___x_398_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__15));
v___x_399_ = lean_box(2);
v___x_400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___x_398_);
lean_ctor_set(v___x_400_, 2, v___x_397_);
return v___x_400_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__18);
v___x_402_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__13);
v___x_403_ = lean_array_push(v___x_402_, v___x_401_);
return v___x_403_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_404_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__19);
v___x_405_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__11));
v___x_406_ = lean_box(2);
v___x_407_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
lean_ctor_set(v___x_407_, 2, v___x_404_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__20);
v___x_409_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_410_ = lean_array_push(v___x_409_, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__21);
v___x_412_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__9));
v___x_413_ = lean_box(2);
v___x_414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v___x_412_);
lean_ctor_set(v___x_414_, 2, v___x_411_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__22);
v___x_416_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_417_ = lean_array_push(v___x_416_, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__23);
v___x_419_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__7));
v___x_420_ = lean_box(2);
v___x_421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
lean_ctor_set(v___x_421_, 2, v___x_418_);
return v___x_421_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__24);
v___x_423_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__5));
v___x_424_ = lean_array_push(v___x_423_, v___x_422_);
return v___x_424_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_425_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__25);
v___x_426_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__4));
v___x_427_ = lean_box(2);
v___x_428_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_425_);
return v___x_428_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_429_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(lean_object* v_x_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Std_instInhabitedSlot_default___redArg___closed__0));
v___x_433_ = lean_st_mk_ref(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_430_ = stack[0].m_obj;
lean_object* v_res_434_;
v_res_434_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(v_x_430_);
stack->m_obj
 = v_res_434_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0___boxed(lean_object* v_x_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___lam__0(v_x_435_);
return v_res_437_;
}
}
lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(lean_object* v_n_438_, lean_object* v_f_439_, lean_object* v_xs_440_, lean_object* v_k_441_, lean_object* v_acc_442_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_lt(v_k_441_, v_n_438_);
if (v___x_444_ == 0)
{
lean_dec(v_k_441_);
lean_dec_ref(v_f_439_);
return v_acc_442_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_445_ = lean_array_fget_borrowed(v_xs_440_, v_k_441_);
lean_inc_ref(v_f_439_);
lean_inc(v___x_445_);
v___x_446_ = lean_apply_2(v_f_439_, v___x_445_, lean_box(0));
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_add(v_k_441_, v___x_447_);
lean_dec(v_k_441_);
v___x_449_ = lean_array_push(v_acc_442_, v___x_446_);
v_k_441_ = v___x_448_;
v_acc_442_ = v___x_449_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_438_ = stack[0].m_obj;
lean_object* v_f_439_ = stack[1].m_obj;
lean_object* v_xs_440_ = stack[2].m_obj;
lean_object* v_k_441_ = stack[3].m_obj;
lean_object* v_acc_442_ = stack[4].m_obj;
lean_object* v_res_451_;
v_res_451_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_438_, v_f_439_, v_xs_440_, v_k_441_, v_acc_442_);
stack->m_obj
 = v_res_451_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg___boxed(lean_object* v_n_452_, lean_object* v_f_453_, lean_object* v_xs_454_, lean_object* v_k_455_, lean_object* v_acc_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_452_, v_f_453_, v_xs_454_, v_k_455_, v_acc_456_);
lean_dec_ref(v_xs_454_);
lean_dec(v_n_452_);
return v_res_458_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2(void){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_Queue_empty___redArg();
return v___x_462_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(lean_object* v_capacity_463_){
_start:
{
lean_object* v___f_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___f_465_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__0));
v___x_466_ = lean_box(0);
lean_inc(v_capacity_463_);
v___x_467_ = lean_mk_array(v_capacity_463_, v___x_466_);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__1));
v___x_470_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_capacity_463_, v___f_465_, v___x_467_, v___x_468_, v___x_469_);
lean_dec_ref(v___x_467_);
v___x_471_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
v___x_472_ = lean_box(1);
v___x_473_ = 0;
v___x_474_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_474_, 0, v___x_471_);
lean_ctor_set(v___x_474_, 1, v___x_471_);
lean_ctor_set(v___x_474_, 2, v_capacity_463_);
lean_ctor_set(v___x_474_, 3, v___x_468_);
lean_ctor_set(v___x_474_, 4, v___x_470_);
lean_ctor_set(v___x_474_, 5, v___x_468_);
lean_ctor_set(v___x_474_, 6, v___x_468_);
lean_ctor_set(v___x_474_, 7, v___x_472_);
lean_ctor_set(v___x_474_, 8, v___x_468_);
lean_ctor_set(v___x_474_, 9, v___x_468_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*10, v___x_473_);
v___x_475_ = l_Std_Mutex_new___redArg(v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_463_ = stack[0].m_obj;
lean_object* v_res_476_;
v_res_476_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_463_);
stack->m_obj
 = v_res_476_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___boxed(lean_object* v_capacity_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_477_);
return v_res_479_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new(lean_object* v_00_u03b1_480_, lean_object* v_capacity_481_, lean_object* v_h_482_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_481_);
return v___x_484_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_481_ = stack[1].m_obj;
lean_object* v_res_485_;
v_res_485_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new(lean_box(0), v_capacity_481_, lean_box(0));
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_new___boxed(lean_object* v_00_u03b1_486_, lean_object* v_capacity_487_, lean_object* v_h_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new(v_00_u03b1_486_, v_capacity_487_, v_h_488_);
return v_res_490_;
}
}
lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(lean_object* v_00_u03b1_491_, lean_object* v_00_u03b2_492_, lean_object* v_n_493_, lean_object* v_f_494_, lean_object* v_xs_495_, lean_object* v_k_496_, lean_object* v_h_497_, lean_object* v_acc_498_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___redArg(v_n_493_, v_f_494_, v_xs_495_, v_k_496_, v_acc_498_);
return v___x_500_;
}
}
LEAN_EXPORT void l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_493_ = stack[2].m_obj;
lean_object* v_f_494_ = stack[3].m_obj;
lean_object* v_xs_495_ = stack[4].m_obj;
lean_object* v_k_496_ = stack[5].m_obj;
lean_object* v_acc_498_ = stack[7].m_obj;
lean_object* v_res_501_;
v_res_501_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(lean_box(0), lean_box(0), v_n_493_, v_f_494_, v_xs_495_, v_k_496_, lean_box(0), v_acc_498_);
stack->m_obj
 = v_res_501_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0___boxed(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_n_504_, lean_object* v_f_505_, lean_object* v_xs_506_, lean_object* v_k_507_, lean_object* v_h_508_, lean_object* v_acc_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_new_spec__0(v_00_u03b1_502_, v_00_u03b2_503_, v_n_504_, v_f_505_, v_xs_506_, v_k_507_, v_h_508_, v_acc_509_);
lean_dec_ref(v_xs_506_);
lean_dec(v_n_504_);
return v_res_511_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(lean_object* v_mutex_512_, lean_object* v_k_513_){
_start:
{
lean_object* v_ref_515_; lean_object* v_mutex_516_; lean_object* v___x_517_; lean_object* v_r_518_; 
v_ref_515_ = lean_ctor_get(v_mutex_512_, 0);
lean_inc(v_ref_515_);
v_mutex_516_ = lean_ctor_get(v_mutex_512_, 1);
lean_inc(v_mutex_516_);
lean_dec_ref(v_mutex_512_);
v___x_517_ = lean_io_basemutex_lock(v_mutex_516_);
v_r_518_ = lean_apply_2(v_k_513_, v_ref_515_, lean_box(0));
if (lean_obj_tag(v_r_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_527_; 
v_a_519_ = lean_ctor_get(v_r_518_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v_r_518_);
if (v_isSharedCheck_527_ == 0)
{
v___x_521_ = v_r_518_;
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v_r_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_527_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_io_basemutex_unlock(v_mutex_516_);
lean_dec(v_mutex_516_);
if (v_isShared_522_ == 0)
{
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_519_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_536_; 
v_a_528_ = lean_ctor_get(v_r_518_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_r_518_);
if (v_isSharedCheck_536_ == 0)
{
v___x_530_ = v_r_518_;
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v_r_518_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_536_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_534_; 
v___x_532_ = lean_io_basemutex_unlock(v_mutex_516_);
lean_dec(v_mutex_516_);
if (v_isShared_531_ == 0)
{
v___x_534_ = v___x_530_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_528_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_512_ = stack[0].m_obj;
lean_object* v_k_513_ = stack[1].m_obj;
lean_object* v_res_537_;
v_res_537_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_512_, v_k_513_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg___boxed(lean_object* v_mutex_538_, lean_object* v_k_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_538_, v_k_539_);
return v_res_541_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_mutex_544_, lean_object* v_k_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_mutex_544_, v_k_545_);
return v___x_547_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_544_ = stack[2].m_obj;
lean_object* v_k_545_ = stack[3].m_obj;
lean_object* v_res_548_;
v_res_548_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(lean_box(0), lean_box(0), v_mutex_544_, v_k_545_);
stack->m_obj
 = v_res_548_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___boxed(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_, lean_object* v_mutex_551_, lean_object* v_k_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1(v_00_u03b1_549_, v_00_u03b2_550_, v_mutex_551_, v_k_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(lean_object* v_k_555_, lean_object* v_v_556_, lean_object* v_t_557_){
_start:
{
if (lean_obj_tag(v_t_557_) == 0)
{
lean_object* v_size_558_; lean_object* v_k_559_; lean_object* v_v_560_; lean_object* v_l_561_; lean_object* v_r_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_843_; 
v_size_558_ = lean_ctor_get(v_t_557_, 0);
v_k_559_ = lean_ctor_get(v_t_557_, 1);
v_v_560_ = lean_ctor_get(v_t_557_, 2);
v_l_561_ = lean_ctor_get(v_t_557_, 3);
v_r_562_ = lean_ctor_get(v_t_557_, 4);
v_isSharedCheck_843_ = !lean_is_exclusive(v_t_557_);
if (v_isSharedCheck_843_ == 0)
{
v___x_564_ = v_t_557_;
v_isShared_565_ = v_isSharedCheck_843_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_r_562_);
lean_inc(v_l_561_);
lean_inc(v_v_560_);
lean_inc(v_k_559_);
lean_inc(v_size_558_);
lean_dec(v_t_557_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_843_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint8_t v___x_566_; 
v___x_566_ = lean_nat_dec_lt(v_k_555_, v_k_559_);
if (v___x_566_ == 0)
{
uint8_t v___x_567_; 
v___x_567_ = lean_nat_dec_eq(v_k_555_, v_k_559_);
if (v___x_567_ == 0)
{
lean_object* v_impl_568_; lean_object* v___x_569_; 
lean_dec(v_size_558_);
v_impl_568_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_555_, v_v_556_, v_r_562_);
v___x_569_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_561_) == 0)
{
lean_object* v_size_570_; lean_object* v_size_571_; lean_object* v_k_572_; lean_object* v_v_573_; lean_object* v_l_574_; lean_object* v_r_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_size_570_ = lean_ctor_get(v_l_561_, 0);
v_size_571_ = lean_ctor_get(v_impl_568_, 0);
v_k_572_ = lean_ctor_get(v_impl_568_, 1);
v_v_573_ = lean_ctor_get(v_impl_568_, 2);
v_l_574_ = lean_ctor_get(v_impl_568_, 3);
lean_inc(v_l_574_);
v_r_575_ = lean_ctor_get(v_impl_568_, 4);
v___x_576_ = lean_unsigned_to_nat(3u);
v___x_577_ = lean_nat_mul(v___x_576_, v_size_570_);
v___x_578_ = lean_nat_dec_lt(v___x_577_, v_size_571_);
lean_dec(v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec(v_l_574_);
v___x_579_ = lean_nat_add(v___x_569_, v_size_570_);
v___x_580_ = lean_nat_add(v___x_579_, v_size_571_);
lean_dec(v___x_579_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v_impl_568_);
lean_ctor_set(v___x_564_, 0, v___x_580_);
v___x_582_ = v___x_564_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_583_, 3, v_l_561_);
lean_ctor_set(v_reuseFailAlloc_583_, 4, v_impl_568_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
else
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_647_; 
lean_inc(v_r_575_);
lean_inc(v_v_573_);
lean_inc(v_k_572_);
lean_inc(v_size_571_);
v_isSharedCheck_647_ = !lean_is_exclusive(v_impl_568_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; lean_object* v_unused_649_; lean_object* v_unused_650_; lean_object* v_unused_651_; lean_object* v_unused_652_; 
v_unused_648_ = lean_ctor_get(v_impl_568_, 4);
lean_dec(v_unused_648_);
v_unused_649_ = lean_ctor_get(v_impl_568_, 3);
lean_dec(v_unused_649_);
v_unused_650_ = lean_ctor_get(v_impl_568_, 2);
lean_dec(v_unused_650_);
v_unused_651_ = lean_ctor_get(v_impl_568_, 1);
lean_dec(v_unused_651_);
v_unused_652_ = lean_ctor_get(v_impl_568_, 0);
lean_dec(v_unused_652_);
v___x_585_ = v_impl_568_;
v_isShared_586_ = v_isSharedCheck_647_;
goto v_resetjp_584_;
}
else
{
lean_dec(v_impl_568_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_647_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_size_587_; lean_object* v_k_588_; lean_object* v_v_589_; lean_object* v_l_590_; lean_object* v_r_591_; lean_object* v_size_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_size_587_ = lean_ctor_get(v_l_574_, 0);
v_k_588_ = lean_ctor_get(v_l_574_, 1);
v_v_589_ = lean_ctor_get(v_l_574_, 2);
v_l_590_ = lean_ctor_get(v_l_574_, 3);
v_r_591_ = lean_ctor_get(v_l_574_, 4);
v_size_592_ = lean_ctor_get(v_r_575_, 0);
v___x_593_ = lean_unsigned_to_nat(2u);
v___x_594_ = lean_nat_mul(v___x_593_, v_size_592_);
v___x_595_ = lean_nat_dec_lt(v_size_587_, v___x_594_);
lean_dec(v___x_594_);
if (v___x_595_ == 0)
{
lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_623_; 
lean_inc(v_r_591_);
lean_inc(v_l_590_);
lean_inc(v_v_589_);
lean_inc(v_k_588_);
v_isSharedCheck_623_ = !lean_is_exclusive(v_l_574_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; lean_object* v_unused_625_; lean_object* v_unused_626_; lean_object* v_unused_627_; lean_object* v_unused_628_; 
v_unused_624_ = lean_ctor_get(v_l_574_, 4);
lean_dec(v_unused_624_);
v_unused_625_ = lean_ctor_get(v_l_574_, 3);
lean_dec(v_unused_625_);
v_unused_626_ = lean_ctor_get(v_l_574_, 2);
lean_dec(v_unused_626_);
v_unused_627_ = lean_ctor_get(v_l_574_, 1);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v_l_574_, 0);
lean_dec(v_unused_628_);
v___x_597_ = v_l_574_;
v_isShared_598_ = v_isSharedCheck_623_;
goto v_resetjp_596_;
}
else
{
lean_dec(v_l_574_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_623_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_613_; 
v___x_599_ = lean_nat_add(v___x_569_, v_size_570_);
v___x_600_ = lean_nat_add(v___x_599_, v_size_571_);
lean_dec(v_size_571_);
if (lean_obj_tag(v_l_590_) == 0)
{
lean_object* v_size_621_; 
v_size_621_ = lean_ctor_get(v_l_590_, 0);
lean_inc(v_size_621_);
v___y_613_ = v_size_621_;
goto v___jp_612_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = lean_unsigned_to_nat(0u);
v___y_613_ = v___x_622_;
goto v___jp_612_;
}
v___jp_601_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = lean_nat_add(v___y_603_, v___y_604_);
lean_dec(v___y_604_);
lean_dec(v___y_603_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 4, v_r_575_);
lean_ctor_set(v___x_597_, 3, v_r_591_);
lean_ctor_set(v___x_597_, 2, v_v_573_);
lean_ctor_set(v___x_597_, 1, v_k_572_);
lean_ctor_set(v___x_597_, 0, v___x_605_);
v___x_607_ = v___x_597_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_k_572_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_v_573_);
lean_ctor_set(v_reuseFailAlloc_611_, 3, v_r_591_);
lean_ctor_set(v_reuseFailAlloc_611_, 4, v_r_575_);
v___x_607_ = v_reuseFailAlloc_611_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_609_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 4, v___x_607_);
lean_ctor_set(v___x_585_, 3, v___y_602_);
lean_ctor_set(v___x_585_, 2, v_v_589_);
lean_ctor_set(v___x_585_, 1, v_k_588_);
lean_ctor_set(v___x_585_, 0, v___x_600_);
v___x_609_ = v___x_585_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_k_588_);
lean_ctor_set(v_reuseFailAlloc_610_, 2, v_v_589_);
lean_ctor_set(v_reuseFailAlloc_610_, 3, v___y_602_);
lean_ctor_set(v_reuseFailAlloc_610_, 4, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
v___jp_612_:
{
lean_object* v___x_614_; lean_object* v___x_616_; 
v___x_614_ = lean_nat_add(v___x_599_, v___y_613_);
lean_dec(v___y_613_);
lean_dec(v___x_599_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v_l_590_);
lean_ctor_set(v___x_564_, 0, v___x_614_);
v___x_616_ = v___x_564_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_l_561_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_l_590_);
v___x_616_ = v_reuseFailAlloc_620_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; 
v___x_617_ = lean_nat_add(v___x_569_, v_size_592_);
if (lean_obj_tag(v_r_591_) == 0)
{
lean_object* v_size_618_; 
v_size_618_ = lean_ctor_get(v_r_591_, 0);
lean_inc(v_size_618_);
v___y_602_ = v___x_616_;
v___y_603_ = v___x_617_;
v___y_604_ = v_size_618_;
goto v___jp_601_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___y_602_ = v___x_616_;
v___y_603_ = v___x_617_;
v___y_604_ = v___x_619_;
goto v___jp_601_;
}
}
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
lean_del_object(v___x_564_);
v___x_629_ = lean_nat_add(v___x_569_, v_size_570_);
v___x_630_ = lean_nat_add(v___x_629_, v_size_571_);
lean_dec(v_size_571_);
v___x_631_ = lean_nat_add(v___x_629_, v_size_587_);
lean_dec(v___x_629_);
lean_inc_ref(v_l_561_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 4, v_l_574_);
lean_ctor_set(v___x_585_, 3, v_l_561_);
lean_ctor_set(v___x_585_, 2, v_v_560_);
lean_ctor_set(v___x_585_, 1, v_k_559_);
lean_ctor_set(v___x_585_, 0, v___x_631_);
v___x_633_ = v___x_585_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_646_, 3, v_l_561_);
lean_ctor_set(v_reuseFailAlloc_646_, 4, v_l_574_);
v___x_633_ = v_reuseFailAlloc_646_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_isSharedCheck_640_ = !lean_is_exclusive(v_l_561_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; lean_object* v_unused_642_; lean_object* v_unused_643_; lean_object* v_unused_644_; lean_object* v_unused_645_; 
v_unused_641_ = lean_ctor_get(v_l_561_, 4);
lean_dec(v_unused_641_);
v_unused_642_ = lean_ctor_get(v_l_561_, 3);
lean_dec(v_unused_642_);
v_unused_643_ = lean_ctor_get(v_l_561_, 2);
lean_dec(v_unused_643_);
v_unused_644_ = lean_ctor_get(v_l_561_, 1);
lean_dec(v_unused_644_);
v_unused_645_ = lean_ctor_get(v_l_561_, 0);
lean_dec(v_unused_645_);
v___x_635_ = v_l_561_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_dec(v_l_561_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 4, v_r_575_);
lean_ctor_set(v___x_635_, 3, v___x_633_);
lean_ctor_set(v___x_635_, 2, v_v_573_);
lean_ctor_set(v___x_635_, 1, v_k_572_);
lean_ctor_set(v___x_635_, 0, v___x_630_);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_630_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v_k_572_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_v_573_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_639_, 4, v_r_575_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_653_; 
v_l_653_ = lean_ctor_get(v_impl_568_, 3);
lean_inc(v_l_653_);
if (lean_obj_tag(v_l_653_) == 0)
{
lean_object* v_r_654_; lean_object* v_k_655_; lean_object* v_v_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_679_; 
v_r_654_ = lean_ctor_get(v_impl_568_, 4);
v_k_655_ = lean_ctor_get(v_impl_568_, 1);
v_v_656_ = lean_ctor_get(v_impl_568_, 2);
v_isSharedCheck_679_ = !lean_is_exclusive(v_impl_568_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; lean_object* v_unused_681_; 
v_unused_680_ = lean_ctor_get(v_impl_568_, 3);
lean_dec(v_unused_680_);
v_unused_681_ = lean_ctor_get(v_impl_568_, 0);
lean_dec(v_unused_681_);
v___x_658_ = v_impl_568_;
v_isShared_659_ = v_isSharedCheck_679_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_r_654_);
lean_inc(v_v_656_);
lean_inc(v_k_655_);
lean_dec(v_impl_568_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_679_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_k_660_; lean_object* v_v_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_675_; 
v_k_660_ = lean_ctor_get(v_l_653_, 1);
v_v_661_ = lean_ctor_get(v_l_653_, 2);
v_isSharedCheck_675_ = !lean_is_exclusive(v_l_653_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; lean_object* v_unused_677_; lean_object* v_unused_678_; 
v_unused_676_ = lean_ctor_get(v_l_653_, 4);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v_l_653_, 3);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v_l_653_, 0);
lean_dec(v_unused_678_);
v___x_663_ = v_l_653_;
v_isShared_664_ = v_isSharedCheck_675_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_v_661_);
lean_inc(v_k_660_);
lean_dec(v_l_653_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_675_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_665_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_654_, 2);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 4, v_r_654_);
lean_ctor_set(v___x_663_, 3, v_r_654_);
lean_ctor_set(v___x_663_, 2, v_v_560_);
lean_ctor_set(v___x_663_, 1, v_k_559_);
lean_ctor_set(v___x_663_, 0, v___x_569_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_r_654_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_r_654_);
v___x_667_ = v_reuseFailAlloc_674_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
lean_inc(v_r_654_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 3, v_r_654_);
lean_ctor_set(v___x_658_, 0, v___x_569_);
v___x_669_ = v___x_658_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_673_, 1, v_k_655_);
lean_ctor_set(v_reuseFailAlloc_673_, 2, v_v_656_);
lean_ctor_set(v_reuseFailAlloc_673_, 3, v_r_654_);
lean_ctor_set(v_reuseFailAlloc_673_, 4, v_r_654_);
v___x_669_ = v_reuseFailAlloc_673_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_671_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v___x_669_);
lean_ctor_set(v___x_564_, 3, v___x_667_);
lean_ctor_set(v___x_564_, 2, v_v_661_);
lean_ctor_set(v___x_564_, 1, v_k_660_);
lean_ctor_set(v___x_564_, 0, v___x_665_);
v___x_671_ = v___x_564_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_k_660_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_v_661_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v___x_667_);
lean_ctor_set(v_reuseFailAlloc_672_, 4, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
else
{
lean_object* v_r_682_; 
v_r_682_ = lean_ctor_get(v_impl_568_, 4);
lean_inc(v_r_682_);
if (lean_obj_tag(v_r_682_) == 0)
{
lean_object* v_k_683_; lean_object* v_v_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_695_; 
v_k_683_ = lean_ctor_get(v_impl_568_, 1);
v_v_684_ = lean_ctor_get(v_impl_568_, 2);
v_isSharedCheck_695_ = !lean_is_exclusive(v_impl_568_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; lean_object* v_unused_697_; lean_object* v_unused_698_; 
v_unused_696_ = lean_ctor_get(v_impl_568_, 4);
lean_dec(v_unused_696_);
v_unused_697_ = lean_ctor_get(v_impl_568_, 3);
lean_dec(v_unused_697_);
v_unused_698_ = lean_ctor_get(v_impl_568_, 0);
lean_dec(v_unused_698_);
v___x_686_ = v_impl_568_;
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_v_684_);
lean_inc(v_k_683_);
lean_dec(v_impl_568_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = lean_unsigned_to_nat(3u);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 4, v_l_653_);
lean_ctor_set(v___x_686_, 2, v_v_560_);
lean_ctor_set(v___x_686_, 1, v_k_559_);
lean_ctor_set(v___x_686_, 0, v___x_569_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_569_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_694_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_694_, 3, v_l_653_);
lean_ctor_set(v_reuseFailAlloc_694_, 4, v_l_653_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v_r_682_);
lean_ctor_set(v___x_564_, 3, v___x_690_);
lean_ctor_set(v___x_564_, 2, v_v_684_);
lean_ctor_set(v___x_564_, 1, v_k_683_);
lean_ctor_set(v___x_564_, 0, v___x_688_);
v___x_692_ = v___x_564_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_k_683_);
lean_ctor_set(v_reuseFailAlloc_693_, 2, v_v_684_);
lean_ctor_set(v_reuseFailAlloc_693_, 3, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_693_, 4, v_r_682_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = lean_unsigned_to_nat(2u);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v_impl_568_);
lean_ctor_set(v___x_564_, 3, v_r_682_);
lean_ctor_set(v___x_564_, 0, v___x_699_);
v___x_701_ = v___x_564_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_r_682_);
lean_ctor_set(v_reuseFailAlloc_702_, 4, v_impl_568_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
else
{
lean_object* v___x_704_; 
lean_dec(v_v_560_);
lean_dec(v_k_559_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 2, v_v_556_);
lean_ctor_set(v___x_564_, 1, v_k_555_);
v___x_704_ = v___x_564_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_size_558_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_k_555_);
lean_ctor_set(v_reuseFailAlloc_705_, 2, v_v_556_);
lean_ctor_set(v_reuseFailAlloc_705_, 3, v_l_561_);
lean_ctor_set(v_reuseFailAlloc_705_, 4, v_r_562_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_object* v_impl_706_; lean_object* v___x_707_; 
lean_dec(v_size_558_);
v_impl_706_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_555_, v_v_556_, v_l_561_);
v___x_707_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_562_) == 0)
{
lean_object* v_size_708_; lean_object* v_size_709_; lean_object* v_k_710_; lean_object* v_v_711_; lean_object* v_l_712_; lean_object* v_r_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; 
v_size_708_ = lean_ctor_get(v_r_562_, 0);
v_size_709_ = lean_ctor_get(v_impl_706_, 0);
v_k_710_ = lean_ctor_get(v_impl_706_, 1);
v_v_711_ = lean_ctor_get(v_impl_706_, 2);
v_l_712_ = lean_ctor_get(v_impl_706_, 3);
v_r_713_ = lean_ctor_get(v_impl_706_, 4);
lean_inc(v_r_713_);
v___x_714_ = lean_unsigned_to_nat(3u);
v___x_715_ = lean_nat_mul(v___x_714_, v_size_708_);
v___x_716_ = lean_nat_dec_lt(v___x_715_, v_size_709_);
lean_dec(v___x_715_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
lean_dec(v_r_713_);
v___x_717_ = lean_nat_add(v___x_707_, v_size_709_);
v___x_718_ = lean_nat_add(v___x_717_, v_size_708_);
lean_dec(v___x_717_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 3, v_impl_706_);
lean_ctor_set(v___x_564_, 0, v___x_718_);
v___x_720_ = v___x_564_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_impl_706_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_r_562_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
else
{
lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_787_; 
lean_inc(v_l_712_);
lean_inc(v_v_711_);
lean_inc(v_k_710_);
lean_inc(v_size_709_);
v_isSharedCheck_787_ = !lean_is_exclusive(v_impl_706_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; lean_object* v_unused_789_; lean_object* v_unused_790_; lean_object* v_unused_791_; lean_object* v_unused_792_; 
v_unused_788_ = lean_ctor_get(v_impl_706_, 4);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_impl_706_, 3);
lean_dec(v_unused_789_);
v_unused_790_ = lean_ctor_get(v_impl_706_, 2);
lean_dec(v_unused_790_);
v_unused_791_ = lean_ctor_get(v_impl_706_, 1);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_impl_706_, 0);
lean_dec(v_unused_792_);
v___x_723_ = v_impl_706_;
v_isShared_724_ = v_isSharedCheck_787_;
goto v_resetjp_722_;
}
else
{
lean_dec(v_impl_706_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_787_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_size_725_; lean_object* v_size_726_; lean_object* v_k_727_; lean_object* v_v_728_; lean_object* v_l_729_; lean_object* v_r_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_size_725_ = lean_ctor_get(v_l_712_, 0);
v_size_726_ = lean_ctor_get(v_r_713_, 0);
v_k_727_ = lean_ctor_get(v_r_713_, 1);
v_v_728_ = lean_ctor_get(v_r_713_, 2);
v_l_729_ = lean_ctor_get(v_r_713_, 3);
v_r_730_ = lean_ctor_get(v_r_713_, 4);
v___x_731_ = lean_unsigned_to_nat(2u);
v___x_732_ = lean_nat_mul(v___x_731_, v_size_725_);
v___x_733_ = lean_nat_dec_lt(v_size_726_, v___x_732_);
lean_dec(v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_762_; 
lean_inc(v_r_730_);
lean_inc(v_l_729_);
lean_inc(v_v_728_);
lean_inc(v_k_727_);
v_isSharedCheck_762_ = !lean_is_exclusive(v_r_713_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; lean_object* v_unused_764_; lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; 
v_unused_763_ = lean_ctor_get(v_r_713_, 4);
lean_dec(v_unused_763_);
v_unused_764_ = lean_ctor_get(v_r_713_, 3);
lean_dec(v_unused_764_);
v_unused_765_ = lean_ctor_get(v_r_713_, 2);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_r_713_, 1);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_r_713_, 0);
lean_dec(v_unused_767_);
v___x_735_ = v_r_713_;
v_isShared_736_ = v_isSharedCheck_762_;
goto v_resetjp_734_;
}
else
{
lean_dec(v_r_713_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_762_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___y_740_; lean_object* v___y_741_; lean_object* v___y_742_; lean_object* v___x_750_; lean_object* v___y_752_; 
v___x_737_ = lean_nat_add(v___x_707_, v_size_709_);
lean_dec(v_size_709_);
v___x_738_ = lean_nat_add(v___x_737_, v_size_708_);
lean_dec(v___x_737_);
v___x_750_ = lean_nat_add(v___x_707_, v_size_725_);
if (lean_obj_tag(v_l_729_) == 0)
{
lean_object* v_size_760_; 
v_size_760_ = lean_ctor_get(v_l_729_, 0);
lean_inc(v_size_760_);
v___y_752_ = v_size_760_;
goto v___jp_751_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = lean_unsigned_to_nat(0u);
v___y_752_ = v___x_761_;
goto v___jp_751_;
}
v___jp_739_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_nat_add(v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec(v___y_741_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 4, v_r_562_);
lean_ctor_set(v___x_735_, 3, v_r_730_);
lean_ctor_set(v___x_735_, 2, v_v_560_);
lean_ctor_set(v___x_735_, 1, v_k_559_);
lean_ctor_set(v___x_735_, 0, v___x_743_);
v___x_745_ = v___x_735_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_749_, 3, v_r_730_);
lean_ctor_set(v_reuseFailAlloc_749_, 4, v_r_562_);
v___x_745_ = v_reuseFailAlloc_749_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_747_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 4, v___x_745_);
lean_ctor_set(v___x_723_, 3, v___y_740_);
lean_ctor_set(v___x_723_, 2, v_v_728_);
lean_ctor_set(v___x_723_, 1, v_k_727_);
lean_ctor_set(v___x_723_, 0, v___x_738_);
v___x_747_ = v___x_723_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_738_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_k_727_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_v_728_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v___y_740_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
v___jp_751_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_753_ = lean_nat_add(v___x_750_, v___y_752_);
lean_dec(v___y_752_);
lean_dec(v___x_750_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v_l_729_);
lean_ctor_set(v___x_564_, 3, v_l_712_);
lean_ctor_set(v___x_564_, 2, v_v_711_);
lean_ctor_set(v___x_564_, 1, v_k_710_);
lean_ctor_set(v___x_564_, 0, v___x_753_);
v___x_755_ = v___x_564_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_k_710_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v_v_711_);
lean_ctor_set(v_reuseFailAlloc_759_, 3, v_l_712_);
lean_ctor_set(v_reuseFailAlloc_759_, 4, v_l_729_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_756_; 
v___x_756_ = lean_nat_add(v___x_707_, v_size_708_);
if (lean_obj_tag(v_r_730_) == 0)
{
lean_object* v_size_757_; 
v_size_757_ = lean_ctor_get(v_r_730_, 0);
lean_inc(v_size_757_);
v___y_740_ = v___x_755_;
v___y_741_ = v___x_756_;
v___y_742_ = v_size_757_;
goto v___jp_739_;
}
else
{
lean_object* v___x_758_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___y_740_ = v___x_755_;
v___y_741_ = v___x_756_;
v___y_742_ = v___x_758_;
goto v___jp_739_;
}
}
}
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_del_object(v___x_564_);
v___x_768_ = lean_nat_add(v___x_707_, v_size_709_);
lean_dec(v_size_709_);
v___x_769_ = lean_nat_add(v___x_768_, v_size_708_);
lean_dec(v___x_768_);
v___x_770_ = lean_nat_add(v___x_707_, v_size_708_);
v___x_771_ = lean_nat_add(v___x_770_, v_size_726_);
lean_dec(v___x_770_);
lean_inc_ref(v_r_562_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 4, v_r_562_);
lean_ctor_set(v___x_723_, 3, v_r_713_);
lean_ctor_set(v___x_723_, 2, v_v_560_);
lean_ctor_set(v___x_723_, 1, v_k_559_);
lean_ctor_set(v___x_723_, 0, v___x_771_);
v___x_773_ = v___x_723_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_786_, 3, v_r_713_);
lean_ctor_set(v_reuseFailAlloc_786_, 4, v_r_562_);
v___x_773_ = v_reuseFailAlloc_786_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
v_isSharedCheck_780_ = !lean_is_exclusive(v_r_562_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; lean_object* v_unused_785_; 
v_unused_781_ = lean_ctor_get(v_r_562_, 4);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_r_562_, 3);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_r_562_, 2);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_r_562_, 1);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_r_562_, 0);
lean_dec(v_unused_785_);
v___x_775_ = v_r_562_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_dec(v_r_562_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 4, v___x_773_);
lean_ctor_set(v___x_775_, 3, v_l_712_);
lean_ctor_set(v___x_775_, 2, v_v_711_);
lean_ctor_set(v___x_775_, 1, v_k_710_);
lean_ctor_set(v___x_775_, 0, v___x_769_);
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_k_710_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_v_711_);
lean_ctor_set(v_reuseFailAlloc_779_, 3, v_l_712_);
lean_ctor_set(v_reuseFailAlloc_779_, 4, v___x_773_);
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
}
}
}
else
{
lean_object* v_l_793_; 
v_l_793_ = lean_ctor_get(v_impl_706_, 3);
if (lean_obj_tag(v_l_793_) == 0)
{
lean_object* v_r_794_; lean_object* v_k_795_; lean_object* v_v_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_807_; 
lean_inc_ref(v_l_793_);
v_r_794_ = lean_ctor_get(v_impl_706_, 4);
v_k_795_ = lean_ctor_get(v_impl_706_, 1);
v_v_796_ = lean_ctor_get(v_impl_706_, 2);
v_isSharedCheck_807_ = !lean_is_exclusive(v_impl_706_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; lean_object* v_unused_809_; 
v_unused_808_ = lean_ctor_get(v_impl_706_, 3);
lean_dec(v_unused_808_);
v_unused_809_ = lean_ctor_get(v_impl_706_, 0);
lean_dec(v_unused_809_);
v___x_798_ = v_impl_706_;
v_isShared_799_ = v_isSharedCheck_807_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_r_794_);
lean_inc(v_v_796_);
lean_inc(v_k_795_);
lean_dec(v_impl_706_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_807_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_794_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 3, v_r_794_);
lean_ctor_set(v___x_798_, 2, v_v_560_);
lean_ctor_set(v___x_798_, 1, v_k_559_);
lean_ctor_set(v___x_798_, 0, v___x_707_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v_r_794_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v_r_794_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v___x_802_);
lean_ctor_set(v___x_564_, 3, v_l_793_);
lean_ctor_set(v___x_564_, 2, v_v_796_);
lean_ctor_set(v___x_564_, 1, v_k_795_);
lean_ctor_set(v___x_564_, 0, v___x_800_);
v___x_804_ = v___x_564_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_k_795_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_v_796_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_l_793_);
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
else
{
lean_object* v_r_810_; 
v_r_810_ = lean_ctor_get(v_impl_706_, 4);
lean_inc(v_r_810_);
if (lean_obj_tag(v_r_810_) == 0)
{
lean_object* v_k_811_; lean_object* v_v_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_835_; 
lean_inc(v_l_793_);
v_k_811_ = lean_ctor_get(v_impl_706_, 1);
v_v_812_ = lean_ctor_get(v_impl_706_, 2);
v_isSharedCheck_835_ = !lean_is_exclusive(v_impl_706_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; lean_object* v_unused_837_; lean_object* v_unused_838_; 
v_unused_836_ = lean_ctor_get(v_impl_706_, 4);
lean_dec(v_unused_836_);
v_unused_837_ = lean_ctor_get(v_impl_706_, 3);
lean_dec(v_unused_837_);
v_unused_838_ = lean_ctor_get(v_impl_706_, 0);
lean_dec(v_unused_838_);
v___x_814_ = v_impl_706_;
v_isShared_815_ = v_isSharedCheck_835_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_v_812_);
lean_inc(v_k_811_);
lean_dec(v_impl_706_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_835_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_k_816_; lean_object* v_v_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_831_; 
v_k_816_ = lean_ctor_get(v_r_810_, 1);
v_v_817_ = lean_ctor_get(v_r_810_, 2);
v_isSharedCheck_831_ = !lean_is_exclusive(v_r_810_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; 
v_unused_832_ = lean_ctor_get(v_r_810_, 4);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_r_810_, 3);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_r_810_, 0);
lean_dec(v_unused_834_);
v___x_819_ = v_r_810_;
v_isShared_820_ = v_isSharedCheck_831_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_v_817_);
lean_inc(v_k_816_);
lean_dec(v_r_810_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_831_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_821_ = lean_unsigned_to_nat(3u);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 4, v_l_793_);
lean_ctor_set(v___x_819_, 3, v_l_793_);
lean_ctor_set(v___x_819_, 2, v_v_812_);
lean_ctor_set(v___x_819_, 1, v_k_811_);
lean_ctor_set(v___x_819_, 0, v___x_707_);
v___x_823_ = v___x_819_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_k_811_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_v_812_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v_l_793_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v_l_793_);
v___x_823_ = v_reuseFailAlloc_830_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_825_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 4, v_l_793_);
lean_ctor_set(v___x_814_, 2, v_v_560_);
lean_ctor_set(v___x_814_, 1, v_k_559_);
lean_ctor_set(v___x_814_, 0, v___x_707_);
v___x_825_ = v___x_814_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v_l_793_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v_l_793_);
v___x_825_ = v_reuseFailAlloc_829_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_827_; 
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v___x_825_);
lean_ctor_set(v___x_564_, 3, v___x_823_);
lean_ctor_set(v___x_564_, 2, v_v_817_);
lean_ctor_set(v___x_564_, 1, v_k_816_);
lean_ctor_set(v___x_564_, 0, v___x_821_);
v___x_827_ = v___x_564_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_816_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_817_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_839_ = lean_unsigned_to_nat(2u);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 4, v_r_810_);
lean_ctor_set(v___x_564_, 3, v_impl_706_);
lean_ctor_set(v___x_564_, 0, v___x_839_);
v___x_841_ = v___x_564_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_k_559_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v_v_560_);
lean_ctor_set(v_reuseFailAlloc_842_, 3, v_impl_706_);
lean_ctor_set(v_reuseFailAlloc_842_, 4, v_r_810_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_unsigned_to_nat(1u);
v___x_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v_k_555_);
lean_ctor_set(v___x_845_, 2, v_v_556_);
lean_ctor_set(v___x_845_, 3, v_t_557_);
lean_ctor_set(v___x_845_, 4, v_t_557_);
return v___x_845_;
}
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(lean_object* v___y_846_){
_start:
{
lean_object* v___x_848_; lean_object* v_producers_849_; lean_object* v_waiters_850_; lean_object* v_capacity_851_; lean_object* v_size_852_; lean_object* v_buffer_853_; lean_object* v_write_854_; lean_object* v_read_855_; lean_object* v_receivers_856_; lean_object* v_nextId_857_; uint8_t v_closed_858_; lean_object* v_pos_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_871_; 
v___x_848_ = lean_st_ref_take(v___y_846_);
v_producers_849_ = lean_ctor_get(v___x_848_, 0);
v_waiters_850_ = lean_ctor_get(v___x_848_, 1);
v_capacity_851_ = lean_ctor_get(v___x_848_, 2);
v_size_852_ = lean_ctor_get(v___x_848_, 3);
v_buffer_853_ = lean_ctor_get(v___x_848_, 4);
v_write_854_ = lean_ctor_get(v___x_848_, 5);
v_read_855_ = lean_ctor_get(v___x_848_, 6);
v_receivers_856_ = lean_ctor_get(v___x_848_, 7);
v_nextId_857_ = lean_ctor_get(v___x_848_, 8);
v_closed_858_ = lean_ctor_get_uint8(v___x_848_, sizeof(void*)*10);
v_pos_859_ = lean_ctor_get(v___x_848_, 9);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_871_ == 0)
{
v___x_861_ = v___x_848_;
v_isShared_862_ = v_isSharedCheck_871_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_pos_859_);
lean_inc(v_nextId_857_);
lean_inc(v_receivers_856_);
lean_inc(v_read_855_);
lean_inc(v_write_854_);
lean_inc(v_buffer_853_);
lean_inc(v_size_852_);
lean_inc(v_capacity_851_);
lean_inc(v_waiters_850_);
lean_inc(v_producers_849_);
lean_dec(v___x_848_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_871_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_867_; 
lean_inc(v_pos_859_);
lean_inc(v_nextId_857_);
v___x_863_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_nextId_857_, v_pos_859_, v_receivers_856_);
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = lean_nat_add(v_nextId_857_, v___x_864_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 8, v___x_865_);
lean_ctor_set(v___x_861_, 7, v___x_863_);
v___x_867_ = v___x_861_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_producers_849_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_waiters_850_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_capacity_851_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_size_852_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_buffer_853_);
lean_ctor_set(v_reuseFailAlloc_870_, 5, v_write_854_);
lean_ctor_set(v_reuseFailAlloc_870_, 6, v_read_855_);
lean_ctor_set(v_reuseFailAlloc_870_, 7, v___x_863_);
lean_ctor_set(v_reuseFailAlloc_870_, 8, v___x_865_);
lean_ctor_set(v_reuseFailAlloc_870_, 9, v_pos_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_870_, sizeof(void*)*10, v_closed_858_);
v___x_867_ = v_reuseFailAlloc_870_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = lean_st_ref_put(v___y_846_, v___x_867_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v_nextId_857_);
return v___x_869_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_846_ = stack[0].m_obj;
lean_object* v_res_872_;
v_res_872_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(v___y_846_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0___boxed(lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___lam__0(v___y_873_);
lean_dec(v___y_873_);
return v_res_875_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(lean_object* v_bd_877_){
_start:
{
lean_object* v___f_879_; lean_object* v___x_880_; 
v___f_879_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___closed__0));
lean_inc_ref(v_bd_877_);
v___x_880_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_bd_877_, v___f_879_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_889_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_889_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_889_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v_bd_877_);
lean_ctor_set(v___x_885_, 1, v_a_881_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_bd_877_);
v_a_890_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_880_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_880_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bd_877_ = stack[0].m_obj;
lean_object* v_res_898_;
v_res_898_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_877_);
stack->m_obj
 = v_res_898_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg___boxed(lean_object* v_bd_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_899_);
return v_res_901_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(lean_object* v_00_u03b1_902_, lean_object* v_bd_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_bd_903_);
return v___x_905_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_0interp(lean_interpreter_value* stack)
{
lean_object* v_bd_903_ = stack[1].m_obj;
lean_object* v_res_906_;
v_res_906_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(lean_box(0), v_bd_903_);
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___boxed(lean_object* v_00_u03b1_907_, lean_object* v_bd_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe(v_00_u03b1_907_, v_bd_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0(lean_object* v_00_u03b2_911_, lean_object* v_k_912_, lean_object* v_v_913_, lean_object* v_t_914_, lean_object* v_hl_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__0___redArg(v_k_912_, v_v_913_, v_t_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(lean_object* v_toApplicative_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_size_919_; lean_object* v_toPure_920_; lean_object* v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_size_919_ = lean_ctor_get(v_a_918_, 3);
v_toPure_920_ = lean_ctor_get(v_toApplicative_917_, 1);
lean_inc(v_toPure_920_);
lean_dec_ref(v_toApplicative_917_);
v___x_921_ = lean_unsigned_to_nat(0u);
v___x_922_ = lean_nat_dec_eq(v_size_919_, v___x_921_);
v___x_923_ = lean_box(v___x_922_);
v___x_924_ = lean_apply_2(v_toPure_920_, lean_box(0), v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed(lean_object* v_toApplicative_925_, lean_object* v_a_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0(v_toApplicative_925_, v_a_926_);
lean_dec_ref(v_a_926_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(lean_object* v_inst_928_, lean_object* v_inst_929_, lean_object* v_a_930_){
_start:
{
lean_object* v_toApplicative_931_; lean_object* v_toBind_932_; lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_toApplicative_931_ = lean_ctor_get(v_inst_928_, 0);
lean_inc_ref(v_toApplicative_931_);
v_toBind_932_ = lean_ctor_get(v_inst_928_, 1);
lean_inc(v_toBind_932_);
lean_dec_ref(v_inst_928_);
v___f_933_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_933_, 0, v_toApplicative_931_);
lean_inc(v_a_930_);
v___x_934_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_934_, 0, lean_box(0));
lean_closure_set(v___x_934_, 1, lean_box(0));
lean_closure_set(v___x_934_, 2, v_a_930_);
v___x_935_ = lean_apply_2(v_inst_929_, lean_box(0), v___x_934_);
v___x_936_ = lean_apply_4(v_toBind_932_, lean_box(0), lean_box(0), v___x_935_, v___f_933_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg___boxed(lean_object* v_inst_937_, lean_object* v_inst_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_937_, v_inst_938_, v_a_939_);
lean_dec(v_a_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(lean_object* v_m_941_, lean_object* v_00_u03b1_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_a_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_943_, v_inst_944_, v_a_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___boxed(lean_object* v_m_947_, lean_object* v_00_u03b1_948_, lean_object* v_inst_949_, lean_object* v_inst_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty(v_m_947_, v_00_u03b1_948_, v_inst_949_, v_inst_950_, v_a_951_);
lean_dec(v_a_951_);
return v_res_952_;
}
}
uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; lean_object* v_capacity_956_; lean_object* v_size_957_; uint8_t v___x_958_; 
v___x_955_ = lean_st_ref_get(v_a_953_);
v_capacity_956_ = lean_ctor_get(v___x_955_, 2);
lean_inc(v_capacity_956_);
v_size_957_ = lean_ctor_get(v___x_955_, 3);
lean_inc(v_size_957_);
lean_dec(v___x_955_);
v___x_958_ = lean_nat_dec_le(v_capacity_956_, v_size_957_);
lean_dec(v_size_957_);
lean_dec(v_capacity_956_);
return v___x_958_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_953_ = stack[0].m_obj;
uint8_t v_res_959_;
v_res_959_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_953_);
stack->m_num = v_res_959_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg___boxed(lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_960_);
lean_dec(v_a_960_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(lean_object* v_00_u03b1_964_, lean_object* v_a_965_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_965_);
return v___x_967_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_965_ = stack[1].m_obj;
uint8_t v_res_968_;
v_res_968_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(lean_box(0), v_a_965_);
stack->m_num = v_res_968_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___boxed(lean_object* v_00_u03b1_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
uint8_t v_res_972_; lean_object* v_r_973_; 
v_res_972_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull(v_00_u03b1_969_, v_a_970_);
lean_dec(v_a_970_);
v_r_973_ = lean_box(v_res_972_);
return v_r_973_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(lean_object* v_value_974_, lean_object* v_st_975_){
_start:
{
lean_object* v_producers_977_; lean_object* v_waiters_978_; lean_object* v_capacity_979_; lean_object* v_size_980_; lean_object* v_buffer_981_; lean_object* v_write_982_; lean_object* v_read_983_; lean_object* v_receivers_984_; lean_object* v_nextId_985_; uint8_t v_closed_986_; lean_object* v_pos_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_1007_; 
v_producers_977_ = lean_ctor_get(v_st_975_, 0);
v_waiters_978_ = lean_ctor_get(v_st_975_, 1);
v_capacity_979_ = lean_ctor_get(v_st_975_, 2);
v_size_980_ = lean_ctor_get(v_st_975_, 3);
v_buffer_981_ = lean_ctor_get(v_st_975_, 4);
v_write_982_ = lean_ctor_get(v_st_975_, 5);
v_read_983_ = lean_ctor_get(v_st_975_, 6);
v_receivers_984_ = lean_ctor_get(v_st_975_, 7);
v_nextId_985_ = lean_ctor_get(v_st_975_, 8);
v_closed_986_ = lean_ctor_get_uint8(v_st_975_, sizeof(void*)*10);
v_pos_987_ = lean_ctor_get(v_st_975_, 9);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_st_975_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_989_ = v_st_975_;
v_isShared_990_ = v_isSharedCheck_1007_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_pos_987_);
lean_inc(v_nextId_985_);
lean_inc(v_receivers_984_);
lean_inc(v_read_983_);
lean_inc(v_write_982_);
lean_inc(v_buffer_981_);
lean_inc(v_size_980_);
lean_inc(v_capacity_979_);
lean_inc(v_waiters_978_);
lean_inc(v_producers_977_);
lean_dec(v_st_975_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_1007_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v_tailRef_991_; lean_object* v___x_992_; lean_object* v___y_994_; 
v_tailRef_991_ = lean_array_fget_borrowed(v_buffer_981_, v_write_982_);
v___x_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_992_, 0, v_value_974_);
if (lean_obj_tag(v_receivers_984_) == 0)
{
lean_object* v_size_1005_; 
v_size_1005_ = lean_ctor_get(v_receivers_984_, 0);
lean_inc(v_size_1005_);
v___y_994_ = v_size_1005_;
goto v___jp_993_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = lean_unsigned_to_nat(0u);
v___y_994_ = v___x_1006_;
goto v___jp_993_;
}
v___jp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1003_; 
lean_inc(v_pos_987_);
v___x_995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_995_, 0, v___x_992_);
lean_ctor_set(v___x_995_, 1, v_pos_987_);
lean_ctor_set(v___x_995_, 2, v___y_994_);
v___x_996_ = lean_st_ref_swap(v_tailRef_991_, v___x_995_);
lean_dec(v___x_996_);
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_write_982_, v___x_997_);
lean_dec(v_write_982_);
v___x_999_ = lean_nat_mod(v___x_998_, v_capacity_979_);
lean_dec(v___x_998_);
v___x_1000_ = lean_nat_add(v_size_980_, v___x_997_);
lean_dec(v_size_980_);
v___x_1001_ = lean_nat_add(v_pos_987_, v___x_997_);
lean_dec(v_pos_987_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 9, v___x_1001_);
lean_ctor_set(v___x_989_, 5, v___x_999_);
lean_ctor_set(v___x_989_, 3, v___x_1000_);
v___x_1003_ = v___x_989_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_producers_977_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_waiters_978_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_capacity_979_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_buffer_981_);
lean_ctor_set(v_reuseFailAlloc_1004_, 5, v___x_999_);
lean_ctor_set(v_reuseFailAlloc_1004_, 6, v_read_983_);
lean_ctor_set(v_reuseFailAlloc_1004_, 7, v_receivers_984_);
lean_ctor_set(v_reuseFailAlloc_1004_, 8, v_nextId_985_);
lean_ctor_set(v_reuseFailAlloc_1004_, 9, v___x_1001_);
lean_ctor_set_uint8(v_reuseFailAlloc_1004_, sizeof(void*)*10, v_closed_986_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_974_ = stack[0].m_obj;
lean_object* v_st_975_ = stack[1].m_obj;
lean_object* v_res_1008_;
v_res_1008_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_974_, v_st_975_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg___boxed(lean_object* v_value_1009_, lean_object* v_st_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_1009_, v_st_1010_);
return v_res_1012_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(lean_object* v_00_u03b1_1013_, lean_object* v_value_1014_, lean_object* v_st_1015_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_value_1014_, v_st_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue_0interp(lean_interpreter_value* stack)
{
lean_object* v_value_1014_ = stack[1].m_obj;
lean_object* v_st_1015_ = stack[2].m_obj;
lean_object* v_res_1018_;
v_res_1018_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(lean_box(0), v_value_1014_, v_st_1015_);
stack->m_obj
 = v_res_1018_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___boxed(lean_object* v_00_u03b1_1019_, lean_object* v_value_1020_, lean_object* v_st_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue(v_00_u03b1_1019_, v_value_1020_, v_st_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(lean_object* v_st_1024_){
_start:
{
lean_object* v_producers_1025_; lean_object* v_waiters_1026_; lean_object* v_capacity_1027_; lean_object* v_size_1028_; lean_object* v_buffer_1029_; lean_object* v_write_1030_; lean_object* v_read_1031_; lean_object* v_receivers_1032_; lean_object* v_nextId_1033_; uint8_t v_closed_1034_; lean_object* v_pos_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1046_; 
v_producers_1025_ = lean_ctor_get(v_st_1024_, 0);
v_waiters_1026_ = lean_ctor_get(v_st_1024_, 1);
v_capacity_1027_ = lean_ctor_get(v_st_1024_, 2);
v_size_1028_ = lean_ctor_get(v_st_1024_, 3);
v_buffer_1029_ = lean_ctor_get(v_st_1024_, 4);
v_write_1030_ = lean_ctor_get(v_st_1024_, 5);
v_read_1031_ = lean_ctor_get(v_st_1024_, 6);
v_receivers_1032_ = lean_ctor_get(v_st_1024_, 7);
v_nextId_1033_ = lean_ctor_get(v_st_1024_, 8);
v_closed_1034_ = lean_ctor_get_uint8(v_st_1024_, sizeof(void*)*10);
v_pos_1035_ = lean_ctor_get(v_st_1024_, 9);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_st_1024_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1037_ = v_st_1024_;
v_isShared_1038_ = v_isSharedCheck_1046_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_pos_1035_);
lean_inc(v_nextId_1033_);
lean_inc(v_receivers_1032_);
lean_inc(v_read_1031_);
lean_inc(v_write_1030_);
lean_inc(v_buffer_1029_);
lean_inc(v_size_1028_);
lean_inc(v_capacity_1027_);
lean_inc(v_waiters_1026_);
lean_inc(v_producers_1025_);
lean_dec(v_st_1024_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1046_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v_size_1040_; lean_object* v___x_1041_; lean_object* v_read_1042_; lean_object* v___x_1044_; 
v___x_1039_ = lean_unsigned_to_nat(1u);
v_size_1040_ = lean_nat_sub(v_size_1028_, v___x_1039_);
lean_dec(v_size_1028_);
v___x_1041_ = lean_nat_add(v_read_1031_, v___x_1039_);
lean_dec(v_read_1031_);
v_read_1042_ = lean_nat_mod(v___x_1041_, v_capacity_1027_);
lean_dec(v___x_1041_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 6, v_read_1042_);
lean_ctor_set(v___x_1037_, 3, v_size_1040_);
v___x_1044_ = v___x_1037_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_producers_1025_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_waiters_1026_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_capacity_1027_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_size_1040_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_buffer_1029_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v_write_1030_);
lean_ctor_set(v_reuseFailAlloc_1045_, 6, v_read_1042_);
lean_ctor_set(v_reuseFailAlloc_1045_, 7, v_receivers_1032_);
lean_ctor_set(v_reuseFailAlloc_1045_, 8, v_nextId_1033_);
lean_ctor_set(v_reuseFailAlloc_1045_, 9, v_pos_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1045_, sizeof(void*)*10, v_closed_1034_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue(lean_object* v_00_u03b1_1047_, lean_object* v_st_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_st_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(lean_object* v_toApplicative_1050_, lean_object* v_place_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_capacity_1053_; lean_object* v_buffer_1054_; lean_object* v_toPure_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_capacity_1053_ = lean_ctor_get(v_a_1052_, 2);
v_buffer_1054_ = lean_ctor_get(v_a_1052_, 4);
v_toPure_1055_ = lean_ctor_get(v_toApplicative_1050_, 1);
lean_inc(v_toPure_1055_);
lean_dec_ref(v_toApplicative_1050_);
v___x_1056_ = lean_nat_mod(v_place_1051_, v_capacity_1053_);
v___x_1057_ = lean_array_fget_borrowed(v_buffer_1054_, v___x_1056_);
lean_dec(v___x_1056_);
lean_inc(v___x_1057_);
v___x_1058_ = lean_apply_2(v_toPure_1055_, lean_box(0), v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed(lean_object* v_toApplicative_1059_, lean_object* v_place_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0(v_toApplicative_1059_, v_place_1060_, v_a_1061_);
lean_dec_ref(v_a_1061_);
lean_dec(v_place_1060_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_place_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_toApplicative_1067_; lean_object* v_toBind_1068_; lean_object* v___f_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_toApplicative_1067_ = lean_ctor_get(v_inst_1063_, 0);
lean_inc_ref(v_toApplicative_1067_);
v_toBind_1068_ = lean_ctor_get(v_inst_1063_, 1);
lean_inc(v_toBind_1068_);
lean_dec_ref(v_inst_1063_);
v___f_1069_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1069_, 0, v_toApplicative_1067_);
lean_closure_set(v___f_1069_, 1, v_place_1065_);
lean_inc(v_a_1066_);
v___x_1070_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1070_, 0, lean_box(0));
lean_closure_set(v___x_1070_, 1, lean_box(0));
lean_closure_set(v___x_1070_, 2, v_a_1066_);
v___x_1071_ = lean_apply_2(v_inst_1064_, lean_box(0), v___x_1070_);
v___x_1072_ = lean_apply_4(v_toBind_1068_, lean_box(0), lean_box(0), v___x_1071_, v___f_1069_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg___boxed(lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_place_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1073_, v_inst_1074_, v_place_1075_, v_a_1076_);
lean_dec(v_a_1076_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(lean_object* v_m_1078_, lean_object* v_00_u03b1_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_place_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1080_, v_inst_1081_, v_place_1082_, v_a_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___boxed(lean_object* v_m_1085_, lean_object* v_00_u03b1_1086_, lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_place_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot(v_m_1085_, v_00_u03b1_1086_, v_inst_1087_, v_inst_1088_, v_place_1089_, v_a_1090_);
lean_dec(v_a_1090_);
return v_res_1091_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(lean_object* v_as_1092_, size_t v_sz_1093_, size_t v_i_1094_, lean_object* v_b_1095_){
_start:
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_usize_dec_lt(v_i_1094_, v_sz_1093_);
if (v___x_1097_ == 0)
{
return v_b_1095_;
}
else
{
lean_object* v___x_1098_; lean_object* v_a_1099_; lean_object* v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; 
v___x_1098_ = lean_box(0);
v_a_1099_ = lean_array_uget_borrowed(v_as_1092_, v_i_1094_);
v___x_1100_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1099_, v___x_1097_);
v___x_1101_ = ((size_t)1ULL);
v___x_1102_ = lean_usize_add(v_i_1094_, v___x_1101_);
v_i_1094_ = v___x_1102_;
v_b_1095_ = v___x_1098_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1092_ = stack[0].m_obj;
size_t v_sz_1093_ = stack[1].m_num;
size_t v_i_1094_ = stack[2].m_num;
lean_object* v_b_1095_ = stack[3].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1092_, v_sz_1093_, v_i_1094_, v_b_1095_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg___boxed(lean_object* v_as_1105_, lean_object* v_sz_1106_, lean_object* v_i_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_){
_start:
{
size_t v_sz_boxed_1110_; size_t v_i_boxed_1111_; lean_object* v_res_1112_; 
v_sz_boxed_1110_ = lean_unbox_usize(v_sz_1106_);
lean_dec(v_sz_1106_);
v_i_boxed_1111_ = lean_unbox_usize(v_i_1107_);
lean_dec(v_i_1107_);
v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1105_, v_sz_boxed_1110_, v_i_boxed_1111_, v_b_1108_);
lean_dec_ref(v_as_1105_);
return v_res_1112_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(lean_object* v_v_1113_, lean_object* v_a_1114_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isFull___redArg(v_a_1114_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v_producers_1119_; lean_object* v_waiters_1120_; lean_object* v_capacity_1121_; lean_object* v_size_1122_; lean_object* v_buffer_1123_; lean_object* v_write_1124_; lean_object* v_read_1125_; lean_object* v_receivers_1126_; lean_object* v_nextId_1127_; uint8_t v_closed_1128_; lean_object* v_pos_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1148_; 
v___x_1117_ = lean_st_ref_get(v_a_1114_);
v___x_1118_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_enqueue___redArg(v_v_1113_, v___x_1117_);
v_producers_1119_ = lean_ctor_get(v___x_1118_, 0);
v_waiters_1120_ = lean_ctor_get(v___x_1118_, 1);
v_capacity_1121_ = lean_ctor_get(v___x_1118_, 2);
v_size_1122_ = lean_ctor_get(v___x_1118_, 3);
v_buffer_1123_ = lean_ctor_get(v___x_1118_, 4);
v_write_1124_ = lean_ctor_get(v___x_1118_, 5);
v_read_1125_ = lean_ctor_get(v___x_1118_, 6);
v_receivers_1126_ = lean_ctor_get(v___x_1118_, 7);
v_nextId_1127_ = lean_ctor_get(v___x_1118_, 8);
v_closed_1128_ = lean_ctor_get_uint8(v___x_1118_, sizeof(void*)*10);
v_pos_1129_ = lean_ctor_get(v___x_1118_, 9);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1131_ = v___x_1118_;
v_isShared_1132_ = v_isSharedCheck_1148_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_pos_1129_);
lean_inc(v_nextId_1127_);
lean_inc(v_receivers_1126_);
lean_inc(v_read_1125_);
lean_inc(v_write_1124_);
lean_inc(v_buffer_1123_);
lean_inc(v_size_1122_);
lean_inc(v_capacity_1121_);
lean_inc(v_waiters_1120_);
lean_inc(v_producers_1119_);
lean_dec(v___x_1118_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1148_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
lean_inc(v_receivers_1126_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v___x_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_producers_1119_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_capacity_1121_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_size_1122_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_buffer_1123_);
lean_ctor_set(v_reuseFailAlloc_1147_, 5, v_write_1124_);
lean_ctor_set(v_reuseFailAlloc_1147_, 6, v_read_1125_);
lean_ctor_set(v_reuseFailAlloc_1147_, 7, v_receivers_1126_);
lean_ctor_set(v_reuseFailAlloc_1147_, 8, v_nextId_1127_);
lean_ctor_set(v_reuseFailAlloc_1147_, 9, v_pos_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1147_, sizeof(void*)*10, v_closed_1128_);
v___x_1135_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; size_t v_sz_1139_; size_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___y_1143_; 
v___x_1136_ = lean_st_ref_swap(v_a_1114_, v___x_1135_);
lean_dec(v___x_1136_);
v___x_1137_ = l_Std_Queue_toArray___redArg(v_waiters_1120_);
v___x_1138_ = lean_box(0);
v_sz_1139_ = lean_array_size(v___x_1137_);
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v___x_1137_, v_sz_1139_, v___x_1140_, v___x_1138_);
lean_dec_ref(v___x_1137_);
if (lean_obj_tag(v_receivers_1126_) == 0)
{
lean_object* v_size_1145_; 
v_size_1145_ = lean_ctor_get(v_receivers_1126_, 0);
lean_inc(v_size_1145_);
lean_dec_ref_known(v_receivers_1126_, 5);
v___y_1143_ = v_size_1145_;
goto v___jp_1142_;
}
else
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v___y_1143_ = v___x_1146_;
goto v___jp_1142_;
}
v___jp_1142_:
{
lean_object* v___x_1144_; 
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___y_1143_);
return v___x_1144_;
}
}
}
}
else
{
lean_object* v___x_1149_; 
lean_dec(v_v_1113_);
v___x_1149_ = lean_box(0);
return v___x_1149_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1113_ = stack[0].m_obj;
lean_object* v_a_1114_ = stack[1].m_obj;
lean_object* v_res_1150_;
v_res_1150_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1113_, v_a_1114_);
stack->m_obj
 = v_res_1150_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg___boxed(lean_object* v_v_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1151_, v_a_1152_);
lean_dec(v_a_1152_);
return v_res_1154_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(lean_object* v_00_u03b1_1155_, lean_object* v_v_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1156_, v_a_1157_);
return v___x_1159_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1156_ = stack[1].m_obj;
lean_object* v_a_1157_ = stack[2].m_obj;
lean_object* v_res_1160_;
v_res_1160_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(lean_box(0), v_v_1156_, v_a_1157_);
stack->m_obj
 = v_res_1160_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_v_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27(v_00_u03b1_1161_, v_v_1162_, v_a_1163_);
lean_dec(v_a_1163_);
return v_res_1165_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(lean_object* v_00_u03b1_1166_, lean_object* v_as_1167_, size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_b_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___redArg(v_as_1167_, v_sz_1168_, v_i_1169_, v_b_1170_);
return v___x_1173_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1167_ = stack[1].m_obj;
size_t v_sz_1168_ = stack[2].m_num;
size_t v_i_1169_ = stack[3].m_num;
lean_object* v_b_1170_ = stack[4].m_obj;
lean_object* v___y_1171_ = stack[5].m_obj;
lean_object* v_res_1174_;
v_res_1174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(lean_box(0), v_as_1167_, v_sz_1168_, v_i_1169_, v_b_1170_, v___y_1171_);
stack->m_obj
 = v_res_1174_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0___boxed(lean_object* v_00_u03b1_1175_, lean_object* v_as_1176_, lean_object* v_sz_1177_, lean_object* v_i_1178_, lean_object* v_b_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
size_t v_sz_boxed_1182_; size_t v_i_boxed_1183_; lean_object* v_res_1184_; 
v_sz_boxed_1182_ = lean_unbox_usize(v_sz_1177_);
lean_dec(v_sz_1177_);
v_i_boxed_1183_ = lean_unbox_usize(v_i_1178_);
lean_dec(v_i_1178_);
v_res_1184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27_spec__0(v_00_u03b1_1175_, v_as_1176_, v_sz_boxed_1182_, v_i_boxed_1183_, v_b_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v_as_1176_);
return v_res_1184_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(lean_object* v_mutex_1185_, lean_object* v_k_1186_){
_start:
{
lean_object* v_ref_1188_; lean_object* v_mutex_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_ref_1188_ = lean_ctor_get(v_mutex_1185_, 0);
lean_inc(v_ref_1188_);
v_mutex_1189_ = lean_ctor_get(v_mutex_1185_, 1);
lean_inc(v_mutex_1189_);
lean_dec_ref(v_mutex_1185_);
v___x_1190_ = lean_io_basemutex_lock(v_mutex_1189_);
v___x_1191_ = lean_apply_2(v_k_1186_, v_ref_1188_, lean_box(0));
v___x_1192_ = lean_io_basemutex_unlock(v_mutex_1189_);
lean_dec(v_mutex_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1185_ = stack[0].m_obj;
lean_object* v_k_1186_ = stack[1].m_obj;
lean_object* v_res_1193_;
v_res_1193_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1185_, v_k_1186_);
stack->m_obj
 = v_res_1193_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg___boxed(lean_object* v_mutex_1194_, lean_object* v_k_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1194_, v_k_1195_);
return v_res_1197_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_mutex_1200_, lean_object* v_k_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_mutex_1200_, v_k_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1200_ = stack[2].m_obj;
lean_object* v_k_1201_ = stack[3].m_obj;
lean_object* v_res_1204_;
v_res_1204_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(lean_box(0), lean_box(0), v_mutex_1200_, v_k_1201_);
stack->m_obj
 = v_res_1204_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___boxed(lean_object* v_00_u03b1_1205_, lean_object* v_00_u03b2_1206_, lean_object* v_mutex_1207_, lean_object* v_k_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v_res_1210_; 
v_res_1210_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0(v_00_u03b1_1205_, v_00_u03b2_1206_, v_mutex_1207_, v_k_1208_);
return v_res_1210_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(lean_object* v_v_1213_, lean_object* v___y_1214_){
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
v___x_1220_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1213_, v___y_1214_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; 
lean_dec(v_v_1213_);
v___x_1221_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___closed__0));
return v___x_1221_;
}
}
else
{
lean_object* v___x_1222_; 
lean_dec(v_v_1213_);
v___x_1222_ = lean_box(0);
return v___x_1222_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1213_ = stack[0].m_obj;
lean_object* v___y_1214_ = stack[1].m_obj;
lean_object* v_res_1223_;
v_res_1223_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(v_v_1213_, v___y_1214_);
stack->m_obj
 = v_res_1223_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed(lean_object* v_v_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0(v_v_1224_, v___y_1225_);
lean_dec(v___y_1225_);
return v_res_1227_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(lean_object* v_ch_1228_, lean_object* v_v_1229_){
_start:
{
lean_object* v___f_1231_; lean_object* v___x_1232_; 
v___f_1231_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1231_, 0, v_v_1229_);
v___x_1232_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1228_, v___f_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1228_ = stack[0].m_obj;
lean_object* v_v_1229_ = stack[1].m_obj;
lean_object* v_res_1233_;
v_res_1233_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1228_, v_v_1229_);
stack->m_obj
 = v_res_1233_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg___boxed(lean_object* v_ch_1234_, lean_object* v_v_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1234_, v_v_1235_);
return v_res_1237_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(lean_object* v_00_u03b1_1238_, lean_object* v_ch_1239_, lean_object* v_v_1240_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_1239_, v_v_1240_);
return v___x_1242_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1239_ = stack[1].m_obj;
lean_object* v_v_1240_ = stack[2].m_obj;
lean_object* v_res_1243_;
v_res_1243_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(lean_box(0), v_ch_1239_, v_v_1240_);
stack->m_obj
 = v_res_1243_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___boxed(lean_object* v_00_u03b1_1244_, lean_object* v_ch_1245_, lean_object* v_v_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend(v_00_u03b1_1244_, v_ch_1245_, v_v_1246_);
return v_res_1248_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__0));
v___x_1252_ = lean_task_pure(v___x_1251_);
return v___x_1252_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1256_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__2));
v___x_1257_ = lean_task_pure(v___x_1256_);
return v___x_1257_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(lean_object* v_v_1258_, lean_object* v___f_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; uint8_t v_closed_1263_; 
v___x_1262_ = lean_st_ref_get(v___y_1260_);
v_closed_1263_ = lean_ctor_get_uint8(v___x_1262_, sizeof(void*)*10);
lean_dec(v___x_1262_);
if (v_closed_1263_ == 0)
{
lean_object* v___x_1264_; lean_object* v_receivers_1265_; 
v___x_1264_ = lean_st_ref_get(v___y_1260_);
v_receivers_1265_ = lean_ctor_get(v___x_1264_, 7);
lean_inc(v_receivers_1265_);
lean_dec(v___x_1264_);
if (lean_obj_tag(v_receivers_1265_) == 0)
{
lean_object* v___x_1266_; 
lean_dec_ref_known(v_receivers_1265_, 5);
v___x_1266_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend_x27___redArg(v_v_1258_, v___y_1260_);
if (lean_obj_tag(v___x_1266_) == 1)
{
lean_object* v_val_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v___f_1259_);
v_val_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_val_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1275_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_val_1267_);
v___x_1272_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_task_pure(v___x_1272_);
return v___x_1273_;
}
}
}
else
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v_producers_1278_; lean_object* v_waiters_1279_; lean_object* v_capacity_1280_; lean_object* v_size_1281_; lean_object* v_buffer_1282_; lean_object* v_write_1283_; lean_object* v_read_1284_; lean_object* v_receivers_1285_; lean_object* v_nextId_1286_; uint8_t v_closed_1287_; lean_object* v_pos_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v___x_1266_);
v___x_1276_ = lean_io_promise_new();
v___x_1277_ = lean_st_ref_take(v___y_1260_);
v_producers_1278_ = lean_ctor_get(v___x_1277_, 0);
v_waiters_1279_ = lean_ctor_get(v___x_1277_, 1);
v_capacity_1280_ = lean_ctor_get(v___x_1277_, 2);
v_size_1281_ = lean_ctor_get(v___x_1277_, 3);
v_buffer_1282_ = lean_ctor_get(v___x_1277_, 4);
v_write_1283_ = lean_ctor_get(v___x_1277_, 5);
v_read_1284_ = lean_ctor_get(v___x_1277_, 6);
v_receivers_1285_ = lean_ctor_get(v___x_1277_, 7);
v_nextId_1286_ = lean_ctor_get(v___x_1277_, 8);
v_closed_1287_ = lean_ctor_get_uint8(v___x_1277_, sizeof(void*)*10);
v_pos_1288_ = lean_ctor_get(v___x_1277_, 9);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1290_ = v___x_1277_;
v_isShared_1291_ = v_isSharedCheck_1300_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_pos_1288_);
lean_inc(v_nextId_1286_);
lean_inc(v_receivers_1285_);
lean_inc(v_read_1284_);
lean_inc(v_write_1283_);
lean_inc(v_buffer_1282_);
lean_inc(v_size_1281_);
lean_inc(v_capacity_1280_);
lean_inc(v_waiters_1279_);
lean_inc(v_producers_1278_);
lean_dec(v___x_1277_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1300_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
lean_inc(v___x_1276_);
v___x_1292_ = l_Std_Queue_enqueue___redArg(v___x_1276_, v_producers_1278_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1292_);
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_waiters_1279_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v_capacity_1280_);
lean_ctor_set(v_reuseFailAlloc_1299_, 3, v_size_1281_);
lean_ctor_set(v_reuseFailAlloc_1299_, 4, v_buffer_1282_);
lean_ctor_set(v_reuseFailAlloc_1299_, 5, v_write_1283_);
lean_ctor_set(v_reuseFailAlloc_1299_, 6, v_read_1284_);
lean_ctor_set(v_reuseFailAlloc_1299_, 7, v_receivers_1285_);
lean_ctor_set(v_reuseFailAlloc_1299_, 8, v_nextId_1286_);
lean_ctor_set(v_reuseFailAlloc_1299_, 9, v_pos_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1299_, sizeof(void*)*10, v_closed_1287_);
v___x_1294_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1295_ = lean_st_ref_put(v___y_1260_, v___x_1294_);
v___x_1296_ = lean_io_promise_result_opt(v___x_1276_);
lean_dec(v___x_1276_);
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_io_bind_task(v___x_1296_, v___f_1259_, v___x_1297_, v_closed_1263_);
return v___x_1298_;
}
}
}
}
else
{
lean_object* v___x_1301_; 
lean_dec_ref(v___f_1259_);
lean_dec(v_v_1258_);
v___x_1301_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__1);
return v___x_1301_;
}
}
else
{
lean_object* v___x_1302_; 
lean_dec_ref(v___f_1259_);
lean_dec(v_v_1258_);
v___x_1302_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1302_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1258_ = stack[0].m_obj;
lean_object* v___f_1259_ = stack[1].m_obj;
lean_object* v___y_1260_ = stack[2].m_obj;
lean_object* v_res_1303_;
v_res_1303_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(v_v_1258_, v___f_1259_, v___y_1260_);
stack->m_obj
 = v_res_1303_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed(lean_object* v_v_1304_, lean_object* v___f_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1(v_v_1304_, v___f_1305_, v___y_1306_);
lean_dec(v___y_1306_);
return v_res_1308_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(lean_object* v_ch_1309_, lean_object* v_v_1310_, lean_object* v_res_1311_){
_start:
{
if (lean_obj_tag(v_res_1311_) == 0)
{
lean_dec(v_v_1310_);
lean_dec_ref(v_ch_1309_);
goto v___jp_1313_;
}
else
{
lean_object* v_val_1315_; uint8_t v___x_1316_; 
v_val_1315_ = lean_ctor_get(v_res_1311_, 0);
v___x_1316_ = lean_unbox(v_val_1315_);
if (v___x_1316_ == 0)
{
lean_dec(v_v_1310_);
lean_dec_ref(v_ch_1309_);
goto v___jp_1313_;
}
else
{
lean_object* v___x_1317_; 
v___x_1317_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1309_, v_v_1310_);
return v___x_1317_;
}
}
v___jp_1313_:
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3, &l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___closed__3);
return v___x_1314_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1309_ = stack[0].m_obj;
lean_object* v_v_1310_ = stack[1].m_obj;
lean_object* v_res_1311_ = stack[2].m_obj;
lean_object* v_res_1318_;
v_res_1318_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(v_ch_1309_, v_v_1310_, v_res_1311_);
stack->m_obj
 = v_res_1318_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed(lean_object* v_ch_1319_, lean_object* v_v_1320_, lean_object* v_res_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0(v_ch_1319_, v_v_1320_, v_res_1321_);
lean_dec(v_res_1321_);
return v_res_1323_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(lean_object* v_ch_1324_, lean_object* v_v_1325_){
_start:
{
lean_object* v___f_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; 
lean_inc(v_v_1325_);
lean_inc_ref(v_ch_1324_);
v___f_1327_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_1327_, 0, v_ch_1324_);
lean_closure_set(v___f_1327_, 1, v_v_1325_);
v___f_1328_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1328_, 0, v_v_1325_);
lean_closure_set(v___f_1328_, 1, v___f_1327_);
v___x_1329_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1324_, v___f_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1324_ = stack[0].m_obj;
lean_object* v_v_1325_ = stack[1].m_obj;
lean_object* v_res_1330_;
v_res_1330_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1324_, v_v_1325_);
stack->m_obj
 = v_res_1330_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg___boxed(lean_object* v_ch_1331_, lean_object* v_v_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1331_, v_v_1332_);
return v_res_1334_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send(lean_object* v_00_u03b1_1335_, lean_object* v_ch_1336_, lean_object* v_v_1337_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_1336_, v_v_1337_);
return v___x_1339_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1336_ = stack[1].m_obj;
lean_object* v_v_1337_ = stack[2].m_obj;
lean_object* v_res_1340_;
v_res_1340_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send(lean_box(0), v_ch_1336_, v_v_1337_);
stack->m_obj
 = v_res_1340_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_send___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_ch_1342_, lean_object* v_v_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send(v_00_u03b1_1341_, v_ch_1342_, v_v_1343_);
return v_res_1345_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(lean_object* v_mutex_1346_, lean_object* v_k_1347_){
_start:
{
lean_object* v_ref_1349_; lean_object* v_mutex_1350_; lean_object* v___x_1351_; lean_object* v_r_1352_; 
v_ref_1349_ = lean_ctor_get(v_mutex_1346_, 0);
lean_inc(v_ref_1349_);
v_mutex_1350_ = lean_ctor_get(v_mutex_1346_, 1);
lean_inc(v_mutex_1350_);
lean_dec_ref(v_mutex_1346_);
v___x_1351_ = lean_io_basemutex_lock(v_mutex_1350_);
v_r_1352_ = lean_apply_2(v_k_1347_, v_ref_1349_, lean_box(0));
if (lean_obj_tag(v_r_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1361_; 
v_a_1353_ = lean_ctor_get(v_r_1352_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_r_1352_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1355_ = v_r_1352_;
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v_r_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1361_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = lean_io_basemutex_unlock(v_mutex_1350_);
lean_dec(v_mutex_1350_);
if (v_isShared_1356_ == 0)
{
v___x_1359_ = v___x_1355_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1353_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1370_; 
v_a_1362_ = lean_ctor_get(v_r_1352_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_r_1352_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1364_ = v_r_1352_;
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v_r_1352_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1370_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1366_ = lean_io_basemutex_unlock(v_mutex_1350_);
lean_dec(v_mutex_1350_);
if (v_isShared_1365_ == 0)
{
v___x_1368_ = v___x_1364_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1362_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1346_ = stack[0].m_obj;
lean_object* v_k_1347_ = stack[1].m_obj;
lean_object* v_res_1371_;
v_res_1371_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(v_mutex_1346_, v_k_1347_);
stack->m_obj
 = v_res_1371_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg___boxed(lean_object* v_mutex_1372_, lean_object* v_k_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(v_mutex_1372_, v_k_1373_);
return v_res_1375_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2(lean_object* v_00_u03b1_1376_, lean_object* v_00_u03b2_1377_, lean_object* v_mutex_1378_, lean_object* v_k_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(v_mutex_1378_, v_k_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_1378_ = stack[2].m_obj;
lean_object* v_k_1379_ = stack[3].m_obj;
lean_object* v_res_1382_;
v_res_1382_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2(lean_box(0), lean_box(0), v_mutex_1378_, v_k_1379_);
stack->m_obj
 = v_res_1382_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___boxed(lean_object* v_00_u03b1_1383_, lean_object* v_00_u03b2_1384_, lean_object* v_mutex_1385_, lean_object* v_k_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2(v_00_u03b1_1383_, v_00_u03b2_1384_, v_mutex_1385_, v_k_1386_);
return v_res_1388_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(uint8_t v___x_1389_, lean_object* v_as_1390_, size_t v_sz_1391_, size_t v_i_1392_, lean_object* v_b_1393_){
_start:
{
uint8_t v___x_1395_; 
v___x_1395_ = lean_usize_dec_lt(v_i_1392_, v_sz_1391_);
if (v___x_1395_ == 0)
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_b_1393_);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; lean_object* v_a_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; size_t v___x_1401_; size_t v___x_1402_; 
v___x_1397_ = lean_box(0);
v_a_1398_ = lean_array_uget_borrowed(v_as_1390_, v_i_1392_);
v___x_1399_ = lean_box(v___x_1389_);
v___x_1400_ = lean_io_promise_resolve(v___x_1399_, v_a_1398_);
v___x_1401_ = ((size_t)1ULL);
v___x_1402_ = lean_usize_add(v_i_1392_, v___x_1401_);
v_i_1392_ = v___x_1402_;
v_b_1393_ = v___x_1397_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1389_ = stack[0].m_num;
lean_object* v_as_1390_ = stack[1].m_obj;
size_t v_sz_1391_ = stack[2].m_num;
size_t v_i_1392_ = stack[3].m_num;
lean_object* v_b_1393_ = stack[4].m_obj;
lean_object* v_res_1404_;
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v___x_1389_, v_as_1390_, v_sz_1391_, v_i_1392_, v_b_1393_);
stack->m_obj
 = v_res_1404_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg___boxed(lean_object* v___x_1405_, lean_object* v_as_1406_, lean_object* v_sz_1407_, lean_object* v_i_1408_, lean_object* v_b_1409_, lean_object* v___y_1410_){
_start:
{
uint8_t v___x_2137__boxed_1411_; size_t v_sz_boxed_1412_; size_t v_i_boxed_1413_; lean_object* v_res_1414_; 
v___x_2137__boxed_1411_ = lean_unbox(v___x_1405_);
v_sz_boxed_1412_ = lean_unbox_usize(v_sz_1407_);
lean_dec(v_sz_1407_);
v_i_boxed_1413_ = lean_unbox_usize(v_i_1408_);
lean_dec(v_i_1408_);
v_res_1414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v___x_2137__boxed_1411_, v_as_1406_, v_sz_boxed_1412_, v_i_boxed_1413_, v_b_1409_);
lean_dec_ref(v_as_1406_);
return v_res_1414_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(uint8_t v___x_1415_, lean_object* v_as_1416_, size_t v_sz_1417_, size_t v_i_1418_, lean_object* v_b_1419_){
_start:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_usize_dec_lt(v_i_1418_, v_sz_1417_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_b_1419_);
return v___x_1422_;
}
else
{
lean_object* v___x_1423_; lean_object* v_a_1424_; lean_object* v___x_1425_; size_t v___x_1426_; size_t v___x_1427_; 
v___x_1423_ = lean_box(0);
v_a_1424_ = lean_array_uget_borrowed(v_as_1416_, v_i_1418_);
v___x_1425_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_a_1424_, v___x_1415_);
v___x_1426_ = ((size_t)1ULL);
v___x_1427_ = lean_usize_add(v_i_1418_, v___x_1426_);
v_i_1418_ = v___x_1427_;
v_b_1419_ = v___x_1423_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1415_ = stack[0].m_num;
lean_object* v_as_1416_ = stack[1].m_obj;
size_t v_sz_1417_ = stack[2].m_num;
size_t v_i_1418_ = stack[3].m_num;
lean_object* v_b_1419_ = stack[4].m_obj;
lean_object* v_res_1429_;
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1415_, v_as_1416_, v_sz_1417_, v_i_1418_, v_b_1419_);
stack->m_obj
 = v_res_1429_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg___boxed(lean_object* v___x_1430_, lean_object* v_as_1431_, lean_object* v_sz_1432_, lean_object* v_i_1433_, lean_object* v_b_1434_, lean_object* v___y_1435_){
_start:
{
uint8_t v___x_2171__boxed_1436_; size_t v_sz_boxed_1437_; size_t v_i_boxed_1438_; lean_object* v_res_1439_; 
v___x_2171__boxed_1436_ = lean_unbox(v___x_1430_);
v_sz_boxed_1437_ = lean_unbox_usize(v_sz_1432_);
lean_dec(v_sz_1432_);
v_i_boxed_1438_ = lean_unbox_usize(v_i_1433_);
lean_dec(v_i_1433_);
v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_2171__boxed_1436_, v_as_1431_, v_sz_boxed_1437_, v_i_boxed_1438_, v_b_1434_);
lean_dec_ref(v_as_1431_);
return v_res_1439_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; uint8_t v_closed_1443_; 
v___x_1442_ = lean_st_ref_get(v___y_1440_);
v_closed_1443_ = lean_ctor_get_uint8(v___x_1442_, sizeof(void*)*10);
if (v_closed_1443_ == 0)
{
lean_object* v_producers_1444_; lean_object* v_waiters_1445_; lean_object* v_capacity_1446_; lean_object* v_size_1447_; lean_object* v_buffer_1448_; lean_object* v_write_1449_; lean_object* v_read_1450_; lean_object* v_receivers_1451_; lean_object* v_nextId_1452_; lean_object* v_pos_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1479_; 
v_producers_1444_ = lean_ctor_get(v___x_1442_, 0);
v_waiters_1445_ = lean_ctor_get(v___x_1442_, 1);
v_capacity_1446_ = lean_ctor_get(v___x_1442_, 2);
v_size_1447_ = lean_ctor_get(v___x_1442_, 3);
v_buffer_1448_ = lean_ctor_get(v___x_1442_, 4);
v_write_1449_ = lean_ctor_get(v___x_1442_, 5);
v_read_1450_ = lean_ctor_get(v___x_1442_, 6);
v_receivers_1451_ = lean_ctor_get(v___x_1442_, 7);
v_nextId_1452_ = lean_ctor_get(v___x_1442_, 8);
v_pos_1453_ = lean_ctor_get(v___x_1442_, 9);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1455_ = v___x_1442_;
v_isShared_1456_ = v_isSharedCheck_1479_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_pos_1453_);
lean_inc(v_nextId_1452_);
lean_inc(v_receivers_1451_);
lean_inc(v_read_1450_);
lean_inc(v_write_1449_);
lean_inc(v_buffer_1448_);
lean_inc(v_size_1447_);
lean_inc(v_capacity_1446_);
lean_inc(v_waiters_1445_);
lean_inc(v_producers_1444_);
lean_dec(v___x_1442_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1479_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; size_t v_sz_1459_; size_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1457_ = l_Std_Queue_toArray___redArg(v_waiters_1445_);
v___x_1458_ = lean_box(0);
v_sz_1459_ = lean_array_size(v___x_1457_);
v___x_1460_ = ((size_t)0ULL);
v___x_1461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v_closed_1443_, v___x_1457_, v_sz_1459_, v___x_1460_, v___x_1458_);
lean_dec_ref(v___x_1457_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v___x_1462_; size_t v_sz_1463_; lean_object* v___x_1464_; 
lean_dec_ref_known(v___x_1461_, 1);
v___x_1462_ = l_Std_Queue_toArray___redArg(v_producers_1444_);
v_sz_1463_ = lean_array_size(v___x_1462_);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v_closed_1443_, v___x_1462_, v_sz_1463_, v___x_1460_, v___x_1458_);
lean_dec_ref(v___x_1462_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1477_; 
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1477_ == 0)
{
lean_object* v_unused_1478_; 
v_unused_1478_ = lean_ctor_get(v___x_1464_, 0);
lean_dec(v_unused_1478_);
v___x_1466_ = v___x_1464_;
v_isShared_1467_ = v_isSharedCheck_1477_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v___x_1464_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1477_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1471_; 
v___x_1468_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg___closed__2);
v___x_1469_ = 1;
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v___x_1468_);
lean_ctor_set(v___x_1455_, 0, v___x_1468_);
v___x_1471_ = v___x_1455_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_capacity_1446_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_size_1447_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_buffer_1448_);
lean_ctor_set(v_reuseFailAlloc_1476_, 5, v_write_1449_);
lean_ctor_set(v_reuseFailAlloc_1476_, 6, v_read_1450_);
lean_ctor_set(v_reuseFailAlloc_1476_, 7, v_receivers_1451_);
lean_ctor_set(v_reuseFailAlloc_1476_, 8, v_nextId_1452_);
lean_ctor_set(v_reuseFailAlloc_1476_, 9, v_pos_1453_);
v___x_1471_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_ctor_set_uint8(v___x_1471_, sizeof(void*)*10, v___x_1469_);
v___x_1472_ = lean_st_ref_swap(v___y_1440_, v___x_1471_);
lean_dec(v___x_1472_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1458_);
v___x_1474_ = v___x_1466_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1458_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_del_object(v___x_1455_);
lean_dec(v_pos_1453_);
lean_dec(v_nextId_1452_);
lean_dec(v_receivers_1451_);
lean_dec(v_read_1450_);
lean_dec(v_write_1449_);
lean_dec_ref(v_buffer_1448_);
lean_dec(v_size_1447_);
lean_dec(v_capacity_1446_);
return v___x_1464_;
}
}
else
{
lean_del_object(v___x_1455_);
lean_dec(v_pos_1453_);
lean_dec(v_nextId_1452_);
lean_dec(v_receivers_1451_);
lean_dec(v_read_1450_);
lean_dec(v_write_1449_);
lean_dec_ref(v_buffer_1448_);
lean_dec(v_size_1447_);
lean_dec(v_capacity_1446_);
lean_dec_ref(v_producers_1444_);
return v___x_1461_;
}
}
}
else
{
uint8_t v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
lean_dec(v___x_1442_);
v___x_1480_ = 1;
v___x_1481_ = lean_box(v___x_1480_);
v___x_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
return v___x_1482_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1440_ = stack[0].m_obj;
lean_object* v_res_1483_;
v_res_1483_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(v___y_1440_);
stack->m_obj
 = v_res_1483_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0___boxed(lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___lam__0(v___y_1484_);
lean_dec(v___y_1484_);
return v_res_1486_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(lean_object* v_ch_1488_){
_start:
{
lean_object* v___f_1490_; lean_object* v___x_1491_; 
v___f_1490_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___closed__0));
v___x_1491_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__2___redArg(v_ch_1488_, v___f_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1488_ = stack[0].m_obj;
lean_object* v_res_1492_;
v_res_1492_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1488_);
stack->m_obj
 = v_res_1492_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg___boxed(lean_object* v_ch_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1493_);
return v_res_1495_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close(lean_object* v_00_u03b1_1496_, lean_object* v_ch_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1497_ = stack[1].m_obj;
lean_object* v_res_1500_;
v_res_1500_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close(lean_box(0), v_ch_1497_);
stack->m_obj
 = v_res_1500_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_close___boxed(lean_object* v_00_u03b1_1501_, lean_object* v_ch_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close(v_00_u03b1_1501_, v_ch_1502_);
return v_res_1504_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(lean_object* v_00_u03b1_1505_, uint8_t v___x_1506_, lean_object* v_as_1507_, size_t v_sz_1508_, size_t v_i_1509_, lean_object* v_b_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___redArg(v___x_1506_, v_as_1507_, v_sz_1508_, v_i_1509_, v_b_1510_);
return v___x_1513_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1506_ = stack[1].m_num;
lean_object* v_as_1507_ = stack[2].m_obj;
size_t v_sz_1508_ = stack[3].m_num;
size_t v_i_1509_ = stack[4].m_num;
lean_object* v_b_1510_ = stack[5].m_obj;
lean_object* v___y_1511_ = stack[6].m_obj;
lean_object* v_res_1514_;
v_res_1514_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(lean_box(0), v___x_1506_, v_as_1507_, v_sz_1508_, v_i_1509_, v_b_1510_, v___y_1511_);
stack->m_obj
 = v_res_1514_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0___boxed(lean_object* v_00_u03b1_1515_, lean_object* v___x_1516_, lean_object* v_as_1517_, lean_object* v_sz_1518_, lean_object* v_i_1519_, lean_object* v_b_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
uint8_t v___x_2324__boxed_1523_; size_t v_sz_boxed_1524_; size_t v_i_boxed_1525_; lean_object* v_res_1526_; 
v___x_2324__boxed_1523_ = lean_unbox(v___x_1516_);
v_sz_boxed_1524_ = lean_unbox_usize(v_sz_1518_);
lean_dec(v_sz_1518_);
v_i_boxed_1525_ = lean_unbox_usize(v_i_1519_);
lean_dec(v_i_1519_);
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__0(v_00_u03b1_1515_, v___x_2324__boxed_1523_, v_as_1517_, v_sz_boxed_1524_, v_i_boxed_1525_, v_b_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v_as_1517_);
return v_res_1526_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(lean_object* v_00_u03b1_1527_, uint8_t v___x_1528_, lean_object* v_as_1529_, size_t v_sz_1530_, size_t v_i_1531_, lean_object* v_b_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___redArg(v___x_1528_, v_as_1529_, v_sz_1530_, v_i_1531_, v_b_1532_);
return v___x_1535_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1528_ = stack[1].m_num;
lean_object* v_as_1529_ = stack[2].m_obj;
size_t v_sz_1530_ = stack[3].m_num;
size_t v_i_1531_ = stack[4].m_num;
lean_object* v_b_1532_ = stack[5].m_obj;
lean_object* v___y_1533_ = stack[6].m_obj;
lean_object* v_res_1536_;
v_res_1536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(lean_box(0), v___x_1528_, v_as_1529_, v_sz_1530_, v_i_1531_, v_b_1532_, v___y_1533_);
stack->m_obj
 = v_res_1536_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1___boxed(lean_object* v_00_u03b1_1537_, lean_object* v___x_1538_, lean_object* v_as_1539_, lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
uint8_t v___x_2342__boxed_1545_; size_t v_sz_boxed_1546_; size_t v_i_boxed_1547_; lean_object* v_res_1548_; 
v___x_2342__boxed_1545_ = lean_unbox(v___x_1538_);
v_sz_boxed_1546_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1547_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_close_spec__1(v_00_u03b1_1537_, v___x_2342__boxed_1545_, v_as_1539_, v_sz_boxed_1546_, v_i_boxed_1547_, v_b_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v_as_1539_);
return v_res_1548_;
}
}
uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; uint8_t v_closed_1552_; 
v___x_1551_ = lean_st_ref_get(v___y_1549_);
v_closed_1552_ = lean_ctor_get_uint8(v___x_1551_, sizeof(void*)*10);
lean_dec(v___x_1551_);
return v_closed_1552_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1549_ = stack[0].m_obj;
uint8_t v_res_1553_;
v_res_1553_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(v___y_1549_);
stack->m_num = v_res_1553_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0___boxed(lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v_res_1556_; lean_object* v_r_1557_; 
v_res_1556_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___lam__0(v___y_1554_);
lean_dec(v___y_1554_);
v_r_1557_ = lean_box(v_res_1556_);
return v_r_1557_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(lean_object* v_ch_1559_){
_start:
{
lean_object* v___f_1561_; lean_object* v___x_1562_; 
v___f_1561_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___closed__0));
v___x_1562_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_ch_1559_, v___f_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1559_ = stack[0].m_obj;
lean_object* v_res_1563_;
v_res_1563_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1559_);
stack->m_obj
 = v_res_1563_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg___boxed(lean_object* v_ch_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1564_);
return v_res_1566_;
}
}
uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(lean_object* v_00_u03b1_1567_, lean_object* v_ch_1568_){
_start:
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___redArg(v_ch_1568_);
v___x_1571_ = lean_unbox(v___x_1570_);
lean_dec(v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_1568_ = stack[1].m_obj;
uint8_t v_res_1572_;
v_res_1572_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(lean_box(0), v_ch_1568_);
stack->m_num = v_res_1572_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_ch_1574_, lean_object* v_a_1575_){
_start:
{
uint8_t v_res_1576_; lean_object* v_r_1577_; 
v_res_1576_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isClosed(v_00_u03b1_1573_, v_ch_1574_);
v_r_1577_ = lean_box(v_res_1576_);
return v_r_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(lean_object* v_next_1578_, lean_object* v_slot_1579_){
_start:
{
lean_object* v_value_1580_; lean_object* v_pos_1581_; lean_object* v_remaining_1582_; uint8_t v___x_1583_; 
v_value_1580_ = lean_ctor_get(v_slot_1579_, 0);
v_pos_1581_ = lean_ctor_get(v_slot_1579_, 1);
v_remaining_1582_ = lean_ctor_get(v_slot_1579_, 2);
v___x_1583_ = lean_nat_dec_eq(v_next_1578_, v_pos_1581_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_box(v___x_1583_);
v___x_1586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v_slot_1579_);
return v___x_1587_;
}
else
{
lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1608_; 
lean_inc(v_remaining_1582_);
lean_inc(v_pos_1581_);
lean_inc(v_value_1580_);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_slot_1579_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; lean_object* v_unused_1610_; lean_object* v_unused_1611_; 
v_unused_1609_ = lean_ctor_get(v_slot_1579_, 2);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_slot_1579_, 1);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_slot_1579_, 0);
lean_dec(v_unused_1611_);
v___x_1589_ = v_slot_1579_;
v_isShared_1590_ = v_isSharedCheck_1608_;
goto v_resetjp_1588_;
}
else
{
lean_dec(v_slot_1579_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1608_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_unsigned_to_nat(1u);
v___x_1592_ = lean_nat_dec_eq(v_remaining_1582_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1593_ = lean_box(v___x_1592_);
lean_inc(v_value_1580_);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v_value_1580_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = lean_nat_sub(v_remaining_1582_, v___x_1591_);
lean_dec(v_remaining_1582_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 2, v___x_1595_);
v___x_1597_ = v___x_1589_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_value_1580_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_pos_1581_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1594_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
return v___x_1598_;
}
}
else
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
lean_dec(v_remaining_1582_);
v___x_1600_ = lean_box(v___x_1583_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v_value_1580_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_box(0);
v___x_1603_ = lean_unsigned_to_nat(0u);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 2, v___x_1603_);
lean_ctor_set(v___x_1589_, 0, v___x_1602_);
v___x_1605_ = v___x_1589_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_pos_1581_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; 
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1601_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
return v___x_1606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed(lean_object* v_next_1612_, lean_object* v_slot_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0(v_next_1612_, v_slot_1613_);
lean_dec(v_next_1612_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(lean_object* v_inst_1615_, lean_object* v_slot_1616_, lean_object* v_next_1617_){
_start:
{
lean_object* v___f_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___f_1618_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1618_, 0, v_next_1617_);
v___x_1619_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_1619_, 0, lean_box(0));
lean_closure_set(v___x_1619_, 1, lean_box(0));
lean_closure_set(v___x_1619_, 2, lean_box(0));
lean_closure_set(v___x_1619_, 3, v_slot_1616_);
lean_closure_set(v___x_1619_, 4, v___f_1618_);
v___x_1620_ = lean_apply_2(v_inst_1615_, lean_box(0), v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(lean_object* v_m_1621_, lean_object* v_00_u03b1_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_slot_1625_, lean_object* v_next_1626_, lean_object* v_a_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1624_, v_slot_1625_, v_next_1626_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___boxed(lean_object* v_m_1629_, lean_object* v_00_u03b1_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_slot_1633_, lean_object* v_next_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue(v_m_1629_, v_00_u03b1_1630_, v_inst_1631_, v_inst_1632_, v_slot_1633_, v_next_1634_, v_a_1635_);
lean_dec(v_a_1635_);
lean_dec_ref(v_inst_1631_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0(lean_object* v_toApplicative_1637_, lean_object* v_fst_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v_toPure_1640_; lean_object* v___x_1641_; 
v_toPure_1640_ = lean_ctor_get(v_toApplicative_1637_, 1);
lean_inc(v_toPure_1640_);
lean_dec_ref(v_toApplicative_1637_);
v___x_1641_ = lean_apply_2(v_toPure_1640_, lean_box(0), v_fst_1638_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(lean_object* v_inst_1642_, lean_object* v_toBind_1643_, lean_object* v___f_1644_, lean_object* v_____r_1645_, lean_object* v_st_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
lean_inc(v___y_1647_);
v___x_1648_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_set___boxed), 5, 4);
lean_closure_set(v___x_1648_, 0, lean_box(0));
lean_closure_set(v___x_1648_, 1, lean_box(0));
lean_closure_set(v___x_1648_, 2, v___y_1647_);
lean_closure_set(v___x_1648_, 3, v_st_1646_);
v___x_1649_ = lean_apply_2(v_inst_1642_, lean_box(0), v___x_1648_);
v___x_1650_ = lean_apply_4(v_toBind_1643_, lean_box(0), lean_box(0), v___x_1649_, v___f_1644_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed(lean_object* v_inst_1651_, lean_object* v_toBind_1652_, lean_object* v___f_1653_, lean_object* v_____r_1654_, lean_object* v_st_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1651_, v_toBind_1652_, v___f_1653_, v_____r_1654_, v_st_1655_, v___y_1656_);
lean_dec(v___y_1656_);
return v_res_1657_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(lean_object* v_snd_1658_, lean_object* v_waiters_1659_, lean_object* v_capacity_1660_, lean_object* v_size_1661_, lean_object* v_buffer_1662_, lean_object* v_write_1663_, lean_object* v_read_1664_, lean_object* v_receivers_1665_, lean_object* v_nextId_1666_, uint8_t v_closed_1667_, lean_object* v_pos_1668_, lean_object* v___f_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_1672_, 0, v_snd_1658_);
lean_ctor_set(v___x_1672_, 1, v_waiters_1659_);
lean_ctor_set(v___x_1672_, 2, v_capacity_1660_);
lean_ctor_set(v___x_1672_, 3, v_size_1661_);
lean_ctor_set(v___x_1672_, 4, v_buffer_1662_);
lean_ctor_set(v___x_1672_, 5, v_write_1663_);
lean_ctor_set(v___x_1672_, 6, v_read_1664_);
lean_ctor_set(v___x_1672_, 7, v_receivers_1665_);
lean_ctor_set(v___x_1672_, 8, v_nextId_1666_);
lean_ctor_set(v___x_1672_, 9, v_pos_1668_);
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*10, v_closed_1667_);
v___x_1673_ = lean_box(0);
lean_inc(v_a_1670_);
v___x_1674_ = lean_apply_3(v___f_1669_, v___x_1673_, v___x_1672_, v_a_1670_);
return v___x_1674_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_1658_ = stack[0].m_obj;
lean_object* v_waiters_1659_ = stack[1].m_obj;
lean_object* v_capacity_1660_ = stack[2].m_obj;
lean_object* v_size_1661_ = stack[3].m_obj;
lean_object* v_buffer_1662_ = stack[4].m_obj;
lean_object* v_write_1663_ = stack[5].m_obj;
lean_object* v_read_1664_ = stack[6].m_obj;
lean_object* v_receivers_1665_ = stack[7].m_obj;
lean_object* v_nextId_1666_ = stack[8].m_obj;
uint8_t v_closed_1667_ = stack[9].m_num;
lean_object* v_pos_1668_ = stack[10].m_obj;
lean_object* v___f_1669_ = stack[11].m_obj;
lean_object* v_a_1670_ = stack[12].m_obj;
lean_object* v_a_1671_ = stack[13].m_obj;
lean_object* v_res_1675_;
v_res_1675_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(v_snd_1658_, v_waiters_1659_, v_capacity_1660_, v_size_1661_, v_buffer_1662_, v_write_1663_, v_read_1664_, v_receivers_1665_, v_nextId_1666_, v_closed_1667_, v_pos_1668_, v___f_1669_, v_a_1670_, v_a_1671_);
stack->m_obj
 = v_res_1675_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed(lean_object* v_snd_1676_, lean_object* v_waiters_1677_, lean_object* v_capacity_1678_, lean_object* v_size_1679_, lean_object* v_buffer_1680_, lean_object* v_write_1681_, lean_object* v_read_1682_, lean_object* v_receivers_1683_, lean_object* v_nextId_1684_, lean_object* v_closed_1685_, lean_object* v_pos_1686_, lean_object* v___f_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
uint8_t v_closed_boxed_1690_; lean_object* v_res_1691_; 
v_closed_boxed_1690_ = lean_unbox(v_closed_1685_);
v_res_1691_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2(v_snd_1676_, v_waiters_1677_, v_capacity_1678_, v_size_1679_, v_buffer_1680_, v_write_1681_, v_read_1682_, v_receivers_1683_, v_nextId_1684_, v_closed_boxed_1690_, v_pos_1686_, v___f_1687_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1688_);
return v_res_1691_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(lean_object* v_toApplicative_1692_, lean_object* v_inst_1693_, lean_object* v_toBind_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, uint8_t v___x_1697_, lean_object* v_inst_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_fst_1700_; 
v_fst_1700_ = lean_ctor_get(v_a_1699_, 0);
lean_inc(v_fst_1700_);
if (lean_obj_tag(v_fst_1700_) == 1)
{
lean_object* v_snd_1701_; lean_object* v___f_1702_; lean_object* v___f_1703_; uint8_t v___x_1704_; 
v_snd_1701_ = lean_ctor_get(v_a_1699_, 1);
lean_inc(v_snd_1701_);
lean_dec_ref(v_a_1699_);
v___f_1702_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1702_, 0, v_toApplicative_1692_);
lean_closure_set(v___f_1702_, 1, v_fst_1700_);
lean_inc_ref(v___f_1702_);
lean_inc(v_toBind_1694_);
lean_inc(v_inst_1693_);
v___f_1703_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1703_, 0, v_inst_1693_);
lean_closure_set(v___f_1703_, 1, v_toBind_1694_);
lean_closure_set(v___f_1703_, 2, v___f_1702_);
v___x_1704_ = lean_unbox(v_snd_1701_);
lean_dec(v_snd_1701_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_dec_ref(v___f_1703_);
lean_dec(v_inst_1698_);
v___x_1705_ = lean_box(0);
v___x_1706_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1693_, v_toBind_1694_, v___f_1702_, v___x_1705_, v_a_1695_, v_a_1696_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v_producers_1708_; lean_object* v_waiters_1709_; lean_object* v_capacity_1710_; lean_object* v_size_1711_; lean_object* v_buffer_1712_; lean_object* v_write_1713_; lean_object* v_read_1714_; lean_object* v_receivers_1715_; lean_object* v_nextId_1716_; uint8_t v_closed_1717_; lean_object* v_pos_1718_; lean_object* v___x_1719_; 
v___x_1707_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_1695_);
v_producers_1708_ = lean_ctor_get(v___x_1707_, 0);
v_waiters_1709_ = lean_ctor_get(v___x_1707_, 1);
v_capacity_1710_ = lean_ctor_get(v___x_1707_, 2);
v_size_1711_ = lean_ctor_get(v___x_1707_, 3);
v_buffer_1712_ = lean_ctor_get(v___x_1707_, 4);
v_write_1713_ = lean_ctor_get(v___x_1707_, 5);
v_read_1714_ = lean_ctor_get(v___x_1707_, 6);
v_receivers_1715_ = lean_ctor_get(v___x_1707_, 7);
v_nextId_1716_ = lean_ctor_get(v___x_1707_, 8);
v_closed_1717_ = lean_ctor_get_uint8(v___x_1707_, sizeof(void*)*10);
v_pos_1718_ = lean_ctor_get(v___x_1707_, 9);
lean_inc_ref(v_producers_1708_);
v___x_1719_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1708_);
if (lean_obj_tag(v___x_1719_) == 1)
{
lean_object* v_val_1720_; lean_object* v_fst_1721_; lean_object* v_snd_1722_; lean_object* v___x_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
lean_inc(v_pos_1718_);
lean_inc(v_nextId_1716_);
lean_inc(v_receivers_1715_);
lean_inc(v_read_1714_);
lean_inc(v_write_1713_);
lean_inc_ref(v_buffer_1712_);
lean_inc(v_size_1711_);
lean_inc(v_capacity_1710_);
lean_inc_ref(v_waiters_1709_);
lean_dec_ref(v___x_1707_);
lean_dec_ref(v___f_1702_);
lean_dec(v_inst_1693_);
v_val_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_val_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v_fst_1721_ = lean_ctor_get(v_val_1720_, 0);
lean_inc(v_fst_1721_);
v_snd_1722_ = lean_ctor_get(v_val_1720_, 1);
lean_inc(v_snd_1722_);
lean_dec(v_val_1720_);
v___x_1723_ = lean_box(v_closed_1717_);
lean_inc(v_a_1696_);
v___f_1724_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_1724_, 0, v_snd_1722_);
lean_closure_set(v___f_1724_, 1, v_waiters_1709_);
lean_closure_set(v___f_1724_, 2, v_capacity_1710_);
lean_closure_set(v___f_1724_, 3, v_size_1711_);
lean_closure_set(v___f_1724_, 4, v_buffer_1712_);
lean_closure_set(v___f_1724_, 5, v_write_1713_);
lean_closure_set(v___f_1724_, 6, v_read_1714_);
lean_closure_set(v___f_1724_, 7, v_receivers_1715_);
lean_closure_set(v___f_1724_, 8, v_nextId_1716_);
lean_closure_set(v___f_1724_, 9, v___x_1723_);
lean_closure_set(v___f_1724_, 10, v_pos_1718_);
lean_closure_set(v___f_1724_, 11, v___f_1703_);
lean_closure_set(v___f_1724_, 12, v_a_1696_);
v___x_1725_ = lean_box(v___x_1697_);
v___x_1726_ = lean_alloc_closure((void*)(l_IO_Promise_resolve___boxed), 4, 3);
lean_closure_set(v___x_1726_, 0, lean_box(0));
lean_closure_set(v___x_1726_, 1, v___x_1725_);
lean_closure_set(v___x_1726_, 2, v_fst_1721_);
v___x_1727_ = lean_apply_2(v_inst_1698_, lean_box(0), v___x_1726_);
v___x_1728_ = lean_apply_4(v_toBind_1694_, lean_box(0), lean_box(0), v___x_1727_, v___f_1724_);
return v___x_1728_;
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec(v___x_1719_);
lean_dec_ref(v___f_1703_);
lean_dec(v_inst_1698_);
v___x_1729_ = lean_box(0);
v___x_1730_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__1(v_inst_1693_, v_toBind_1694_, v___f_1702_, v___x_1729_, v___x_1707_, v_a_1696_);
return v___x_1730_;
}
}
}
else
{
lean_object* v_toPure_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_fst_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_inst_1698_);
lean_dec_ref(v_a_1695_);
lean_dec(v_toBind_1694_);
lean_dec(v_inst_1693_);
v_toPure_1731_ = lean_ctor_get(v_toApplicative_1692_, 1);
lean_inc(v_toPure_1731_);
lean_dec_ref(v_toApplicative_1692_);
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_apply_2(v_toPure_1731_, lean_box(0), v___x_1732_);
return v___x_1733_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_1692_ = stack[0].m_obj;
lean_object* v_inst_1693_ = stack[1].m_obj;
lean_object* v_toBind_1694_ = stack[2].m_obj;
lean_object* v_a_1695_ = stack[3].m_obj;
lean_object* v_a_1696_ = stack[4].m_obj;
uint8_t v___x_1697_ = stack[5].m_num;
lean_object* v_inst_1698_ = stack[6].m_obj;
lean_object* v_a_1699_ = stack[7].m_obj;
lean_object* v_res_1734_;
v_res_1734_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1692_, v_inst_1693_, v_toBind_1694_, v_a_1695_, v_a_1696_, v___x_1697_, v_inst_1698_, v_a_1699_);
stack->m_obj
 = v_res_1734_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed(lean_object* v_toApplicative_1735_, lean_object* v_inst_1736_, lean_object* v_toBind_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v___x_1740_, lean_object* v_inst_1741_, lean_object* v_a_1742_){
_start:
{
uint8_t v___x_809__boxed_1743_; lean_object* v_res_1744_; 
v___x_809__boxed_1743_ = lean_unbox(v___x_1740_);
v_res_1744_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3(v_toApplicative_1735_, v_inst_1736_, v_toBind_1737_, v_a_1738_, v_a_1739_, v___x_809__boxed_1743_, v_inst_1741_, v_a_1742_);
lean_dec(v_a_1739_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4(lean_object* v_inst_1745_, lean_object* v_next_1746_, lean_object* v_toBind_1747_, lean_object* v___f_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___redArg(v_inst_1745_, v_a_1749_, v_next_1746_);
v___x_1751_ = lean_apply_4(v_toBind_1747_, lean_box(0), lean_box(0), v___x_1750_, v___f_1748_);
return v___x_1751_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(lean_object* v_a_1752_, lean_object* v_toApplicative_1753_, lean_object* v_inst_1754_, lean_object* v_toBind_1755_, lean_object* v_a_1756_, lean_object* v_inst_1757_, lean_object* v_next_1758_, lean_object* v_inst_1759_, uint8_t v_a_1760_){
_start:
{
if (v_a_1760_ == 0)
{
lean_object* v_capacity_1761_; uint8_t v___x_1762_; lean_object* v___x_1763_; lean_object* v___f_1764_; lean_object* v___f_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v_capacity_1761_ = lean_ctor_get(v_a_1752_, 2);
lean_inc(v_capacity_1761_);
v___x_1762_ = 1;
v___x_1763_ = lean_box(v___x_1762_);
lean_inc(v_a_1756_);
lean_inc_n(v_toBind_1755_, 2);
lean_inc_n(v_inst_1754_, 2);
v___f_1764_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_1764_, 0, v_toApplicative_1753_);
lean_closure_set(v___f_1764_, 1, v_inst_1754_);
lean_closure_set(v___f_1764_, 2, v_toBind_1755_);
lean_closure_set(v___f_1764_, 3, v_a_1752_);
lean_closure_set(v___f_1764_, 4, v_a_1756_);
lean_closure_set(v___f_1764_, 5, v___x_1763_);
lean_closure_set(v___f_1764_, 6, v_inst_1757_);
lean_inc(v_next_1758_);
v___f_1765_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__4), 5, 4);
lean_closure_set(v___f_1765_, 0, v_inst_1754_);
lean_closure_set(v___f_1765_, 1, v_next_1758_);
lean_closure_set(v___f_1765_, 2, v_toBind_1755_);
lean_closure_set(v___f_1765_, 3, v___f_1764_);
v___x_1766_ = lean_nat_mod(v_next_1758_, v_capacity_1761_);
lean_dec(v_capacity_1761_);
lean_dec(v_next_1758_);
v___x_1767_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_1759_, v_inst_1754_, v___x_1766_, v_a_1756_);
v___x_1768_ = lean_apply_4(v_toBind_1755_, lean_box(0), lean_box(0), v___x_1767_, v___f_1765_);
return v___x_1768_;
}
else
{
lean_object* v_toPure_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec_ref(v_inst_1759_);
lean_dec(v_next_1758_);
lean_dec(v_inst_1757_);
lean_dec(v_toBind_1755_);
lean_dec(v_inst_1754_);
lean_dec_ref(v_a_1752_);
v_toPure_1769_ = lean_ctor_get(v_toApplicative_1753_, 1);
lean_inc(v_toPure_1769_);
lean_dec_ref(v_toApplicative_1753_);
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_apply_2(v_toPure_1769_, lean_box(0), v___x_1770_);
return v___x_1771_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1752_ = stack[0].m_obj;
lean_object* v_toApplicative_1753_ = stack[1].m_obj;
lean_object* v_inst_1754_ = stack[2].m_obj;
lean_object* v_toBind_1755_ = stack[3].m_obj;
lean_object* v_a_1756_ = stack[4].m_obj;
lean_object* v_inst_1757_ = stack[5].m_obj;
lean_object* v_next_1758_ = stack[6].m_obj;
lean_object* v_inst_1759_ = stack[7].m_obj;
uint8_t v_a_1760_ = stack[8].m_num;
lean_object* v_res_1772_;
v_res_1772_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(v_a_1752_, v_toApplicative_1753_, v_inst_1754_, v_toBind_1755_, v_a_1756_, v_inst_1757_, v_next_1758_, v_inst_1759_, v_a_1760_);
stack->m_obj
 = v_res_1772_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed(lean_object* v_a_1773_, lean_object* v_toApplicative_1774_, lean_object* v_inst_1775_, lean_object* v_toBind_1776_, lean_object* v_a_1777_, lean_object* v_inst_1778_, lean_object* v_next_1779_, lean_object* v_inst_1780_, lean_object* v_a_1781_){
_start:
{
uint8_t v_a_boxed_1782_; lean_object* v_res_1783_; 
v_a_boxed_1782_ = lean_unbox(v_a_1781_);
v_res_1783_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5(v_a_1773_, v_toApplicative_1774_, v_inst_1775_, v_toBind_1776_, v_a_1777_, v_inst_1778_, v_next_1779_, v_inst_1780_, v_a_boxed_1782_);
lean_dec(v_a_1777_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(lean_object* v_toApplicative_1784_, lean_object* v_inst_1785_, lean_object* v_toBind_1786_, lean_object* v_a_1787_, lean_object* v_inst_1788_, lean_object* v_next_1789_, lean_object* v_inst_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v___f_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
lean_inc_ref(v_inst_1790_);
lean_inc(v_a_1787_);
lean_inc(v_toBind_1786_);
lean_inc(v_inst_1785_);
v___f_1792_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_1792_, 0, v_a_1791_);
lean_closure_set(v___f_1792_, 1, v_toApplicative_1784_);
lean_closure_set(v___f_1792_, 2, v_inst_1785_);
lean_closure_set(v___f_1792_, 3, v_toBind_1786_);
lean_closure_set(v___f_1792_, 4, v_a_1787_);
lean_closure_set(v___f_1792_, 5, v_inst_1788_);
lean_closure_set(v___f_1792_, 6, v_next_1789_);
lean_closure_set(v___f_1792_, 7, v_inst_1790_);
v___x_1793_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___redArg(v_inst_1790_, v_inst_1785_, v_a_1787_);
v___x_1794_ = lean_apply_4(v_toBind_1786_, lean_box(0), lean_box(0), v___x_1793_, v___f_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed(lean_object* v_toApplicative_1795_, lean_object* v_inst_1796_, lean_object* v_toBind_1797_, lean_object* v_a_1798_, lean_object* v_inst_1799_, lean_object* v_next_1800_, lean_object* v_inst_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6(v_toApplicative_1795_, v_inst_1796_, v_toBind_1797_, v_a_1798_, v_inst_1799_, v_next_1800_, v_inst_1801_, v_a_1802_);
lean_dec(v_a_1798_);
return v_res_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(lean_object* v_inst_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_next_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_toApplicative_1809_; lean_object* v_toBind_1810_; lean_object* v___f_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v_toApplicative_1809_ = lean_ctor_get(v_inst_1804_, 0);
lean_inc_ref(v_toApplicative_1809_);
v_toBind_1810_ = lean_ctor_get(v_inst_1804_, 1);
lean_inc_n(v_toBind_1810_, 2);
lean_inc_n(v_a_1808_, 2);
lean_inc(v_inst_1805_);
v___f_1811_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___lam__6___boxed), 8, 7);
lean_closure_set(v___f_1811_, 0, v_toApplicative_1809_);
lean_closure_set(v___f_1811_, 1, v_inst_1805_);
lean_closure_set(v___f_1811_, 2, v_toBind_1810_);
lean_closure_set(v___f_1811_, 3, v_a_1808_);
lean_closure_set(v___f_1811_, 4, v_inst_1806_);
lean_closure_set(v___f_1811_, 5, v_next_1807_);
lean_closure_set(v___f_1811_, 6, v_inst_1804_);
v___x_1812_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1812_, 0, lean_box(0));
lean_closure_set(v___x_1812_, 1, lean_box(0));
lean_closure_set(v___x_1812_, 2, v_a_1808_);
v___x_1813_ = lean_apply_2(v_inst_1805_, lean_box(0), v___x_1812_);
v___x_1814_ = lean_apply_4(v_toBind_1810_, lean_box(0), lean_box(0), v___x_1813_, v___f_1811_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg___boxed(lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_next_1818_, lean_object* v_a_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1815_, v_inst_1816_, v_inst_1817_, v_next_1818_, v_a_1819_);
lean_dec(v_a_1819_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(lean_object* v_m_1821_, lean_object* v_00_u03b1_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_next_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_1823_, v_inst_1824_, v_inst_1825_, v_next_1826_, v_a_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___boxed(lean_object* v_m_1829_, lean_object* v_00_u03b1_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_next_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition(v_m_1829_, v_00_u03b1_1830_, v_inst_1831_, v_inst_1832_, v_inst_1833_, v_next_1834_, v_a_1835_);
lean_dec(v_a_1835_);
return v_res_1836_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(lean_object* v_place_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___x_1840_; lean_object* v_capacity_1841_; lean_object* v_buffer_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1840_ = lean_st_ref_get(v_a_1838_);
v_capacity_1841_ = lean_ctor_get(v___x_1840_, 2);
lean_inc(v_capacity_1841_);
v_buffer_1842_ = lean_ctor_get(v___x_1840_, 4);
lean_inc_ref(v_buffer_1842_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_nat_mod(v_place_1837_, v_capacity_1841_);
lean_dec(v_capacity_1841_);
v___x_1844_ = lean_array_fget(v_buffer_1842_, v___x_1843_);
lean_dec(v___x_1843_);
lean_dec_ref(v_buffer_1842_);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_place_1837_ = stack[0].m_obj;
lean_object* v_a_1838_ = stack[1].m_obj;
lean_object* v_res_1846_;
v_res_1846_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_1837_, v_a_1838_);
stack->m_obj
 = v_res_1846_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg___boxed(lean_object* v_place_1847_, lean_object* v_a_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_1847_, v_a_1848_);
lean_dec(v_a_1848_);
lean_dec(v_place_1847_);
return v_res_1850_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(lean_object* v_a_1851_){
_start:
{
lean_object* v___x_1853_; lean_object* v_size_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1853_ = lean_st_ref_get(v_a_1851_);
v_size_1854_ = lean_ctor_get(v___x_1853_, 3);
lean_inc(v_size_1854_);
lean_dec(v___x_1853_);
v___x_1855_ = lean_unsigned_to_nat(0u);
v___x_1856_ = lean_nat_dec_eq(v_size_1854_, v___x_1855_);
lean_dec(v_size_1854_);
v___x_1857_ = lean_box(v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1851_ = stack[0].m_obj;
lean_object* v_res_1859_;
v_res_1859_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1851_);
stack->m_obj
 = v_res_1859_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg___boxed(lean_object* v_a_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1860_);
lean_dec(v_a_1860_);
return v_res_1862_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(lean_object* v_slot_1863_, lean_object* v_next_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v_fst_1868_; lean_object* v_snd_1869_; lean_object* v_value_1872_; lean_object* v_pos_1873_; lean_object* v_remaining_1874_; uint8_t v___x_1875_; 
v___x_1866_ = lean_st_ref_take(v_slot_1863_);
v_value_1872_ = lean_ctor_get(v___x_1866_, 0);
v_pos_1873_ = lean_ctor_get(v___x_1866_, 1);
v_remaining_1874_ = lean_ctor_get(v___x_1866_, 2);
v___x_1875_ = lean_nat_dec_eq(v_next_1864_, v_pos_1873_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_box(0);
v___x_1877_ = lean_box(v___x_1875_);
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v_fst_1868_ = v___x_1878_;
v_snd_1869_ = v___x_1866_;
goto v___jp_1867_;
}
else
{
lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1897_; 
lean_inc(v_remaining_1874_);
lean_inc(v_pos_1873_);
lean_inc(v_value_1872_);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; lean_object* v_unused_1899_; lean_object* v_unused_1900_; 
v_unused_1898_ = lean_ctor_get(v___x_1866_, 2);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v___x_1866_, 1);
lean_dec(v_unused_1899_);
v_unused_1900_ = lean_ctor_get(v___x_1866_, 0);
lean_dec(v_unused_1900_);
v___x_1880_ = v___x_1866_;
v_isShared_1881_ = v_isSharedCheck_1897_;
goto v_resetjp_1879_;
}
else
{
lean_dec(v___x_1866_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1897_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = lean_unsigned_to_nat(1u);
v___x_1883_ = lean_nat_dec_eq(v_remaining_1874_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1884_ = lean_box(v___x_1883_);
lean_inc(v_value_1872_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_value_1872_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = lean_nat_sub(v_remaining_1874_, v___x_1882_);
lean_dec(v_remaining_1874_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 2, v___x_1886_);
v___x_1888_ = v___x_1880_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_value_1872_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_pos_1873_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
v_fst_1868_ = v___x_1885_;
v_snd_1869_ = v___x_1888_;
goto v___jp_1867_;
}
}
else
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_dec(v_remaining_1874_);
v___x_1890_ = lean_box(v___x_1875_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v_value_1872_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_unsigned_to_nat(0u);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 2, v___x_1893_);
lean_ctor_set(v___x_1880_, 0, v___x_1892_);
v___x_1895_ = v___x_1880_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_pos_1873_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
v_fst_1868_ = v___x_1891_;
v_snd_1869_ = v___x_1895_;
goto v___jp_1867_;
}
}
}
}
v___jp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_st_ref_put(v_slot_1863_, v_snd_1869_);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_fst_1868_);
return v___x_1871_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_slot_1863_ = stack[0].m_obj;
lean_object* v_next_1864_ = stack[1].m_obj;
lean_object* v_res_1901_;
v_res_1901_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_1863_, v_next_1864_);
stack->m_obj
 = v_res_1901_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg___boxed(lean_object* v_slot_1902_, lean_object* v_next_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_1902_, v_next_1903_);
lean_dec(v_next_1903_);
lean_dec(v_slot_1902_);
return v_res_1905_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(lean_object* v_next_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1984_; 
v___x_1909_ = lean_st_ref_get(v_a_1907_);
v___x_1910_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_1907_);
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1984_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1984_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
uint8_t v___x_1915_; 
v___x_1915_ = lean_unbox(v_a_1911_);
lean_dec(v_a_1911_);
if (v___x_1915_ == 0)
{
lean_object* v_capacity_1916_; uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1979_; 
lean_del_object(v___x_1913_);
v_capacity_1916_ = lean_ctor_get(v___x_1909_, 2);
v___x_1917_ = 1;
v___x_1918_ = lean_nat_mod(v_next_1906_, v_capacity_1916_);
v___x_1919_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_1918_, v_a_1907_);
lean_dec(v___x_1918_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1979_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1979_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1924_; lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1978_; 
v___x_1924_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_a_1920_, v_next_1906_);
lean_dec(v_a_1920_);
v_a_1925_ = lean_ctor_get(v___x_1924_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1927_ = v___x_1924_;
v_isShared_1928_ = v_isSharedCheck_1978_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1924_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1978_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v_st_1932_; lean_object* v___y_1933_; 
v_fst_1929_ = lean_ctor_get(v_a_1925_, 0);
lean_inc(v_fst_1929_);
v_snd_1930_ = lean_ctor_get(v_a_1925_, 1);
lean_inc(v_snd_1930_);
lean_dec(v_a_1925_);
if (lean_obj_tag(v_fst_1929_) == 1)
{
uint8_t v___x_1938_; 
lean_del_object(v___x_1922_);
v___x_1938_ = lean_unbox(v_snd_1930_);
lean_dec(v_snd_1930_);
if (v___x_1938_ == 0)
{
v_st_1932_ = v___x_1909_;
v___y_1933_ = v_a_1907_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1939_; lean_object* v_producers_1940_; lean_object* v_waiters_1941_; lean_object* v_capacity_1942_; lean_object* v_size_1943_; lean_object* v_buffer_1944_; lean_object* v_write_1945_; lean_object* v_read_1946_; lean_object* v_receivers_1947_; lean_object* v_nextId_1948_; uint8_t v_closed_1949_; lean_object* v_pos_1950_; lean_object* v___x_1951_; 
v___x_1939_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_1909_);
v_producers_1940_ = lean_ctor_get(v___x_1939_, 0);
v_waiters_1941_ = lean_ctor_get(v___x_1939_, 1);
v_capacity_1942_ = lean_ctor_get(v___x_1939_, 2);
v_size_1943_ = lean_ctor_get(v___x_1939_, 3);
v_buffer_1944_ = lean_ctor_get(v___x_1939_, 4);
v_write_1945_ = lean_ctor_get(v___x_1939_, 5);
v_read_1946_ = lean_ctor_get(v___x_1939_, 6);
v_receivers_1947_ = lean_ctor_get(v___x_1939_, 7);
v_nextId_1948_ = lean_ctor_get(v___x_1939_, 8);
v_closed_1949_ = lean_ctor_get_uint8(v___x_1939_, sizeof(void*)*10);
v_pos_1950_ = lean_ctor_get(v___x_1939_, 9);
lean_inc_ref(v_producers_1940_);
v___x_1951_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_1940_);
if (lean_obj_tag(v___x_1951_) == 1)
{
lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1963_; 
lean_inc(v_pos_1950_);
lean_inc(v_nextId_1948_);
lean_inc(v_receivers_1947_);
lean_inc(v_read_1946_);
lean_inc(v_write_1945_);
lean_inc_ref(v_buffer_1944_);
lean_inc(v_size_1943_);
lean_inc(v_capacity_1942_);
lean_inc_ref(v_waiters_1941_);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1963_ == 0)
{
lean_object* v_unused_1964_; lean_object* v_unused_1965_; lean_object* v_unused_1966_; lean_object* v_unused_1967_; lean_object* v_unused_1968_; lean_object* v_unused_1969_; lean_object* v_unused_1970_; lean_object* v_unused_1971_; lean_object* v_unused_1972_; lean_object* v_unused_1973_; 
v_unused_1964_ = lean_ctor_get(v___x_1939_, 9);
lean_dec(v_unused_1964_);
v_unused_1965_ = lean_ctor_get(v___x_1939_, 8);
lean_dec(v_unused_1965_);
v_unused_1966_ = lean_ctor_get(v___x_1939_, 7);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v___x_1939_, 6);
lean_dec(v_unused_1967_);
v_unused_1968_ = lean_ctor_get(v___x_1939_, 5);
lean_dec(v_unused_1968_);
v_unused_1969_ = lean_ctor_get(v___x_1939_, 4);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v___x_1939_, 3);
lean_dec(v_unused_1970_);
v_unused_1971_ = lean_ctor_get(v___x_1939_, 2);
lean_dec(v_unused_1971_);
v_unused_1972_ = lean_ctor_get(v___x_1939_, 1);
lean_dec(v_unused_1972_);
v_unused_1973_ = lean_ctor_get(v___x_1939_, 0);
lean_dec(v_unused_1973_);
v___x_1953_ = v___x_1939_;
v_isShared_1954_ = v_isSharedCheck_1963_;
goto v_resetjp_1952_;
}
else
{
lean_dec(v___x_1939_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1963_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v_val_1955_; lean_object* v_fst_1956_; lean_object* v_snd_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v_val_1955_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v___x_1951_, 1);
v_fst_1956_ = lean_ctor_get(v_val_1955_, 0);
lean_inc(v_fst_1956_);
v_snd_1957_ = lean_ctor_get(v_val_1955_, 1);
lean_inc(v_snd_1957_);
lean_dec(v_val_1955_);
v___x_1958_ = lean_box(v___x_1917_);
v___x_1959_ = lean_io_promise_resolve(v___x_1958_, v_fst_1956_);
lean_dec(v_fst_1956_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v_snd_1957_);
v___x_1961_ = v___x_1953_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_snd_1957_);
lean_ctor_set(v_reuseFailAlloc_1962_, 1, v_waiters_1941_);
lean_ctor_set(v_reuseFailAlloc_1962_, 2, v_capacity_1942_);
lean_ctor_set(v_reuseFailAlloc_1962_, 3, v_size_1943_);
lean_ctor_set(v_reuseFailAlloc_1962_, 4, v_buffer_1944_);
lean_ctor_set(v_reuseFailAlloc_1962_, 5, v_write_1945_);
lean_ctor_set(v_reuseFailAlloc_1962_, 6, v_read_1946_);
lean_ctor_set(v_reuseFailAlloc_1962_, 7, v_receivers_1947_);
lean_ctor_set(v_reuseFailAlloc_1962_, 8, v_nextId_1948_);
lean_ctor_set(v_reuseFailAlloc_1962_, 9, v_pos_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1962_, sizeof(void*)*10, v_closed_1949_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
v_st_1932_ = v___x_1961_;
v___y_1933_ = v_a_1907_;
goto v___jp_1931_;
}
}
}
else
{
lean_dec(v___x_1951_);
v_st_1932_ = v___x_1939_;
v___y_1933_ = v_a_1907_;
goto v___jp_1931_;
}
}
}
else
{
lean_object* v___x_1974_; lean_object* v___x_1976_; 
lean_dec(v_snd_1930_);
lean_dec(v_fst_1929_);
lean_del_object(v___x_1927_);
lean_dec(v___x_1909_);
v___x_1974_ = lean_box(0);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1974_);
v___x_1976_ = v___x_1922_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
v___jp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1936_; 
v___x_1934_ = lean_st_ref_swap(v___y_1933_, v_st_1932_);
lean_dec(v___x_1934_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v_fst_1929_);
v___x_1936_ = v___x_1927_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_fst_1929_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
lean_dec(v___x_1909_);
v___x_1980_ = lean_box(0);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1980_);
v___x_1982_ = v___x_1913_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
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
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_next_1906_ = stack[0].m_obj;
lean_object* v_a_1907_ = stack[1].m_obj;
lean_object* v_res_1985_;
v_res_1985_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_1906_, v_a_1907_);
stack->m_obj
 = v_res_1985_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg___boxed(lean_object* v_next_1986_, lean_object* v_a_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_1986_, v_a_1987_);
lean_dec(v_a_1987_);
lean_dec(v_next_1986_);
return v_res_1989_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(lean_object* v_a_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_fst_1993_; lean_object* v_snd_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2031_; 
v_fst_1993_ = lean_ctor_get(v_a_1990_, 0);
v_snd_1994_ = lean_ctor_get(v_a_1990_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_a_1990_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1996_ = v_a_1990_;
v_isShared_1997_ = v_isSharedCheck_2031_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_snd_1994_);
lean_inc(v_fst_1993_);
lean_dec(v_a_1990_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2031_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_size_2003_; lean_object* v_pos_2004_; uint8_t v___x_2005_; 
v_size_2003_ = lean_ctor_get(v_fst_1993_, 3);
v_pos_2004_ = lean_ctor_get(v_fst_1993_, 9);
v___x_2005_ = lean_nat_dec_lt(v_snd_1994_, v_pos_2004_);
if (v___x_2005_ == 0)
{
goto v___jp_1998_;
}
else
{
lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = lean_unsigned_to_nat(0u);
v___x_2007_ = lean_nat_dec_lt(v___x_2006_, v_size_2003_);
if (v___x_2007_ == 0)
{
goto v___jp_1998_;
}
else
{
lean_object* v___x_2008_; 
lean_del_object(v___x_1996_);
v___x_2008_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_snd_1994_, v___y_1991_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2022_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2022_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2022_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
if (lean_obj_tag(v_a_2009_) == 1)
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_dec_ref_known(v_a_2009_, 1);
lean_del_object(v___x_2011_);
lean_dec(v_fst_1993_);
v___x_2013_ = lean_st_ref_get(v___y_1991_);
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = lean_nat_add(v_snd_1994_, v___x_2014_);
lean_dec(v_snd_1994_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2013_);
lean_ctor_set(v___x_2016_, 1, v___x_2015_);
v_a_1990_ = v___x_2016_;
goto _start;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2020_; 
lean_dec(v_a_2009_);
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v_fst_1993_);
lean_ctor_set(v___x_2018_, 1, v_snd_1994_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2018_);
v___x_2020_ = v___x_2011_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2018_);
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
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v_snd_1994_);
lean_dec(v_fst_1993_);
v_a_2023_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2008_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2008_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
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
v___jp_1998_:
{
lean_object* v___x_2000_; 
if (v_isShared_1997_ == 0)
{
v___x_2000_ = v___x_1996_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_fst_1993_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_snd_1994_);
v___x_2000_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1990_ = stack[0].m_obj;
lean_object* v___y_1991_ = stack[1].m_obj;
lean_object* v_res_2032_;
v_res_2032_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_1990_, v___y_1991_);
stack->m_obj
 = v_res_2032_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg___boxed(lean_object* v_a_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_2033_, v___y_2034_);
lean_dec(v___y_2034_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(lean_object* v_t_2037_, lean_object* v_k_2038_){
_start:
{
if (lean_obj_tag(v_t_2037_) == 0)
{
lean_object* v_k_2039_; lean_object* v_v_2040_; lean_object* v_l_2041_; lean_object* v_r_2042_; uint8_t v___x_2043_; 
v_k_2039_ = lean_ctor_get(v_t_2037_, 1);
v_v_2040_ = lean_ctor_get(v_t_2037_, 2);
v_l_2041_ = lean_ctor_get(v_t_2037_, 3);
v_r_2042_ = lean_ctor_get(v_t_2037_, 4);
v___x_2043_ = lean_nat_dec_lt(v_k_2038_, v_k_2039_);
if (v___x_2043_ == 0)
{
uint8_t v___x_2044_; 
v___x_2044_ = lean_nat_dec_eq(v_k_2038_, v_k_2039_);
if (v___x_2044_ == 0)
{
v_t_2037_ = v_r_2042_;
goto _start;
}
else
{
lean_object* v___x_2046_; 
lean_inc(v_v_2040_);
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_v_2040_);
return v___x_2046_;
}
}
else
{
v_t_2037_ = v_l_2041_;
goto _start;
}
}
else
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_box(0);
return v___x_2048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg___boxed(lean_object* v_t_2049_, lean_object* v_k_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_2049_, v_k_2050_);
lean_dec(v_k_2050_);
lean_dec(v_t_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(lean_object* v_k_2052_, lean_object* v_t_2053_){
_start:
{
if (lean_obj_tag(v_t_2053_) == 0)
{
lean_object* v_k_2054_; lean_object* v_v_2055_; lean_object* v_l_2056_; lean_object* v_r_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2712_; 
v_k_2054_ = lean_ctor_get(v_t_2053_, 1);
v_v_2055_ = lean_ctor_get(v_t_2053_, 2);
v_l_2056_ = lean_ctor_get(v_t_2053_, 3);
v_r_2057_ = lean_ctor_get(v_t_2053_, 4);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_t_2053_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; 
v_unused_2713_ = lean_ctor_get(v_t_2053_, 0);
lean_dec(v_unused_2713_);
v___x_2059_ = v_t_2053_;
v_isShared_2060_ = v_isSharedCheck_2712_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_r_2057_);
lean_inc(v_l_2056_);
lean_inc(v_v_2055_);
lean_inc(v_k_2054_);
lean_dec(v_t_2053_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2712_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
uint8_t v___x_2061_; 
v___x_2061_ = lean_nat_dec_lt(v_k_2052_, v_k_2054_);
if (v___x_2061_ == 0)
{
uint8_t v___x_2062_; 
v___x_2062_ = lean_nat_dec_eq(v_k_2052_, v_k_2054_);
if (v___x_2062_ == 0)
{
lean_object* v_impl_2063_; lean_object* v___x_2064_; 
v_impl_2063_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2052_, v_r_2057_);
v___x_2064_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2063_) == 0)
{
if (lean_obj_tag(v_l_2056_) == 0)
{
lean_object* v_size_2065_; lean_object* v_size_2066_; lean_object* v_k_2067_; lean_object* v_v_2068_; lean_object* v_l_2069_; lean_object* v_r_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_size_2065_ = lean_ctor_get(v_impl_2063_, 0);
v_size_2066_ = lean_ctor_get(v_l_2056_, 0);
v_k_2067_ = lean_ctor_get(v_l_2056_, 1);
v_v_2068_ = lean_ctor_get(v_l_2056_, 2);
v_l_2069_ = lean_ctor_get(v_l_2056_, 3);
v_r_2070_ = lean_ctor_get(v_l_2056_, 4);
lean_inc(v_r_2070_);
v___x_2071_ = lean_unsigned_to_nat(3u);
v___x_2072_ = lean_nat_mul(v___x_2071_, v_size_2065_);
v___x_2073_ = lean_nat_dec_lt(v___x_2072_, v_size_2066_);
lean_dec(v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; 
lean_dec(v_r_2070_);
v___x_2074_ = lean_nat_add(v___x_2064_, v_size_2066_);
v___x_2075_ = lean_nat_add(v___x_2074_, v_size_2065_);
lean_dec(v___x_2074_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_impl_2063_);
lean_ctor_set(v___x_2059_, 0, v___x_2075_);
v___x_2077_ = v___x_2059_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2078_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2078_, 3, v_l_2056_);
lean_ctor_set(v_reuseFailAlloc_2078_, 4, v_impl_2063_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
else
{
lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2144_; 
lean_inc(v_l_2069_);
lean_inc(v_v_2068_);
lean_inc(v_k_2067_);
lean_inc(v_size_2066_);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_l_2056_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; lean_object* v_unused_2146_; lean_object* v_unused_2147_; lean_object* v_unused_2148_; lean_object* v_unused_2149_; 
v_unused_2145_ = lean_ctor_get(v_l_2056_, 4);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_l_2056_, 3);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_l_2056_, 2);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_l_2056_, 1);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_l_2056_, 0);
lean_dec(v_unused_2149_);
v___x_2080_ = v_l_2056_;
v_isShared_2081_ = v_isSharedCheck_2144_;
goto v_resetjp_2079_;
}
else
{
lean_dec(v_l_2056_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2144_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v_size_2082_; lean_object* v_size_2083_; lean_object* v_k_2084_; lean_object* v_v_2085_; lean_object* v_l_2086_; lean_object* v_r_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; 
v_size_2082_ = lean_ctor_get(v_l_2069_, 0);
v_size_2083_ = lean_ctor_get(v_r_2070_, 0);
v_k_2084_ = lean_ctor_get(v_r_2070_, 1);
v_v_2085_ = lean_ctor_get(v_r_2070_, 2);
v_l_2086_ = lean_ctor_get(v_r_2070_, 3);
v_r_2087_ = lean_ctor_get(v_r_2070_, 4);
v___x_2088_ = lean_unsigned_to_nat(2u);
v___x_2089_ = lean_nat_mul(v___x_2088_, v_size_2082_);
v___x_2090_ = lean_nat_dec_lt(v_size_2083_, v___x_2089_);
lean_dec(v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2119_; 
lean_inc(v_r_2087_);
lean_inc(v_l_2086_);
lean_inc(v_v_2085_);
lean_inc(v_k_2084_);
v_isSharedCheck_2119_ = !lean_is_exclusive(v_r_2070_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; lean_object* v_unused_2121_; lean_object* v_unused_2122_; lean_object* v_unused_2123_; lean_object* v_unused_2124_; 
v_unused_2120_ = lean_ctor_get(v_r_2070_, 4);
lean_dec(v_unused_2120_);
v_unused_2121_ = lean_ctor_get(v_r_2070_, 3);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v_r_2070_, 2);
lean_dec(v_unused_2122_);
v_unused_2123_ = lean_ctor_get(v_r_2070_, 1);
lean_dec(v_unused_2123_);
v_unused_2124_ = lean_ctor_get(v_r_2070_, 0);
lean_dec(v_unused_2124_);
v___x_2092_ = v_r_2070_;
v_isShared_2093_ = v_isSharedCheck_2119_;
goto v_resetjp_2091_;
}
else
{
lean_dec(v_r_2070_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2119_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___x_2107_; lean_object* v___y_2109_; 
v___x_2094_ = lean_nat_add(v___x_2064_, v_size_2066_);
lean_dec(v_size_2066_);
v___x_2095_ = lean_nat_add(v___x_2094_, v_size_2065_);
lean_dec(v___x_2094_);
v___x_2107_ = lean_nat_add(v___x_2064_, v_size_2082_);
if (lean_obj_tag(v_l_2086_) == 0)
{
lean_object* v_size_2117_; 
v_size_2117_ = lean_ctor_get(v_l_2086_, 0);
lean_inc(v_size_2117_);
v___y_2109_ = v_size_2117_;
goto v___jp_2108_;
}
else
{
lean_object* v___x_2118_; 
v___x_2118_ = lean_unsigned_to_nat(0u);
v___y_2109_ = v___x_2118_;
goto v___jp_2108_;
}
v___jp_2096_:
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2100_ = lean_nat_add(v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec(v___y_2098_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 4, v_impl_2063_);
lean_ctor_set(v___x_2092_, 3, v_r_2087_);
lean_ctor_set(v___x_2092_, 2, v_v_2055_);
lean_ctor_set(v___x_2092_, 1, v_k_2054_);
lean_ctor_set(v___x_2092_, 0, v___x_2100_);
v___x_2102_ = v___x_2092_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2106_, 3, v_r_2087_);
lean_ctor_set(v_reuseFailAlloc_2106_, 4, v_impl_2063_);
v___x_2102_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2104_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 4, v___x_2102_);
lean_ctor_set(v___x_2080_, 3, v___y_2097_);
lean_ctor_set(v___x_2080_, 2, v_v_2085_);
lean_ctor_set(v___x_2080_, 1, v_k_2084_);
lean_ctor_set(v___x_2080_, 0, v___x_2095_);
v___x_2104_ = v___x_2080_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_k_2084_);
lean_ctor_set(v_reuseFailAlloc_2105_, 2, v_v_2085_);
lean_ctor_set(v_reuseFailAlloc_2105_, 3, v___y_2097_);
lean_ctor_set(v_reuseFailAlloc_2105_, 4, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
v___jp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2110_ = lean_nat_add(v___x_2107_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec(v___x_2107_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_l_2086_);
lean_ctor_set(v___x_2059_, 3, v_l_2069_);
lean_ctor_set(v___x_2059_, 2, v_v_2068_);
lean_ctor_set(v___x_2059_, 1, v_k_2067_);
lean_ctor_set(v___x_2059_, 0, v___x_2110_);
v___x_2112_ = v___x_2059_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2110_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2067_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2068_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_l_2069_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_l_2086_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_nat_add(v___x_2064_, v_size_2065_);
if (lean_obj_tag(v_r_2087_) == 0)
{
lean_object* v_size_2114_; 
v_size_2114_ = lean_ctor_get(v_r_2087_, 0);
lean_inc(v_size_2114_);
v___y_2097_ = v___x_2112_;
v___y_2098_ = v___x_2113_;
v___y_2099_ = v_size_2114_;
goto v___jp_2096_;
}
else
{
lean_object* v___x_2115_; 
v___x_2115_ = lean_unsigned_to_nat(0u);
v___y_2097_ = v___x_2112_;
v___y_2098_ = v___x_2113_;
v___y_2099_ = v___x_2115_;
goto v___jp_2096_;
}
}
}
}
}
else
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
lean_del_object(v___x_2059_);
v___x_2125_ = lean_nat_add(v___x_2064_, v_size_2066_);
lean_dec(v_size_2066_);
v___x_2126_ = lean_nat_add(v___x_2125_, v_size_2065_);
lean_dec(v___x_2125_);
v___x_2127_ = lean_nat_add(v___x_2064_, v_size_2065_);
v___x_2128_ = lean_nat_add(v___x_2127_, v_size_2083_);
lean_dec(v___x_2127_);
lean_inc_ref(v_impl_2063_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 4, v_impl_2063_);
lean_ctor_set(v___x_2080_, 3, v_r_2070_);
lean_ctor_set(v___x_2080_, 2, v_v_2055_);
lean_ctor_set(v___x_2080_, 1, v_k_2054_);
lean_ctor_set(v___x_2080_, 0, v___x_2128_);
v___x_2130_ = v___x_2080_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v_r_2070_);
lean_ctor_set(v_reuseFailAlloc_2143_, 4, v_impl_2063_);
v___x_2130_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_isSharedCheck_2137_ = !lean_is_exclusive(v_impl_2063_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; lean_object* v_unused_2139_; lean_object* v_unused_2140_; lean_object* v_unused_2141_; lean_object* v_unused_2142_; 
v_unused_2138_ = lean_ctor_get(v_impl_2063_, 4);
lean_dec(v_unused_2138_);
v_unused_2139_ = lean_ctor_get(v_impl_2063_, 3);
lean_dec(v_unused_2139_);
v_unused_2140_ = lean_ctor_get(v_impl_2063_, 2);
lean_dec(v_unused_2140_);
v_unused_2141_ = lean_ctor_get(v_impl_2063_, 1);
lean_dec(v_unused_2141_);
v_unused_2142_ = lean_ctor_get(v_impl_2063_, 0);
lean_dec(v_unused_2142_);
v___x_2132_ = v_impl_2063_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_dec(v_impl_2063_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 4, v___x_2130_);
lean_ctor_set(v___x_2132_, 3, v_l_2069_);
lean_ctor_set(v___x_2132_, 2, v_v_2068_);
lean_ctor_set(v___x_2132_, 1, v_k_2067_);
lean_ctor_set(v___x_2132_, 0, v___x_2126_);
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2126_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_k_2067_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_v_2068_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_l_2069_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v___x_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
v_size_2150_ = lean_ctor_get(v_impl_2063_, 0);
v___x_2151_ = lean_nat_add(v___x_2064_, v_size_2150_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_impl_2063_);
lean_ctor_set(v___x_2059_, 0, v___x_2151_);
v___x_2153_ = v___x_2059_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_l_2056_);
lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_impl_2063_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
else
{
if (lean_obj_tag(v_l_2056_) == 0)
{
lean_object* v_l_2155_; 
v_l_2155_ = lean_ctor_get(v_l_2056_, 3);
if (lean_obj_tag(v_l_2155_) == 0)
{
lean_object* v_r_2156_; 
lean_inc_ref(v_l_2155_);
v_r_2156_ = lean_ctor_get(v_l_2056_, 4);
lean_inc(v_r_2156_);
if (lean_obj_tag(v_r_2156_) == 0)
{
lean_object* v_size_2157_; lean_object* v_k_2158_; lean_object* v_v_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2172_; 
v_size_2157_ = lean_ctor_get(v_l_2056_, 0);
v_k_2158_ = lean_ctor_get(v_l_2056_, 1);
v_v_2159_ = lean_ctor_get(v_l_2056_, 2);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_l_2056_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; lean_object* v_unused_2174_; 
v_unused_2173_ = lean_ctor_get(v_l_2056_, 4);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_l_2056_, 3);
lean_dec(v_unused_2174_);
v___x_2161_ = v_l_2056_;
v_isShared_2162_ = v_isSharedCheck_2172_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_v_2159_);
lean_inc(v_k_2158_);
lean_inc(v_size_2157_);
lean_dec(v_l_2056_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2172_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_size_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
v_size_2163_ = lean_ctor_get(v_r_2156_, 0);
v___x_2164_ = lean_nat_add(v___x_2064_, v_size_2157_);
lean_dec(v_size_2157_);
v___x_2165_ = lean_nat_add(v___x_2064_, v_size_2163_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 4, v_impl_2063_);
lean_ctor_set(v___x_2161_, 3, v_r_2156_);
lean_ctor_set(v___x_2161_, 2, v_v_2055_);
lean_ctor_set(v___x_2161_, 1, v_k_2054_);
lean_ctor_set(v___x_2161_, 0, v___x_2165_);
v___x_2167_ = v___x_2161_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2171_, 3, v_r_2156_);
lean_ctor_set(v_reuseFailAlloc_2171_, 4, v_impl_2063_);
v___x_2167_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v___x_2167_);
lean_ctor_set(v___x_2059_, 3, v_l_2155_);
lean_ctor_set(v___x_2059_, 2, v_v_2159_);
lean_ctor_set(v___x_2059_, 1, v_k_2158_);
lean_ctor_set(v___x_2059_, 0, v___x_2164_);
v___x_2169_ = v___x_2059_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_k_2158_);
lean_ctor_set(v_reuseFailAlloc_2170_, 2, v_v_2159_);
lean_ctor_set(v_reuseFailAlloc_2170_, 3, v_l_2155_);
lean_ctor_set(v_reuseFailAlloc_2170_, 4, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_k_2175_; lean_object* v_v_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2187_; 
v_k_2175_ = lean_ctor_get(v_l_2056_, 1);
v_v_2176_ = lean_ctor_get(v_l_2056_, 2);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_l_2056_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; lean_object* v_unused_2189_; lean_object* v_unused_2190_; 
v_unused_2188_ = lean_ctor_get(v_l_2056_, 4);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_l_2056_, 3);
lean_dec(v_unused_2189_);
v_unused_2190_ = lean_ctor_get(v_l_2056_, 0);
lean_dec(v_unused_2190_);
v___x_2178_ = v_l_2056_;
v_isShared_2179_ = v_isSharedCheck_2187_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_v_2176_);
lean_inc(v_k_2175_);
lean_dec(v_l_2056_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2187_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2180_ = lean_unsigned_to_nat(3u);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 3, v_r_2156_);
lean_ctor_set(v___x_2178_, 2, v_v_2055_);
lean_ctor_set(v___x_2178_, 1, v_k_2054_);
lean_ctor_set(v___x_2178_, 0, v___x_2064_);
v___x_2182_ = v___x_2178_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_r_2156_);
lean_ctor_set(v_reuseFailAlloc_2186_, 4, v_r_2156_);
v___x_2182_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v___x_2182_);
lean_ctor_set(v___x_2059_, 3, v_l_2155_);
lean_ctor_set(v___x_2059_, 2, v_v_2176_);
lean_ctor_set(v___x_2059_, 1, v_k_2175_);
lean_ctor_set(v___x_2059_, 0, v___x_2180_);
v___x_2184_ = v___x_2059_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_l_2155_);
lean_ctor_set(v_reuseFailAlloc_2185_, 4, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
else
{
lean_object* v_r_2191_; 
v_r_2191_ = lean_ctor_get(v_l_2056_, 4);
lean_inc(v_r_2191_);
if (lean_obj_tag(v_r_2191_) == 0)
{
lean_object* v_k_2192_; lean_object* v_v_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2216_; 
lean_inc(v_l_2155_);
v_k_2192_ = lean_ctor_get(v_l_2056_, 1);
v_v_2193_ = lean_ctor_get(v_l_2056_, 2);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_l_2056_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; lean_object* v_unused_2218_; lean_object* v_unused_2219_; 
v_unused_2217_ = lean_ctor_get(v_l_2056_, 4);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_l_2056_, 3);
lean_dec(v_unused_2218_);
v_unused_2219_ = lean_ctor_get(v_l_2056_, 0);
lean_dec(v_unused_2219_);
v___x_2195_ = v_l_2056_;
v_isShared_2196_ = v_isSharedCheck_2216_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_v_2193_);
lean_inc(v_k_2192_);
lean_dec(v_l_2056_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2216_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v_k_2197_; lean_object* v_v_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2212_; 
v_k_2197_ = lean_ctor_get(v_r_2191_, 1);
v_v_2198_ = lean_ctor_get(v_r_2191_, 2);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_r_2191_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; 
v_unused_2213_ = lean_ctor_get(v_r_2191_, 4);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_r_2191_, 3);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_r_2191_, 0);
lean_dec(v_unused_2215_);
v___x_2200_ = v_r_2191_;
v_isShared_2201_ = v_isSharedCheck_2212_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_v_2198_);
lean_inc(v_k_2197_);
lean_dec(v_r_2191_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2212_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2202_ = lean_unsigned_to_nat(3u);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 4, v_l_2155_);
lean_ctor_set(v___x_2200_, 3, v_l_2155_);
lean_ctor_set(v___x_2200_, 2, v_v_2193_);
lean_ctor_set(v___x_2200_, 1, v_k_2192_);
lean_ctor_set(v___x_2200_, 0, v___x_2064_);
v___x_2204_ = v___x_2200_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_k_2192_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_v_2193_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_l_2155_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v_l_2155_);
v___x_2204_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2206_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 4, v_l_2155_);
lean_ctor_set(v___x_2195_, 2, v_v_2055_);
lean_ctor_set(v___x_2195_, 1, v_k_2054_);
lean_ctor_set(v___x_2195_, 0, v___x_2064_);
v___x_2206_ = v___x_2195_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_l_2155_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_l_2155_);
v___x_2206_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2208_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v___x_2206_);
lean_ctor_set(v___x_2059_, 3, v___x_2204_);
lean_ctor_set(v___x_2059_, 2, v_v_2198_);
lean_ctor_set(v___x_2059_, 1, v_k_2197_);
lean_ctor_set(v___x_2059_, 0, v___x_2202_);
v___x_2208_ = v___x_2059_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_k_2197_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_v_2198_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2222_; 
v___x_2220_ = lean_unsigned_to_nat(2u);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_r_2191_);
lean_ctor_set(v___x_2059_, 0, v___x_2220_);
v___x_2222_ = v___x_2059_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2220_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_l_2056_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_r_2191_);
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
else
{
lean_object* v___x_2225_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_l_2056_);
lean_ctor_set(v___x_2059_, 0, v___x_2064_);
v___x_2225_ = v___x_2059_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_l_2056_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_l_2056_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_del_object(v___x_2059_);
lean_dec(v_v_2055_);
lean_dec(v_k_2054_);
if (lean_obj_tag(v_l_2056_) == 0)
{
if (lean_obj_tag(v_r_2057_) == 0)
{
lean_object* v_size_2227_; lean_object* v_k_2228_; lean_object* v_v_2229_; lean_object* v_l_2230_; lean_object* v_r_2231_; lean_object* v_size_2232_; lean_object* v_k_2233_; lean_object* v_v_2234_; lean_object* v_l_2235_; lean_object* v_r_2236_; lean_object* v___x_2237_; uint8_t v___x_2238_; 
v_size_2227_ = lean_ctor_get(v_l_2056_, 0);
v_k_2228_ = lean_ctor_get(v_l_2056_, 1);
v_v_2229_ = lean_ctor_get(v_l_2056_, 2);
v_l_2230_ = lean_ctor_get(v_l_2056_, 3);
v_r_2231_ = lean_ctor_get(v_l_2056_, 4);
lean_inc(v_r_2231_);
v_size_2232_ = lean_ctor_get(v_r_2057_, 0);
v_k_2233_ = lean_ctor_get(v_r_2057_, 1);
v_v_2234_ = lean_ctor_get(v_r_2057_, 2);
v_l_2235_ = lean_ctor_get(v_r_2057_, 3);
lean_inc(v_l_2235_);
v_r_2236_ = lean_ctor_get(v_r_2057_, 4);
v___x_2237_ = lean_unsigned_to_nat(1u);
v___x_2238_ = lean_nat_dec_lt(v_size_2227_, v_size_2232_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2374_; 
lean_inc(v_l_2230_);
lean_inc(v_v_2229_);
lean_inc(v_k_2228_);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_l_2056_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; lean_object* v_unused_2376_; lean_object* v_unused_2377_; lean_object* v_unused_2378_; lean_object* v_unused_2379_; 
v_unused_2375_ = lean_ctor_get(v_l_2056_, 4);
lean_dec(v_unused_2375_);
v_unused_2376_ = lean_ctor_get(v_l_2056_, 3);
lean_dec(v_unused_2376_);
v_unused_2377_ = lean_ctor_get(v_l_2056_, 2);
lean_dec(v_unused_2377_);
v_unused_2378_ = lean_ctor_get(v_l_2056_, 1);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v_l_2056_, 0);
lean_dec(v_unused_2379_);
v___x_2240_ = v_l_2056_;
v_isShared_2241_ = v_isSharedCheck_2374_;
goto v_resetjp_2239_;
}
else
{
lean_dec(v_l_2056_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2374_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v_tree_2243_; 
v___x_2242_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_2228_, v_v_2229_, v_l_2230_, v_r_2231_);
v_tree_2243_ = lean_ctor_get(v___x_2242_, 2);
if (lean_obj_tag(v_tree_2243_) == 0)
{
lean_object* v_k_2244_; lean_object* v_v_2245_; lean_object* v_size_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
lean_inc_ref(v_tree_2243_);
v_k_2244_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_k_2244_);
v_v_2245_ = lean_ctor_get(v___x_2242_, 1);
lean_inc(v_v_2245_);
lean_dec_ref(v___x_2242_);
v_size_2246_ = lean_ctor_get(v_tree_2243_, 0);
v___x_2247_ = lean_unsigned_to_nat(3u);
v___x_2248_ = lean_nat_mul(v___x_2247_, v_size_2246_);
v___x_2249_ = lean_nat_dec_lt(v___x_2248_, v_size_2232_);
lean_dec(v___x_2248_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2253_; 
lean_dec(v_l_2235_);
v___x_2250_ = lean_nat_add(v___x_2237_, v_size_2246_);
v___x_2251_ = lean_nat_add(v___x_2250_, v_size_2232_);
lean_dec(v___x_2250_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 4, v_r_2057_);
lean_ctor_set(v___x_2240_, 3, v_tree_2243_);
lean_ctor_set(v___x_2240_, 2, v_v_2245_);
lean_ctor_set(v___x_2240_, 1, v_k_2244_);
lean_ctor_set(v___x_2240_, 0, v___x_2251_);
v___x_2253_ = v___x_2240_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_k_2244_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_v_2245_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_tree_2243_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_r_2057_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
else
{
lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2309_; 
lean_inc(v_r_2236_);
lean_inc(v_v_2234_);
lean_inc(v_k_2233_);
lean_inc(v_size_2232_);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_r_2057_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; lean_object* v_unused_2311_; lean_object* v_unused_2312_; lean_object* v_unused_2313_; lean_object* v_unused_2314_; 
v_unused_2310_ = lean_ctor_get(v_r_2057_, 4);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_r_2057_, 3);
lean_dec(v_unused_2311_);
v_unused_2312_ = lean_ctor_get(v_r_2057_, 2);
lean_dec(v_unused_2312_);
v_unused_2313_ = lean_ctor_get(v_r_2057_, 1);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_r_2057_, 0);
lean_dec(v_unused_2314_);
v___x_2256_ = v_r_2057_;
v_isShared_2257_ = v_isSharedCheck_2309_;
goto v_resetjp_2255_;
}
else
{
lean_dec(v_r_2057_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2309_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_size_2258_; lean_object* v_k_2259_; lean_object* v_v_2260_; lean_object* v_l_2261_; lean_object* v_r_2262_; lean_object* v_size_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v_size_2258_ = lean_ctor_get(v_l_2235_, 0);
v_k_2259_ = lean_ctor_get(v_l_2235_, 1);
v_v_2260_ = lean_ctor_get(v_l_2235_, 2);
v_l_2261_ = lean_ctor_get(v_l_2235_, 3);
v_r_2262_ = lean_ctor_get(v_l_2235_, 4);
v_size_2263_ = lean_ctor_get(v_r_2236_, 0);
v___x_2264_ = lean_unsigned_to_nat(2u);
v___x_2265_ = lean_nat_mul(v___x_2264_, v_size_2263_);
v___x_2266_ = lean_nat_dec_lt(v_size_2258_, v___x_2265_);
lean_dec(v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2294_; 
lean_inc(v_r_2262_);
lean_inc(v_l_2261_);
lean_inc(v_v_2260_);
lean_inc(v_k_2259_);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_l_2235_);
if (v_isSharedCheck_2294_ == 0)
{
lean_object* v_unused_2295_; lean_object* v_unused_2296_; lean_object* v_unused_2297_; lean_object* v_unused_2298_; lean_object* v_unused_2299_; 
v_unused_2295_ = lean_ctor_get(v_l_2235_, 4);
lean_dec(v_unused_2295_);
v_unused_2296_ = lean_ctor_get(v_l_2235_, 3);
lean_dec(v_unused_2296_);
v_unused_2297_ = lean_ctor_get(v_l_2235_, 2);
lean_dec(v_unused_2297_);
v_unused_2298_ = lean_ctor_get(v_l_2235_, 1);
lean_dec(v_unused_2298_);
v_unused_2299_ = lean_ctor_get(v_l_2235_, 0);
lean_dec(v_unused_2299_);
v___x_2268_ = v_l_2235_;
v_isShared_2269_ = v_isSharedCheck_2294_;
goto v_resetjp_2267_;
}
else
{
lean_dec(v_l_2235_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2294_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2284_; 
v___x_2270_ = lean_nat_add(v___x_2237_, v_size_2246_);
v___x_2271_ = lean_nat_add(v___x_2270_, v_size_2232_);
lean_dec(v_size_2232_);
if (lean_obj_tag(v_l_2261_) == 0)
{
lean_object* v_size_2292_; 
v_size_2292_ = lean_ctor_get(v_l_2261_, 0);
lean_inc(v_size_2292_);
v___y_2284_ = v_size_2292_;
goto v___jp_2283_;
}
else
{
lean_object* v___x_2293_; 
v___x_2293_ = lean_unsigned_to_nat(0u);
v___y_2284_ = v___x_2293_;
goto v___jp_2283_;
}
v___jp_2272_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
v___x_2276_ = lean_nat_add(v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec(v___y_2274_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 4, v_r_2236_);
lean_ctor_set(v___x_2268_, 3, v_r_2262_);
lean_ctor_set(v___x_2268_, 2, v_v_2234_);
lean_ctor_set(v___x_2268_, 1, v_k_2233_);
lean_ctor_set(v___x_2268_, 0, v___x_2276_);
v___x_2278_ = v___x_2268_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2282_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2282_, 3, v_r_2262_);
lean_ctor_set(v_reuseFailAlloc_2282_, 4, v_r_2236_);
v___x_2278_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2280_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 4, v___x_2278_);
lean_ctor_set(v___x_2256_, 3, v___y_2273_);
lean_ctor_set(v___x_2256_, 2, v_v_2260_);
lean_ctor_set(v___x_2256_, 1, v_k_2259_);
lean_ctor_set(v___x_2256_, 0, v___x_2271_);
v___x_2280_ = v___x_2256_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2281_, 1, v_k_2259_);
lean_ctor_set(v_reuseFailAlloc_2281_, 2, v_v_2260_);
lean_ctor_set(v_reuseFailAlloc_2281_, 3, v___y_2273_);
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
v___jp_2283_:
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2285_ = lean_nat_add(v___x_2270_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec(v___x_2270_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 4, v_l_2261_);
lean_ctor_set(v___x_2240_, 3, v_tree_2243_);
lean_ctor_set(v___x_2240_, 2, v_v_2245_);
lean_ctor_set(v___x_2240_, 1, v_k_2244_);
lean_ctor_set(v___x_2240_, 0, v___x_2285_);
v___x_2287_ = v___x_2240_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v_k_2244_);
lean_ctor_set(v_reuseFailAlloc_2291_, 2, v_v_2245_);
lean_ctor_set(v_reuseFailAlloc_2291_, 3, v_tree_2243_);
lean_ctor_set(v_reuseFailAlloc_2291_, 4, v_l_2261_);
v___x_2287_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_nat_add(v___x_2237_, v_size_2263_);
if (lean_obj_tag(v_r_2262_) == 0)
{
lean_object* v_size_2289_; 
v_size_2289_ = lean_ctor_get(v_r_2262_, 0);
lean_inc(v_size_2289_);
v___y_2273_ = v___x_2287_;
v___y_2274_ = v___x_2288_;
v___y_2275_ = v_size_2289_;
goto v___jp_2272_;
}
else
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_unsigned_to_nat(0u);
v___y_2273_ = v___x_2287_;
v___y_2274_ = v___x_2288_;
v___y_2275_ = v___x_2290_;
goto v___jp_2272_;
}
}
}
}
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2300_ = lean_nat_add(v___x_2237_, v_size_2246_);
v___x_2301_ = lean_nat_add(v___x_2300_, v_size_2232_);
lean_dec(v_size_2232_);
v___x_2302_ = lean_nat_add(v___x_2300_, v_size_2258_);
lean_dec(v___x_2300_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 4, v_l_2235_);
lean_ctor_set(v___x_2256_, 3, v_tree_2243_);
lean_ctor_set(v___x_2256_, 2, v_v_2245_);
lean_ctor_set(v___x_2256_, 1, v_k_2244_);
lean_ctor_set(v___x_2256_, 0, v___x_2302_);
v___x_2304_ = v___x_2256_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_k_2244_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_v_2245_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_tree_2243_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v_l_2235_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2306_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 4, v_r_2236_);
lean_ctor_set(v___x_2240_, 3, v___x_2304_);
lean_ctor_set(v___x_2240_, 2, v_v_2234_);
lean_ctor_set(v___x_2240_, 1, v_k_2233_);
lean_ctor_set(v___x_2240_, 0, v___x_2301_);
v___x_2306_ = v___x_2240_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_r_2236_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
}
else
{
lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2368_; 
lean_inc(v_r_2236_);
lean_inc(v_v_2234_);
lean_inc(v_k_2233_);
lean_inc(v_size_2232_);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_r_2057_);
if (v_isSharedCheck_2368_ == 0)
{
lean_object* v_unused_2369_; lean_object* v_unused_2370_; lean_object* v_unused_2371_; lean_object* v_unused_2372_; lean_object* v_unused_2373_; 
v_unused_2369_ = lean_ctor_get(v_r_2057_, 4);
lean_dec(v_unused_2369_);
v_unused_2370_ = lean_ctor_get(v_r_2057_, 3);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v_r_2057_, 2);
lean_dec(v_unused_2371_);
v_unused_2372_ = lean_ctor_get(v_r_2057_, 1);
lean_dec(v_unused_2372_);
v_unused_2373_ = lean_ctor_get(v_r_2057_, 0);
lean_dec(v_unused_2373_);
v___x_2316_ = v_r_2057_;
v_isShared_2317_ = v_isSharedCheck_2368_;
goto v_resetjp_2315_;
}
else
{
lean_dec(v_r_2057_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2368_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
if (lean_obj_tag(v_l_2235_) == 0)
{
if (lean_obj_tag(v_r_2236_) == 0)
{
lean_object* v_k_2318_; lean_object* v_v_2319_; lean_object* v_size_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2324_; 
lean_inc(v_tree_2243_);
v_k_2318_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_k_2318_);
v_v_2319_ = lean_ctor_get(v___x_2242_, 1);
lean_inc(v_v_2319_);
lean_dec_ref(v___x_2242_);
v_size_2320_ = lean_ctor_get(v_l_2235_, 0);
v___x_2321_ = lean_nat_add(v___x_2237_, v_size_2232_);
lean_dec(v_size_2232_);
v___x_2322_ = lean_nat_add(v___x_2237_, v_size_2320_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 4, v_l_2235_);
lean_ctor_set(v___x_2316_, 3, v_tree_2243_);
lean_ctor_set(v___x_2316_, 2, v_v_2319_);
lean_ctor_set(v___x_2316_, 1, v_k_2318_);
lean_ctor_set(v___x_2316_, 0, v___x_2322_);
v___x_2324_ = v___x_2316_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_k_2318_);
lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_v_2319_);
lean_ctor_set(v_reuseFailAlloc_2328_, 3, v_tree_2243_);
lean_ctor_set(v_reuseFailAlloc_2328_, 4, v_l_2235_);
v___x_2324_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 4, v_r_2236_);
lean_ctor_set(v___x_2240_, 3, v___x_2324_);
lean_ctor_set(v___x_2240_, 2, v_v_2234_);
lean_ctor_set(v___x_2240_, 1, v_k_2233_);
lean_ctor_set(v___x_2240_, 0, v___x_2321_);
v___x_2326_ = v___x_2240_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2321_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v___x_2324_);
lean_ctor_set(v_reuseFailAlloc_2327_, 4, v_r_2236_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
else
{
lean_object* v_k_2329_; lean_object* v_v_2330_; lean_object* v_k_2331_; lean_object* v_v_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_size_2232_);
v_k_2329_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_k_2329_);
v_v_2330_ = lean_ctor_get(v___x_2242_, 1);
lean_inc(v_v_2330_);
lean_dec_ref(v___x_2242_);
v_k_2331_ = lean_ctor_get(v_l_2235_, 1);
v_v_2332_ = lean_ctor_get(v_l_2235_, 2);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_l_2235_);
if (v_isSharedCheck_2346_ == 0)
{
lean_object* v_unused_2347_; lean_object* v_unused_2348_; lean_object* v_unused_2349_; 
v_unused_2347_ = lean_ctor_get(v_l_2235_, 4);
lean_dec(v_unused_2347_);
v_unused_2348_ = lean_ctor_get(v_l_2235_, 3);
lean_dec(v_unused_2348_);
v_unused_2349_ = lean_ctor_get(v_l_2235_, 0);
lean_dec(v_unused_2349_);
v___x_2334_ = v_l_2235_;
v_isShared_2335_ = v_isSharedCheck_2346_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_v_2332_);
lean_inc(v_k_2331_);
lean_dec(v_l_2235_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2346_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2336_ = lean_unsigned_to_nat(3u);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 4, v_r_2236_);
lean_ctor_set(v___x_2334_, 3, v_r_2236_);
lean_ctor_set(v___x_2334_, 2, v_v_2330_);
lean_ctor_set(v___x_2334_, 1, v_k_2329_);
lean_ctor_set(v___x_2334_, 0, v___x_2237_);
v___x_2338_ = v___x_2334_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_k_2329_);
lean_ctor_set(v_reuseFailAlloc_2345_, 2, v_v_2330_);
lean_ctor_set(v_reuseFailAlloc_2345_, 3, v_r_2236_);
lean_ctor_set(v_reuseFailAlloc_2345_, 4, v_r_2236_);
v___x_2338_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2340_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 3, v_r_2236_);
lean_ctor_set(v___x_2316_, 0, v___x_2237_);
v___x_2340_ = v___x_2316_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2344_, 3, v_r_2236_);
lean_ctor_set(v_reuseFailAlloc_2344_, 4, v_r_2236_);
v___x_2340_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
lean_object* v___x_2342_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 4, v___x_2340_);
lean_ctor_set(v___x_2240_, 3, v___x_2338_);
lean_ctor_set(v___x_2240_, 2, v_v_2332_);
lean_ctor_set(v___x_2240_, 1, v_k_2331_);
lean_ctor_set(v___x_2240_, 0, v___x_2336_);
v___x_2342_ = v___x_2240_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_k_2331_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v_v_2332_);
lean_ctor_set(v_reuseFailAlloc_2343_, 3, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2343_, 4, v___x_2340_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2236_) == 0)
{
lean_object* v_k_2350_; lean_object* v_v_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; 
lean_dec(v_size_2232_);
v_k_2350_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_k_2350_);
v_v_2351_ = lean_ctor_get(v___x_2242_, 1);
lean_inc(v_v_2351_);
lean_dec_ref(v___x_2242_);
v___x_2352_ = lean_unsigned_to_nat(3u);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 4, v_l_2235_);
lean_ctor_set(v___x_2316_, 2, v_v_2351_);
lean_ctor_set(v___x_2316_, 1, v_k_2350_);
lean_ctor_set(v___x_2316_, 0, v___x_2237_);
v___x_2354_ = v___x_2316_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_2350_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_2351_);
lean_ctor_set(v_reuseFailAlloc_2358_, 3, v_l_2235_);
lean_ctor_set(v_reuseFailAlloc_2358_, 4, v_l_2235_);
v___x_2354_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2356_; 
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 4, v_r_2236_);
lean_ctor_set(v___x_2240_, 3, v___x_2354_);
lean_ctor_set(v___x_2240_, 2, v_v_2234_);
lean_ctor_set(v___x_2240_, 1, v_k_2233_);
lean_ctor_set(v___x_2240_, 0, v___x_2352_);
v___x_2356_ = v___x_2240_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2357_, 3, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2357_, 4, v_r_2236_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
else
{
lean_object* v_k_2359_; lean_object* v_v_2360_; lean_object* v___x_2362_; 
v_k_2359_ = lean_ctor_get(v___x_2242_, 0);
lean_inc(v_k_2359_);
v_v_2360_ = lean_ctor_get(v___x_2242_, 1);
lean_inc(v_v_2360_);
lean_dec_ref(v___x_2242_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 3, v_r_2236_);
v___x_2362_ = v___x_2316_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_size_2232_);
lean_ctor_set(v_reuseFailAlloc_2367_, 1, v_k_2233_);
lean_ctor_set(v_reuseFailAlloc_2367_, 2, v_v_2234_);
lean_ctor_set(v_reuseFailAlloc_2367_, 3, v_r_2236_);
lean_ctor_set(v_reuseFailAlloc_2367_, 4, v_r_2236_);
v___x_2362_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2363_ = lean_unsigned_to_nat(2u);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 4, v___x_2362_);
lean_ctor_set(v___x_2240_, 3, v_r_2236_);
lean_ctor_set(v___x_2240_, 2, v_v_2360_);
lean_ctor_set(v___x_2240_, 1, v_k_2359_);
lean_ctor_set(v___x_2240_, 0, v___x_2363_);
v___x_2365_ = v___x_2240_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_k_2359_);
lean_ctor_set(v_reuseFailAlloc_2366_, 2, v_v_2360_);
lean_ctor_set(v_reuseFailAlloc_2366_, 3, v_r_2236_);
lean_ctor_set(v_reuseFailAlloc_2366_, 4, v___x_2362_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
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
lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2532_; 
lean_inc(v_r_2236_);
lean_inc(v_v_2234_);
lean_inc(v_k_2233_);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_r_2057_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; lean_object* v_unused_2536_; lean_object* v_unused_2537_; 
v_unused_2533_ = lean_ctor_get(v_r_2057_, 4);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_r_2057_, 3);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_r_2057_, 2);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v_r_2057_, 1);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_r_2057_, 0);
lean_dec(v_unused_2537_);
v___x_2381_ = v_r_2057_;
v_isShared_2382_ = v_isSharedCheck_2532_;
goto v_resetjp_2380_;
}
else
{
lean_dec(v_r_2057_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2532_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v_tree_2384_; 
v___x_2383_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_2233_, v_v_2234_, v_l_2235_, v_r_2236_);
v_tree_2384_ = lean_ctor_get(v___x_2383_, 2);
lean_inc(v_tree_2384_);
if (lean_obj_tag(v_tree_2384_) == 0)
{
lean_object* v_k_2385_; lean_object* v_v_2386_; lean_object* v_size_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; 
v_k_2385_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_k_2385_);
v_v_2386_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_v_2386_);
lean_dec_ref(v___x_2383_);
v_size_2387_ = lean_ctor_get(v_tree_2384_, 0);
v___x_2388_ = lean_unsigned_to_nat(3u);
v___x_2389_ = lean_nat_mul(v___x_2388_, v_size_2387_);
v___x_2390_ = lean_nat_dec_lt(v___x_2389_, v_size_2227_);
lean_dec(v___x_2389_);
if (v___x_2390_ == 0)
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
lean_dec(v_r_2231_);
v___x_2391_ = lean_nat_add(v___x_2237_, v_size_2227_);
v___x_2392_ = lean_nat_add(v___x_2391_, v_size_2387_);
lean_dec(v___x_2391_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 4, v_tree_2384_);
lean_ctor_set(v___x_2381_, 3, v_l_2056_);
lean_ctor_set(v___x_2381_, 2, v_v_2386_);
lean_ctor_set(v___x_2381_, 1, v_k_2385_);
lean_ctor_set(v___x_2381_, 0, v___x_2392_);
v___x_2394_ = v___x_2381_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_k_2385_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_v_2386_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v_l_2056_);
lean_ctor_set(v_reuseFailAlloc_2395_, 4, v_tree_2384_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
else
{
lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2461_; 
lean_inc(v_l_2230_);
lean_inc(v_v_2229_);
lean_inc(v_k_2228_);
lean_inc(v_size_2227_);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_l_2056_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; lean_object* v_unused_2463_; lean_object* v_unused_2464_; lean_object* v_unused_2465_; lean_object* v_unused_2466_; 
v_unused_2462_ = lean_ctor_get(v_l_2056_, 4);
lean_dec(v_unused_2462_);
v_unused_2463_ = lean_ctor_get(v_l_2056_, 3);
lean_dec(v_unused_2463_);
v_unused_2464_ = lean_ctor_get(v_l_2056_, 2);
lean_dec(v_unused_2464_);
v_unused_2465_ = lean_ctor_get(v_l_2056_, 1);
lean_dec(v_unused_2465_);
v_unused_2466_ = lean_ctor_get(v_l_2056_, 0);
lean_dec(v_unused_2466_);
v___x_2397_ = v_l_2056_;
v_isShared_2398_ = v_isSharedCheck_2461_;
goto v_resetjp_2396_;
}
else
{
lean_dec(v_l_2056_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2461_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v_size_2399_; lean_object* v_size_2400_; lean_object* v_k_2401_; lean_object* v_v_2402_; lean_object* v_l_2403_; lean_object* v_r_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v_size_2399_ = lean_ctor_get(v_l_2230_, 0);
v_size_2400_ = lean_ctor_get(v_r_2231_, 0);
v_k_2401_ = lean_ctor_get(v_r_2231_, 1);
v_v_2402_ = lean_ctor_get(v_r_2231_, 2);
v_l_2403_ = lean_ctor_get(v_r_2231_, 3);
v_r_2404_ = lean_ctor_get(v_r_2231_, 4);
v___x_2405_ = lean_unsigned_to_nat(2u);
v___x_2406_ = lean_nat_mul(v___x_2405_, v_size_2399_);
v___x_2407_ = lean_nat_dec_lt(v_size_2400_, v___x_2406_);
lean_dec(v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2445_; 
lean_inc(v_r_2404_);
lean_inc(v_l_2403_);
lean_inc(v_v_2402_);
lean_inc(v_k_2401_);
lean_del_object(v___x_2397_);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_r_2231_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; lean_object* v_unused_2447_; lean_object* v_unused_2448_; lean_object* v_unused_2449_; lean_object* v_unused_2450_; 
v_unused_2446_ = lean_ctor_get(v_r_2231_, 4);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_r_2231_, 3);
lean_dec(v_unused_2447_);
v_unused_2448_ = lean_ctor_get(v_r_2231_, 2);
lean_dec(v_unused_2448_);
v_unused_2449_ = lean_ctor_get(v_r_2231_, 1);
lean_dec(v_unused_2449_);
v_unused_2450_ = lean_ctor_get(v_r_2231_, 0);
lean_dec(v_unused_2450_);
v___x_2409_ = v_r_2231_;
v_isShared_2410_ = v_isSharedCheck_2445_;
goto v_resetjp_2408_;
}
else
{
lean_dec(v_r_2231_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2445_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___x_2433_; lean_object* v___y_2435_; 
v___x_2411_ = lean_nat_add(v___x_2237_, v_size_2227_);
lean_dec(v_size_2227_);
v___x_2412_ = lean_nat_add(v___x_2411_, v_size_2387_);
lean_dec(v___x_2411_);
v___x_2433_ = lean_nat_add(v___x_2237_, v_size_2399_);
if (lean_obj_tag(v_l_2403_) == 0)
{
lean_object* v_size_2443_; 
v_size_2443_ = lean_ctor_get(v_l_2403_, 0);
lean_inc(v_size_2443_);
v___y_2435_ = v_size_2443_;
goto v___jp_2434_;
}
else
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_unsigned_to_nat(0u);
v___y_2435_ = v___x_2444_;
goto v___jp_2434_;
}
v___jp_2413_:
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2417_ = lean_nat_add(v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec(v___y_2415_);
lean_inc_ref(v_tree_2384_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 4, v_tree_2384_);
lean_ctor_set(v___x_2409_, 3, v_r_2404_);
lean_ctor_set(v___x_2409_, 2, v_v_2386_);
lean_ctor_set(v___x_2409_, 1, v_k_2385_);
lean_ctor_set(v___x_2409_, 0, v___x_2417_);
v___x_2419_ = v___x_2409_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_k_2385_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_v_2386_);
lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_r_2404_);
lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_tree_2384_);
v___x_2419_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v_isSharedCheck_2426_ = !lean_is_exclusive(v_tree_2384_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; lean_object* v_unused_2428_; lean_object* v_unused_2429_; lean_object* v_unused_2430_; lean_object* v_unused_2431_; 
v_unused_2427_ = lean_ctor_get(v_tree_2384_, 4);
lean_dec(v_unused_2427_);
v_unused_2428_ = lean_ctor_get(v_tree_2384_, 3);
lean_dec(v_unused_2428_);
v_unused_2429_ = lean_ctor_get(v_tree_2384_, 2);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_tree_2384_, 1);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_tree_2384_, 0);
lean_dec(v_unused_2431_);
v___x_2421_ = v_tree_2384_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_dec(v_tree_2384_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 4, v___x_2419_);
lean_ctor_set(v___x_2421_, 3, v___y_2414_);
lean_ctor_set(v___x_2421_, 2, v_v_2402_);
lean_ctor_set(v___x_2421_, 1, v_k_2401_);
lean_ctor_set(v___x_2421_, 0, v___x_2412_);
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_k_2401_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_v_2402_);
lean_ctor_set(v_reuseFailAlloc_2425_, 3, v___y_2414_);
lean_ctor_set(v_reuseFailAlloc_2425_, 4, v___x_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
v___jp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2438_; 
v___x_2436_ = lean_nat_add(v___x_2433_, v___y_2435_);
lean_dec(v___y_2435_);
lean_dec(v___x_2433_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 4, v_l_2403_);
lean_ctor_set(v___x_2381_, 3, v_l_2230_);
lean_ctor_set(v___x_2381_, 2, v_v_2229_);
lean_ctor_set(v___x_2381_, 1, v_k_2228_);
lean_ctor_set(v___x_2381_, 0, v___x_2436_);
v___x_2438_ = v___x_2381_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2436_);
lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_k_2228_);
lean_ctor_set(v_reuseFailAlloc_2442_, 2, v_v_2229_);
lean_ctor_set(v_reuseFailAlloc_2442_, 3, v_l_2230_);
lean_ctor_set(v_reuseFailAlloc_2442_, 4, v_l_2403_);
v___x_2438_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_nat_add(v___x_2237_, v_size_2387_);
if (lean_obj_tag(v_r_2404_) == 0)
{
lean_object* v_size_2440_; 
v_size_2440_ = lean_ctor_get(v_r_2404_, 0);
lean_inc(v_size_2440_);
v___y_2414_ = v___x_2438_;
v___y_2415_ = v___x_2439_;
v___y_2416_ = v_size_2440_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_unsigned_to_nat(0u);
v___y_2414_ = v___x_2438_;
v___y_2415_ = v___x_2439_;
v___y_2416_ = v___x_2441_;
goto v___jp_2413_;
}
}
}
}
}
else
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2451_ = lean_nat_add(v___x_2237_, v_size_2227_);
lean_dec(v_size_2227_);
v___x_2452_ = lean_nat_add(v___x_2451_, v_size_2387_);
lean_dec(v___x_2451_);
v___x_2453_ = lean_nat_add(v___x_2237_, v_size_2387_);
v___x_2454_ = lean_nat_add(v___x_2453_, v_size_2400_);
lean_dec(v___x_2453_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 4, v_tree_2384_);
lean_ctor_set(v___x_2381_, 3, v_r_2231_);
lean_ctor_set(v___x_2381_, 2, v_v_2386_);
lean_ctor_set(v___x_2381_, 1, v_k_2385_);
lean_ctor_set(v___x_2381_, 0, v___x_2454_);
v___x_2456_ = v___x_2381_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_k_2385_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_v_2386_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v_r_2231_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v_tree_2384_);
v___x_2456_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2458_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 4, v___x_2456_);
lean_ctor_set(v___x_2397_, 0, v___x_2452_);
v___x_2458_ = v___x_2397_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_k_2228_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_v_2229_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_l_2230_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_2230_) == 0)
{
lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2490_; 
lean_inc_ref(v_l_2230_);
lean_inc(v_v_2229_);
lean_inc(v_k_2228_);
lean_inc(v_size_2227_);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_l_2056_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; lean_object* v_unused_2492_; lean_object* v_unused_2493_; lean_object* v_unused_2494_; lean_object* v_unused_2495_; 
v_unused_2491_ = lean_ctor_get(v_l_2056_, 4);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_l_2056_, 3);
lean_dec(v_unused_2492_);
v_unused_2493_ = lean_ctor_get(v_l_2056_, 2);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v_l_2056_, 1);
lean_dec(v_unused_2494_);
v_unused_2495_ = lean_ctor_get(v_l_2056_, 0);
lean_dec(v_unused_2495_);
v___x_2468_ = v_l_2056_;
v_isShared_2469_ = v_isSharedCheck_2490_;
goto v_resetjp_2467_;
}
else
{
lean_dec(v_l_2056_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2490_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
if (lean_obj_tag(v_r_2231_) == 0)
{
lean_object* v_k_2470_; lean_object* v_v_2471_; lean_object* v_size_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v_k_2470_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_k_2470_);
v_v_2471_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_v_2471_);
lean_dec_ref(v___x_2383_);
v_size_2472_ = lean_ctor_get(v_r_2231_, 0);
v___x_2473_ = lean_nat_add(v___x_2237_, v_size_2227_);
lean_dec(v_size_2227_);
v___x_2474_ = lean_nat_add(v___x_2237_, v_size_2472_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 4, v_tree_2384_);
lean_ctor_set(v___x_2381_, 3, v_r_2231_);
lean_ctor_set(v___x_2381_, 2, v_v_2471_);
lean_ctor_set(v___x_2381_, 1, v_k_2470_);
lean_ctor_set(v___x_2381_, 0, v___x_2474_);
v___x_2476_ = v___x_2381_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_k_2470_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_v_2471_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_r_2231_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v_tree_2384_);
v___x_2476_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2478_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 4, v___x_2476_);
lean_ctor_set(v___x_2468_, 0, v___x_2473_);
v___x_2478_ = v___x_2468_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v_k_2228_);
lean_ctor_set(v_reuseFailAlloc_2479_, 2, v_v_2229_);
lean_ctor_set(v_reuseFailAlloc_2479_, 3, v_l_2230_);
lean_ctor_set(v_reuseFailAlloc_2479_, 4, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
else
{
lean_object* v_k_2481_; lean_object* v_v_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
lean_dec(v_size_2227_);
v_k_2481_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_k_2481_);
v_v_2482_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_v_2482_);
lean_dec_ref(v___x_2383_);
v___x_2483_ = lean_unsigned_to_nat(3u);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 4, v_r_2231_);
lean_ctor_set(v___x_2381_, 3, v_r_2231_);
lean_ctor_set(v___x_2381_, 2, v_v_2482_);
lean_ctor_set(v___x_2381_, 1, v_k_2481_);
lean_ctor_set(v___x_2381_, 0, v___x_2237_);
v___x_2485_ = v___x_2381_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_k_2481_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_v_2482_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_r_2231_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_r_2231_);
v___x_2485_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2487_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 4, v___x_2485_);
lean_ctor_set(v___x_2468_, 0, v___x_2483_);
v___x_2487_ = v___x_2468_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_k_2228_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_v_2229_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_l_2230_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v___x_2485_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_2231_) == 0)
{
lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2520_; 
lean_inc(v_l_2230_);
lean_inc(v_v_2229_);
lean_inc(v_k_2228_);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_l_2056_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; lean_object* v_unused_2522_; lean_object* v_unused_2523_; lean_object* v_unused_2524_; lean_object* v_unused_2525_; 
v_unused_2521_ = lean_ctor_get(v_l_2056_, 4);
lean_dec(v_unused_2521_);
v_unused_2522_ = lean_ctor_get(v_l_2056_, 3);
lean_dec(v_unused_2522_);
v_unused_2523_ = lean_ctor_get(v_l_2056_, 2);
lean_dec(v_unused_2523_);
v_unused_2524_ = lean_ctor_get(v_l_2056_, 1);
lean_dec(v_unused_2524_);
v_unused_2525_ = lean_ctor_get(v_l_2056_, 0);
lean_dec(v_unused_2525_);
v___x_2497_ = v_l_2056_;
v_isShared_2498_ = v_isSharedCheck_2520_;
goto v_resetjp_2496_;
}
else
{
lean_dec(v_l_2056_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2520_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v_k_2499_; lean_object* v_v_2500_; lean_object* v_k_2501_; lean_object* v_v_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2516_; 
v_k_2499_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_k_2499_);
v_v_2500_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_v_2500_);
lean_dec_ref(v___x_2383_);
v_k_2501_ = lean_ctor_get(v_r_2231_, 1);
v_v_2502_ = lean_ctor_get(v_r_2231_, 2);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_r_2231_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; lean_object* v_unused_2518_; lean_object* v_unused_2519_; 
v_unused_2517_ = lean_ctor_get(v_r_2231_, 4);
lean_dec(v_unused_2517_);
v_unused_2518_ = lean_ctor_get(v_r_2231_, 3);
lean_dec(v_unused_2518_);
v_unused_2519_ = lean_ctor_get(v_r_2231_, 0);
lean_dec(v_unused_2519_);
v___x_2504_ = v_r_2231_;
v_isShared_2505_ = v_isSharedCheck_2516_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_v_2502_);
lean_inc(v_k_2501_);
lean_dec(v_r_2231_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2516_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___x_2508_; 
v___x_2506_ = lean_unsigned_to_nat(3u);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 4, v_l_2230_);
lean_ctor_set(v___x_2504_, 3, v_l_2230_);
lean_ctor_set(v___x_2504_, 2, v_v_2229_);
lean_ctor_set(v___x_2504_, 1, v_k_2228_);
lean_ctor_set(v___x_2504_, 0, v___x_2237_);
v___x_2508_ = v___x_2504_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_k_2228_);
lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_v_2229_);
lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_l_2230_);
lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_l_2230_);
v___x_2508_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
lean_object* v___x_2510_; 
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 4, v_l_2230_);
lean_ctor_set(v___x_2381_, 3, v_l_2230_);
lean_ctor_set(v___x_2381_, 2, v_v_2500_);
lean_ctor_set(v___x_2381_, 1, v_k_2499_);
lean_ctor_set(v___x_2381_, 0, v___x_2237_);
v___x_2510_ = v___x_2381_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2237_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_k_2499_);
lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_v_2500_);
lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_l_2230_);
lean_ctor_set(v_reuseFailAlloc_2514_, 4, v_l_2230_);
v___x_2510_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2512_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 4, v___x_2510_);
lean_ctor_set(v___x_2497_, 3, v___x_2508_);
lean_ctor_set(v___x_2497_, 2, v_v_2502_);
lean_ctor_set(v___x_2497_, 1, v_k_2501_);
lean_ctor_set(v___x_2497_, 0, v___x_2506_);
v___x_2512_ = v___x_2497_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_k_2501_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v_v_2502_);
lean_ctor_set(v_reuseFailAlloc_2513_, 3, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2513_, 4, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
}
else
{
lean_object* v_k_2526_; lean_object* v_v_2527_; lean_object* v___x_2528_; lean_object* v___x_2530_; 
v_k_2526_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_k_2526_);
v_v_2527_ = lean_ctor_get(v___x_2383_, 1);
lean_inc(v_v_2527_);
lean_dec_ref(v___x_2383_);
v___x_2528_ = lean_unsigned_to_nat(2u);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 4, v_r_2231_);
lean_ctor_set(v___x_2381_, 3, v_l_2056_);
lean_ctor_set(v___x_2381_, 2, v_v_2527_);
lean_ctor_set(v___x_2381_, 1, v_k_2526_);
lean_ctor_set(v___x_2381_, 0, v___x_2528_);
v___x_2530_ = v___x_2381_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2528_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_k_2526_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_v_2527_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_l_2056_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_r_2231_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
}
}
else
{
return v_l_2056_;
}
}
else
{
return v_r_2057_;
}
}
}
else
{
lean_object* v_impl_2538_; lean_object* v___x_2539_; 
v_impl_2538_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2052_, v_l_2056_);
v___x_2539_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_2538_) == 0)
{
if (lean_obj_tag(v_r_2057_) == 0)
{
lean_object* v_size_2540_; lean_object* v_size_2541_; lean_object* v_k_2542_; lean_object* v_v_2543_; lean_object* v_l_2544_; lean_object* v_r_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v_size_2540_ = lean_ctor_get(v_impl_2538_, 0);
v_size_2541_ = lean_ctor_get(v_r_2057_, 0);
v_k_2542_ = lean_ctor_get(v_r_2057_, 1);
v_v_2543_ = lean_ctor_get(v_r_2057_, 2);
v_l_2544_ = lean_ctor_get(v_r_2057_, 3);
lean_inc(v_l_2544_);
v_r_2545_ = lean_ctor_get(v_r_2057_, 4);
v___x_2546_ = lean_unsigned_to_nat(3u);
v___x_2547_ = lean_nat_mul(v___x_2546_, v_size_2540_);
v___x_2548_ = lean_nat_dec_lt(v___x_2547_, v_size_2541_);
lean_dec(v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; 
lean_dec(v_l_2544_);
v___x_2549_ = lean_nat_add(v___x_2539_, v_size_2540_);
v___x_2550_ = lean_nat_add(v___x_2549_, v_size_2541_);
lean_dec(v___x_2549_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 3, v_impl_2538_);
lean_ctor_set(v___x_2059_, 0, v___x_2550_);
v___x_2552_ = v___x_2059_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2550_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_impl_2538_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_r_2057_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
else
{
lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2617_; 
lean_inc(v_r_2545_);
lean_inc(v_v_2543_);
lean_inc(v_k_2542_);
lean_inc(v_size_2541_);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_r_2057_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; lean_object* v_unused_2619_; lean_object* v_unused_2620_; lean_object* v_unused_2621_; lean_object* v_unused_2622_; 
v_unused_2618_ = lean_ctor_get(v_r_2057_, 4);
lean_dec(v_unused_2618_);
v_unused_2619_ = lean_ctor_get(v_r_2057_, 3);
lean_dec(v_unused_2619_);
v_unused_2620_ = lean_ctor_get(v_r_2057_, 2);
lean_dec(v_unused_2620_);
v_unused_2621_ = lean_ctor_get(v_r_2057_, 1);
lean_dec(v_unused_2621_);
v_unused_2622_ = lean_ctor_get(v_r_2057_, 0);
lean_dec(v_unused_2622_);
v___x_2555_ = v_r_2057_;
v_isShared_2556_ = v_isSharedCheck_2617_;
goto v_resetjp_2554_;
}
else
{
lean_dec(v_r_2057_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2617_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v_size_2557_; lean_object* v_k_2558_; lean_object* v_v_2559_; lean_object* v_l_2560_; lean_object* v_r_2561_; lean_object* v_size_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v_size_2557_ = lean_ctor_get(v_l_2544_, 0);
v_k_2558_ = lean_ctor_get(v_l_2544_, 1);
v_v_2559_ = lean_ctor_get(v_l_2544_, 2);
v_l_2560_ = lean_ctor_get(v_l_2544_, 3);
v_r_2561_ = lean_ctor_get(v_l_2544_, 4);
v_size_2562_ = lean_ctor_get(v_r_2545_, 0);
v___x_2563_ = lean_unsigned_to_nat(2u);
v___x_2564_ = lean_nat_mul(v___x_2563_, v_size_2562_);
v___x_2565_ = lean_nat_dec_lt(v_size_2557_, v___x_2564_);
lean_dec(v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2593_; 
lean_inc(v_r_2561_);
lean_inc(v_l_2560_);
lean_inc(v_v_2559_);
lean_inc(v_k_2558_);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_l_2544_);
if (v_isSharedCheck_2593_ == 0)
{
lean_object* v_unused_2594_; lean_object* v_unused_2595_; lean_object* v_unused_2596_; lean_object* v_unused_2597_; lean_object* v_unused_2598_; 
v_unused_2594_ = lean_ctor_get(v_l_2544_, 4);
lean_dec(v_unused_2594_);
v_unused_2595_ = lean_ctor_get(v_l_2544_, 3);
lean_dec(v_unused_2595_);
v_unused_2596_ = lean_ctor_get(v_l_2544_, 2);
lean_dec(v_unused_2596_);
v_unused_2597_ = lean_ctor_get(v_l_2544_, 1);
lean_dec(v_unused_2597_);
v_unused_2598_ = lean_ctor_get(v_l_2544_, 0);
lean_dec(v_unused_2598_);
v___x_2567_ = v_l_2544_;
v_isShared_2568_ = v_isSharedCheck_2593_;
goto v_resetjp_2566_;
}
else
{
lean_dec(v_l_2544_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2593_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2583_; 
v___x_2569_ = lean_nat_add(v___x_2539_, v_size_2540_);
v___x_2570_ = lean_nat_add(v___x_2569_, v_size_2541_);
lean_dec(v_size_2541_);
if (lean_obj_tag(v_l_2560_) == 0)
{
lean_object* v_size_2591_; 
v_size_2591_ = lean_ctor_get(v_l_2560_, 0);
lean_inc(v_size_2591_);
v___y_2583_ = v_size_2591_;
goto v___jp_2582_;
}
else
{
lean_object* v___x_2592_; 
v___x_2592_ = lean_unsigned_to_nat(0u);
v___y_2583_ = v___x_2592_;
goto v___jp_2582_;
}
v___jp_2571_:
{
lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2575_ = lean_nat_add(v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec(v___y_2573_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 4, v_r_2545_);
lean_ctor_set(v___x_2567_, 3, v_r_2561_);
lean_ctor_set(v___x_2567_, 2, v_v_2543_);
lean_ctor_set(v___x_2567_, 1, v_k_2542_);
lean_ctor_set(v___x_2567_, 0, v___x_2575_);
v___x_2577_ = v___x_2567_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_k_2542_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_v_2543_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_r_2561_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_r_2545_);
v___x_2577_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 4, v___x_2577_);
lean_ctor_set(v___x_2555_, 3, v___y_2572_);
lean_ctor_set(v___x_2555_, 2, v_v_2559_);
lean_ctor_set(v___x_2555_, 1, v_k_2558_);
lean_ctor_set(v___x_2555_, 0, v___x_2570_);
v___x_2579_ = v___x_2555_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v_k_2558_);
lean_ctor_set(v_reuseFailAlloc_2580_, 2, v_v_2559_);
lean_ctor_set(v_reuseFailAlloc_2580_, 3, v___y_2572_);
lean_ctor_set(v_reuseFailAlloc_2580_, 4, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
v___jp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2586_; 
v___x_2584_ = lean_nat_add(v___x_2569_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec(v___x_2569_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_l_2560_);
lean_ctor_set(v___x_2059_, 3, v_impl_2538_);
lean_ctor_set(v___x_2059_, 0, v___x_2584_);
v___x_2586_ = v___x_2059_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_impl_2538_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_l_2560_);
v___x_2586_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_nat_add(v___x_2539_, v_size_2562_);
if (lean_obj_tag(v_r_2561_) == 0)
{
lean_object* v_size_2588_; 
v_size_2588_ = lean_ctor_get(v_r_2561_, 0);
lean_inc(v_size_2588_);
v___y_2572_ = v___x_2586_;
v___y_2573_ = v___x_2587_;
v___y_2574_ = v_size_2588_;
goto v___jp_2571_;
}
else
{
lean_object* v___x_2589_; 
v___x_2589_ = lean_unsigned_to_nat(0u);
v___y_2572_ = v___x_2586_;
v___y_2573_ = v___x_2587_;
v___y_2574_ = v___x_2589_;
goto v___jp_2571_;
}
}
}
}
}
else
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
lean_del_object(v___x_2059_);
v___x_2599_ = lean_nat_add(v___x_2539_, v_size_2540_);
v___x_2600_ = lean_nat_add(v___x_2599_, v_size_2541_);
lean_dec(v_size_2541_);
v___x_2601_ = lean_nat_add(v___x_2599_, v_size_2557_);
lean_dec(v___x_2599_);
lean_inc_ref(v_impl_2538_);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 4, v_l_2544_);
lean_ctor_set(v___x_2555_, 3, v_impl_2538_);
lean_ctor_set(v___x_2555_, 2, v_v_2055_);
lean_ctor_set(v___x_2555_, 1, v_k_2054_);
lean_ctor_set(v___x_2555_, 0, v___x_2601_);
v___x_2603_ = v___x_2555_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2616_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2616_, 3, v_impl_2538_);
lean_ctor_set(v_reuseFailAlloc_2616_, 4, v_l_2544_);
v___x_2603_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
v_isSharedCheck_2610_ = !lean_is_exclusive(v_impl_2538_);
if (v_isSharedCheck_2610_ == 0)
{
lean_object* v_unused_2611_; lean_object* v_unused_2612_; lean_object* v_unused_2613_; lean_object* v_unused_2614_; lean_object* v_unused_2615_; 
v_unused_2611_ = lean_ctor_get(v_impl_2538_, 4);
lean_dec(v_unused_2611_);
v_unused_2612_ = lean_ctor_get(v_impl_2538_, 3);
lean_dec(v_unused_2612_);
v_unused_2613_ = lean_ctor_get(v_impl_2538_, 2);
lean_dec(v_unused_2613_);
v_unused_2614_ = lean_ctor_get(v_impl_2538_, 1);
lean_dec(v_unused_2614_);
v_unused_2615_ = lean_ctor_get(v_impl_2538_, 0);
lean_dec(v_unused_2615_);
v___x_2605_ = v_impl_2538_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_dec(v_impl_2538_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 4, v_r_2545_);
lean_ctor_set(v___x_2605_, 3, v___x_2603_);
lean_ctor_set(v___x_2605_, 2, v_v_2543_);
lean_ctor_set(v___x_2605_, 1, v_k_2542_);
lean_ctor_set(v___x_2605_, 0, v___x_2600_);
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_k_2542_);
lean_ctor_set(v_reuseFailAlloc_2609_, 2, v_v_2543_);
lean_ctor_set(v_reuseFailAlloc_2609_, 3, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2609_, 4, v_r_2545_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v_size_2623_ = lean_ctor_get(v_impl_2538_, 0);
v___x_2624_ = lean_nat_add(v___x_2539_, v_size_2623_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 3, v_impl_2538_);
lean_ctor_set(v___x_2059_, 0, v___x_2624_);
v___x_2626_ = v___x_2059_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2624_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2627_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2627_, 3, v_impl_2538_);
lean_ctor_set(v_reuseFailAlloc_2627_, 4, v_r_2057_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
else
{
if (lean_obj_tag(v_r_2057_) == 0)
{
lean_object* v_l_2628_; 
v_l_2628_ = lean_ctor_get(v_r_2057_, 3);
lean_inc(v_l_2628_);
if (lean_obj_tag(v_l_2628_) == 0)
{
lean_object* v_r_2629_; 
v_r_2629_ = lean_ctor_get(v_r_2057_, 4);
lean_inc(v_r_2629_);
if (lean_obj_tag(v_r_2629_) == 0)
{
lean_object* v_size_2630_; lean_object* v_k_2631_; lean_object* v_v_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2645_; 
v_size_2630_ = lean_ctor_get(v_r_2057_, 0);
v_k_2631_ = lean_ctor_get(v_r_2057_, 1);
v_v_2632_ = lean_ctor_get(v_r_2057_, 2);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_r_2057_);
if (v_isSharedCheck_2645_ == 0)
{
lean_object* v_unused_2646_; lean_object* v_unused_2647_; 
v_unused_2646_ = lean_ctor_get(v_r_2057_, 4);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_r_2057_, 3);
lean_dec(v_unused_2647_);
v___x_2634_ = v_r_2057_;
v_isShared_2635_ = v_isSharedCheck_2645_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_v_2632_);
lean_inc(v_k_2631_);
lean_inc(v_size_2630_);
lean_dec(v_r_2057_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2645_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v_size_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
v_size_2636_ = lean_ctor_get(v_l_2628_, 0);
v___x_2637_ = lean_nat_add(v___x_2539_, v_size_2630_);
lean_dec(v_size_2630_);
v___x_2638_ = lean_nat_add(v___x_2539_, v_size_2636_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 4, v_l_2628_);
lean_ctor_set(v___x_2634_, 3, v_impl_2538_);
lean_ctor_set(v___x_2634_, 2, v_v_2055_);
lean_ctor_set(v___x_2634_, 1, v_k_2054_);
lean_ctor_set(v___x_2634_, 0, v___x_2638_);
v___x_2640_ = v___x_2634_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2638_);
lean_ctor_set(v_reuseFailAlloc_2644_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2644_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2644_, 3, v_impl_2538_);
lean_ctor_set(v_reuseFailAlloc_2644_, 4, v_l_2628_);
v___x_2640_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2642_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_r_2629_);
lean_ctor_set(v___x_2059_, 3, v___x_2640_);
lean_ctor_set(v___x_2059_, 2, v_v_2632_);
lean_ctor_set(v___x_2059_, 1, v_k_2631_);
lean_ctor_set(v___x_2059_, 0, v___x_2637_);
v___x_2642_ = v___x_2059_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2643_, 1, v_k_2631_);
lean_ctor_set(v_reuseFailAlloc_2643_, 2, v_v_2632_);
lean_ctor_set(v_reuseFailAlloc_2643_, 3, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2643_, 4, v_r_2629_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_k_2648_; lean_object* v_v_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2672_; 
v_k_2648_ = lean_ctor_get(v_r_2057_, 1);
v_v_2649_ = lean_ctor_get(v_r_2057_, 2);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_r_2057_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; lean_object* v_unused_2674_; lean_object* v_unused_2675_; 
v_unused_2673_ = lean_ctor_get(v_r_2057_, 4);
lean_dec(v_unused_2673_);
v_unused_2674_ = lean_ctor_get(v_r_2057_, 3);
lean_dec(v_unused_2674_);
v_unused_2675_ = lean_ctor_get(v_r_2057_, 0);
lean_dec(v_unused_2675_);
v___x_2651_ = v_r_2057_;
v_isShared_2652_ = v_isSharedCheck_2672_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_v_2649_);
lean_inc(v_k_2648_);
lean_dec(v_r_2057_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2672_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v_k_2653_; lean_object* v_v_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2668_; 
v_k_2653_ = lean_ctor_get(v_l_2628_, 1);
v_v_2654_ = lean_ctor_get(v_l_2628_, 2);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_l_2628_);
if (v_isSharedCheck_2668_ == 0)
{
lean_object* v_unused_2669_; lean_object* v_unused_2670_; lean_object* v_unused_2671_; 
v_unused_2669_ = lean_ctor_get(v_l_2628_, 4);
lean_dec(v_unused_2669_);
v_unused_2670_ = lean_ctor_get(v_l_2628_, 3);
lean_dec(v_unused_2670_);
v_unused_2671_ = lean_ctor_get(v_l_2628_, 0);
lean_dec(v_unused_2671_);
v___x_2656_ = v_l_2628_;
v_isShared_2657_ = v_isSharedCheck_2668_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_v_2654_);
lean_inc(v_k_2653_);
lean_dec(v_l_2628_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2668_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = lean_unsigned_to_nat(3u);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 4, v_r_2629_);
lean_ctor_set(v___x_2656_, 3, v_r_2629_);
lean_ctor_set(v___x_2656_, 2, v_v_2055_);
lean_ctor_set(v___x_2656_, 1, v_k_2054_);
lean_ctor_set(v___x_2656_, 0, v___x_2539_);
v___x_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2667_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2667_, 3, v_r_2629_);
lean_ctor_set(v_reuseFailAlloc_2667_, 4, v_r_2629_);
v___x_2660_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
lean_object* v___x_2662_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 3, v_r_2629_);
lean_ctor_set(v___x_2651_, 0, v___x_2539_);
v___x_2662_ = v___x_2651_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_k_2648_);
lean_ctor_set(v_reuseFailAlloc_2666_, 2, v_v_2649_);
lean_ctor_set(v_reuseFailAlloc_2666_, 3, v_r_2629_);
lean_ctor_set(v_reuseFailAlloc_2666_, 4, v_r_2629_);
v___x_2662_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
lean_object* v___x_2664_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v___x_2662_);
lean_ctor_set(v___x_2059_, 3, v___x_2660_);
lean_ctor_set(v___x_2059_, 2, v_v_2654_);
lean_ctor_set(v___x_2059_, 1, v_k_2653_);
lean_ctor_set(v___x_2059_, 0, v___x_2658_);
v___x_2664_ = v___x_2059_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2658_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_k_2653_);
lean_ctor_set(v_reuseFailAlloc_2665_, 2, v_v_2654_);
lean_ctor_set(v_reuseFailAlloc_2665_, 3, v___x_2660_);
lean_ctor_set(v_reuseFailAlloc_2665_, 4, v___x_2662_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_2676_; 
v_r_2676_ = lean_ctor_get(v_r_2057_, 4);
lean_inc(v_r_2676_);
if (lean_obj_tag(v_r_2676_) == 0)
{
lean_object* v_k_2677_; lean_object* v_v_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2689_; 
v_k_2677_ = lean_ctor_get(v_r_2057_, 1);
v_v_2678_ = lean_ctor_get(v_r_2057_, 2);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_r_2057_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; lean_object* v_unused_2691_; lean_object* v_unused_2692_; 
v_unused_2690_ = lean_ctor_get(v_r_2057_, 4);
lean_dec(v_unused_2690_);
v_unused_2691_ = lean_ctor_get(v_r_2057_, 3);
lean_dec(v_unused_2691_);
v_unused_2692_ = lean_ctor_get(v_r_2057_, 0);
lean_dec(v_unused_2692_);
v___x_2680_ = v_r_2057_;
v_isShared_2681_ = v_isSharedCheck_2689_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_v_2678_);
lean_inc(v_k_2677_);
lean_dec(v_r_2057_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2689_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2682_ = lean_unsigned_to_nat(3u);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 4, v_l_2628_);
lean_ctor_set(v___x_2680_, 2, v_v_2055_);
lean_ctor_set(v___x_2680_, 1, v_k_2054_);
lean_ctor_set(v___x_2680_, 0, v___x_2539_);
v___x_2684_ = v___x_2680_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2688_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2688_, 3, v_l_2628_);
lean_ctor_set(v_reuseFailAlloc_2688_, 4, v_l_2628_);
v___x_2684_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2686_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_r_2676_);
lean_ctor_set(v___x_2059_, 3, v___x_2684_);
lean_ctor_set(v___x_2059_, 2, v_v_2678_);
lean_ctor_set(v___x_2059_, 1, v_k_2677_);
lean_ctor_set(v___x_2059_, 0, v___x_2682_);
v___x_2686_ = v___x_2059_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_k_2677_);
lean_ctor_set(v_reuseFailAlloc_2687_, 2, v_v_2678_);
lean_ctor_set(v_reuseFailAlloc_2687_, 3, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2687_, 4, v_r_2676_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_object* v_size_2693_; lean_object* v_k_2694_; lean_object* v_v_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2706_; 
v_size_2693_ = lean_ctor_get(v_r_2057_, 0);
v_k_2694_ = lean_ctor_get(v_r_2057_, 1);
v_v_2695_ = lean_ctor_get(v_r_2057_, 2);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_r_2057_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; lean_object* v_unused_2708_; 
v_unused_2707_ = lean_ctor_get(v_r_2057_, 4);
lean_dec(v_unused_2707_);
v_unused_2708_ = lean_ctor_get(v_r_2057_, 3);
lean_dec(v_unused_2708_);
v___x_2697_ = v_r_2057_;
v_isShared_2698_ = v_isSharedCheck_2706_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_v_2695_);
lean_inc(v_k_2694_);
lean_inc(v_size_2693_);
lean_dec(v_r_2057_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2706_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 3, v_r_2676_);
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_size_2693_);
lean_ctor_set(v_reuseFailAlloc_2705_, 1, v_k_2694_);
lean_ctor_set(v_reuseFailAlloc_2705_, 2, v_v_2695_);
lean_ctor_set(v_reuseFailAlloc_2705_, 3, v_r_2676_);
lean_ctor_set(v_reuseFailAlloc_2705_, 4, v_r_2676_);
v___x_2700_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2701_ = lean_unsigned_to_nat(2u);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v___x_2700_);
lean_ctor_set(v___x_2059_, 3, v_r_2676_);
lean_ctor_set(v___x_2059_, 0, v___x_2701_);
v___x_2703_ = v___x_2059_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v_r_2676_);
lean_ctor_set(v_reuseFailAlloc_2704_, 4, v___x_2700_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
else
{
lean_object* v___x_2710_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 3, v_r_2057_);
lean_ctor_set(v___x_2059_, 0, v___x_2539_);
v___x_2710_ = v___x_2059_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2539_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2711_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2711_, 3, v_r_2057_);
lean_ctor_set(v_reuseFailAlloc_2711_, 4, v_r_2057_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
}
}
}
}
else
{
return v_t_2053_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg___boxed(lean_object* v_k_2714_, lean_object* v_t_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2714_, v_t_2715_);
lean_dec(v_k_2714_);
return v_res_2716_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(lean_object* v_id_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; lean_object* v_receivers_2726_; lean_object* v___x_2727_; 
v___x_2725_ = lean_st_ref_get(v___y_2723_);
v_receivers_2726_ = lean_ctor_get(v___x_2725_, 7);
v___x_2727_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_2726_, v_id_2722_);
if (lean_obj_tag(v___x_2727_) == 1)
{
lean_object* v_val_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_val_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_val_2728_);
lean_dec_ref_known(v___x_2727_, 1);
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2725_);
lean_ctor_set(v___x_2729_, 1, v_val_2728_);
v___x_2730_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v___x_2729_, v___y_2723_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2760_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2760_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2760_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v_fst_2735_; lean_object* v_producers_2736_; lean_object* v_waiters_2737_; lean_object* v_capacity_2738_; lean_object* v_size_2739_; lean_object* v_buffer_2740_; lean_object* v_write_2741_; lean_object* v_read_2742_; lean_object* v_receivers_2743_; lean_object* v_nextId_2744_; uint8_t v_closed_2745_; lean_object* v_pos_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2759_; 
v_fst_2735_ = lean_ctor_get(v_a_2731_, 0);
lean_inc(v_fst_2735_);
lean_dec(v_a_2731_);
v_producers_2736_ = lean_ctor_get(v_fst_2735_, 0);
v_waiters_2737_ = lean_ctor_get(v_fst_2735_, 1);
v_capacity_2738_ = lean_ctor_get(v_fst_2735_, 2);
v_size_2739_ = lean_ctor_get(v_fst_2735_, 3);
v_buffer_2740_ = lean_ctor_get(v_fst_2735_, 4);
v_write_2741_ = lean_ctor_get(v_fst_2735_, 5);
v_read_2742_ = lean_ctor_get(v_fst_2735_, 6);
v_receivers_2743_ = lean_ctor_get(v_fst_2735_, 7);
v_nextId_2744_ = lean_ctor_get(v_fst_2735_, 8);
v_closed_2745_ = lean_ctor_get_uint8(v_fst_2735_, sizeof(void*)*10);
v_pos_2746_ = lean_ctor_get(v_fst_2735_, 9);
v_isSharedCheck_2759_ = !lean_is_exclusive(v_fst_2735_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2748_ = v_fst_2735_;
v_isShared_2749_ = v_isSharedCheck_2759_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_pos_2746_);
lean_inc(v_nextId_2744_);
lean_inc(v_receivers_2743_);
lean_inc(v_read_2742_);
lean_inc(v_write_2741_);
lean_inc(v_buffer_2740_);
lean_inc(v_size_2739_);
lean_inc(v_capacity_2738_);
lean_inc(v_waiters_2737_);
lean_inc(v_producers_2736_);
lean_dec(v_fst_2735_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2759_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2750_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_id_2722_, v_receivers_2743_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 7, v___x_2750_);
v___x_2752_ = v___x_2748_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_producers_2736_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_waiters_2737_);
lean_ctor_set(v_reuseFailAlloc_2758_, 2, v_capacity_2738_);
lean_ctor_set(v_reuseFailAlloc_2758_, 3, v_size_2739_);
lean_ctor_set(v_reuseFailAlloc_2758_, 4, v_buffer_2740_);
lean_ctor_set(v_reuseFailAlloc_2758_, 5, v_write_2741_);
lean_ctor_set(v_reuseFailAlloc_2758_, 6, v_read_2742_);
lean_ctor_set(v_reuseFailAlloc_2758_, 7, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2758_, 8, v_nextId_2744_);
lean_ctor_set(v_reuseFailAlloc_2758_, 9, v_pos_2746_);
lean_ctor_set_uint8(v_reuseFailAlloc_2758_, sizeof(void*)*10, v_closed_2745_);
v___x_2752_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2753_ = lean_st_ref_swap(v___y_2723_, v___x_2752_);
lean_dec(v___x_2753_);
v___x_2754_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__0));
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2754_);
v___x_2756_ = v___x_2733_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
v_a_2761_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2730_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2730_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
lean_dec(v___x_2727_);
lean_dec(v___x_2725_);
v___x_2769_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___closed__1));
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2769_);
return v___x_2770_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_2722_ = stack[0].m_obj;
lean_object* v___y_2723_ = stack[1].m_obj;
lean_object* v_res_2771_;
v_res_2771_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(v_id_2722_, v___y_2723_);
stack->m_obj
 = v_res_2771_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed(lean_object* v_id_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0(v_id_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec(v_id_2772_);
return v_res_2775_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(lean_object* v_bd_2776_){
_start:
{
lean_object* v_state_2778_; lean_object* v_id_2779_; lean_object* v___f_2780_; lean_object* v___x_2781_; 
v_state_2778_ = lean_ctor_get(v_bd_2776_, 0);
lean_inc_ref(v_state_2778_);
v_id_2779_ = lean_ctor_get(v_bd_2776_, 1);
lean_inc(v_id_2779_);
lean_dec_ref(v_bd_2776_);
v___f_2780_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2780_, 0, v_id_2779_);
v___x_2781_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_2778_, v___f_2780_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2806_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2806_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2806_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___y_2787_; 
if (lean_obj_tag(v_a_2782_) == 0)
{
lean_object* v_a_2792_; uint8_t v___x_2793_; 
v_a_2792_ = lean_ctor_get(v_a_2782_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v_a_2782_, 1);
v___x_2793_ = lean_unbox(v_a_2792_);
lean_dec(v_a_2792_);
switch(v___x_2793_)
{
case 0:
{
lean_object* v___x_2794_; 
v___x_2794_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_2787_ = v___x_2794_;
goto v___jp_2786_;
}
case 1:
{
lean_object* v___x_2795_; 
v___x_2795_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_2787_ = v___x_2795_;
goto v___jp_2786_;
}
default: 
{
lean_object* v___x_2796_; 
v___x_2796_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_2787_ = v___x_2796_;
goto v___jp_2786_;
}
}
}
else
{
lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2804_; 
lean_del_object(v___x_2784_);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_a_2782_);
if (v_isSharedCheck_2804_ == 0)
{
lean_object* v_unused_2805_; 
v_unused_2805_ = lean_ctor_get(v_a_2782_, 0);
lean_dec(v_unused_2805_);
v___x_2798_ = v_a_2782_;
v_isShared_2799_ = v_isSharedCheck_2804_;
goto v_resetjp_2797_;
}
else
{
lean_dec(v_a_2782_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2804_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2802_; 
v___x_2800_ = lean_box(0);
if (v_isShared_2799_ == 0)
{
lean_ctor_set_tag(v___x_2798_, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2800_);
v___x_2802_ = v___x_2798_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v___x_2800_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
}
v___jp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2790_; 
lean_inc_ref(v___y_2787_);
v___x_2788_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___y_2787_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set_tag(v___x_2784_, 1);
lean_ctor_set(v___x_2784_, 0, v___x_2788_);
v___x_2790_ = v___x_2784_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2788_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
v_a_2807_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2781_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2781_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_bd_2776_ = stack[0].m_obj;
lean_object* v_res_2815_;
v_res_2815_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2776_);
stack->m_obj
 = v_res_2815_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg___boxed(lean_object* v_bd_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2816_);
return v_res_2818_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(lean_object* v_00_u03b1_2819_, lean_object* v_bd_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_bd_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_0interp(lean_interpreter_value* stack)
{
lean_object* v_bd_2820_ = stack[1].m_obj;
lean_object* v_res_2823_;
v_res_2823_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(lean_box(0), v_bd_2820_);
stack->m_obj
 = v_res_2823_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_2824_, lean_object* v_bd_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe(v_00_u03b1_2824_, v_bd_2825_);
return v_res_2827_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(lean_object* v_00_u03b1_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___redArg(v_a_2829_);
return v___x_2831_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2829_ = stack[1].m_obj;
lean_object* v_res_2832_;
v_res_2832_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(lean_box(0), v_a_2829_);
stack->m_obj
 = v_res_2832_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2833_, lean_object* v_a_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__0(v_00_u03b1_2833_, v_a_2834_);
lean_dec(v_a_2834_);
return v_res_2836_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(lean_object* v_00_u03b1_2837_, lean_object* v_place_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v_place_2838_, v_a_2839_);
return v___x_2841_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_place_2838_ = stack[1].m_obj;
lean_object* v_a_2839_ = stack[2].m_obj;
lean_object* v_res_2842_;
v_res_2842_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(lean_box(0), v_place_2838_, v_a_2839_);
stack->m_obj
 = v_res_2842_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2843_, lean_object* v_place_2844_, lean_object* v_a_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_res_2847_; 
v_res_2847_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1(v_00_u03b1_2843_, v_place_2844_, v_a_2845_);
lean_dec(v_a_2845_);
lean_dec(v_place_2844_);
return v_res_2847_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(lean_object* v_00_u03b1_2848_, lean_object* v_slot_2849_, lean_object* v_next_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___redArg(v_slot_2849_, v_next_2850_);
return v___x_2853_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_slot_2849_ = stack[1].m_obj;
lean_object* v_next_2850_ = stack[2].m_obj;
lean_object* v_a_2851_ = stack[3].m_obj;
lean_object* v_res_2854_;
v_res_2854_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(lean_box(0), v_slot_2849_, v_next_2850_, v_a_2851_);
stack->m_obj
 = v_res_2854_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2855_, lean_object* v_slot_2856_, lean_object* v_next_2857_, lean_object* v_a_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__2(v_00_u03b1_2855_, v_slot_2856_, v_next_2857_, v_a_2858_);
lean_dec(v_a_2858_);
lean_dec(v_next_2857_);
lean_dec(v_slot_2856_);
return v_res_2860_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(lean_object* v_00_u03b1_2861_, lean_object* v_next_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_next_2862_, v_a_2863_);
return v___x_2865_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_next_2862_ = stack[1].m_obj;
lean_object* v_a_2863_ = stack[2].m_obj;
lean_object* v_res_2866_;
v_res_2866_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(lean_box(0), v_next_2862_, v_a_2863_);
stack->m_obj
 = v_res_2866_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___boxed(lean_object* v_00_u03b1_2867_, lean_object* v_next_2868_, lean_object* v_a_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0(v_00_u03b1_2867_, v_next_2868_, v_a_2869_);
lean_dec(v_a_2869_);
lean_dec(v_next_2868_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(lean_object* v_00_u03b4_2872_, lean_object* v_t_2873_, lean_object* v_k_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_t_2873_, v_k_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___boxed(lean_object* v_00_u03b4_2876_, lean_object* v_t_2877_, lean_object* v_k_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1(v_00_u03b4_2876_, v_t_2877_, v_k_2878_);
lean_dec(v_k_2878_);
lean_dec(v_t_2877_);
return v_res_2879_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_object* v_00_u03b1_2880_, lean_object* v_inst_2881_, lean_object* v_a_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___redArg(v_a_2882_, v___y_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2882_ = stack[2].m_obj;
lean_object* v___y_2883_ = stack[3].m_obj;
lean_object* v_res_2886_;
v_res_2886_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(lean_box(0), lean_box(0), v_a_2882_, v___y_2883_);
stack->m_obj
 = v_res_2886_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2___boxed(lean_object* v_00_u03b1_2887_, lean_object* v_inst_2888_, lean_object* v_a_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l___private_Init_While_0__repeatM_erased___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__2(v_00_u03b1_2887_, v_inst_2888_, v_a_2889_, v___y_2890_);
lean_dec(v___y_2890_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(lean_object* v_00_u03b2_2893_, lean_object* v_k_2894_, lean_object* v_t_2895_, lean_object* v_h_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___redArg(v_k_2894_, v_t_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3___boxed(lean_object* v_00_u03b2_2898_, lean_object* v_k_2899_, lean_object* v_t_2900_, lean_object* v_h_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__3(v_00_u03b2_2898_, v_k_2899_, v_t_2900_, v_h_2901_);
lean_dec(v_k_2899_);
return v_res_2902_;
}
}
uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(lean_object* v_x_2903_, lean_object* v_y_2904_){
_start:
{
uint8_t v___x_2905_; 
v___x_2905_ = lean_nat_dec_lt(v_x_2903_, v_y_2904_);
if (v___x_2905_ == 0)
{
uint8_t v___x_2906_; 
v___x_2906_ = lean_nat_dec_eq(v_x_2903_, v_y_2904_);
if (v___x_2906_ == 0)
{
uint8_t v___x_2907_; 
v___x_2907_ = 2;
return v___x_2907_;
}
else
{
uint8_t v___x_2908_; 
v___x_2908_ = 1;
return v___x_2908_;
}
}
else
{
uint8_t v___x_2909_; 
v___x_2909_ = 0;
return v___x_2909_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2903_ = stack[0].m_obj;
lean_object* v_y_2904_ = stack[1].m_obj;
uint8_t v_res_2910_;
v_res_2910_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(v_x_2903_, v_y_2904_);
stack->m_num = v_res_2910_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0___boxed(lean_object* v_x_2911_, lean_object* v_y_2912_){
_start:
{
uint8_t v_res_2913_; lean_object* v_r_2914_; 
v_res_2913_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__0(v_x_2911_, v_y_2912_);
lean_dec(v_y_2912_);
lean_dec(v_x_2911_);
v_r_2914_ = lean_box(v_res_2913_);
return v_r_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(lean_object* v_x_2915_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_unsigned_to_nat(1u);
v___x_2917_ = lean_nat_add(v_x_2915_, v___x_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1___boxed(lean_object* v_x_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__1(v_x_2918_);
lean_dec(v_x_2918_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3(lean_object* v___f_2920_, lean_object* v_receiverId_2921_, lean_object* v___f_2922_, lean_object* v_receivers_2923_, lean_object* v_s_2924_){
_start:
{
lean_object* v_producers_2925_; lean_object* v_waiters_2926_; lean_object* v_capacity_2927_; lean_object* v_size_2928_; lean_object* v_buffer_2929_; lean_object* v_write_2930_; lean_object* v_read_2931_; lean_object* v_nextId_2932_; uint8_t v_closed_2933_; lean_object* v_pos_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2944_; 
v_producers_2925_ = lean_ctor_get(v_s_2924_, 0);
v_waiters_2926_ = lean_ctor_get(v_s_2924_, 1);
v_capacity_2927_ = lean_ctor_get(v_s_2924_, 2);
v_size_2928_ = lean_ctor_get(v_s_2924_, 3);
v_buffer_2929_ = lean_ctor_get(v_s_2924_, 4);
v_write_2930_ = lean_ctor_get(v_s_2924_, 5);
v_read_2931_ = lean_ctor_get(v_s_2924_, 6);
v_nextId_2932_ = lean_ctor_get(v_s_2924_, 8);
v_closed_2933_ = lean_ctor_get_uint8(v_s_2924_, sizeof(void*)*10);
v_pos_2934_ = lean_ctor_get(v_s_2924_, 9);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_s_2924_);
if (v_isSharedCheck_2944_ == 0)
{
lean_object* v_unused_2945_; 
v_unused_2945_ = lean_ctor_get(v_s_2924_, 7);
lean_dec(v_unused_2945_);
v___x_2936_ = v_s_2924_;
v_isShared_2937_ = v_isSharedCheck_2944_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_pos_2934_);
lean_inc(v_nextId_2932_);
lean_inc(v_read_2931_);
lean_inc(v_write_2930_);
lean_inc(v_buffer_2929_);
lean_inc(v_size_2928_);
lean_inc(v_capacity_2927_);
lean_inc(v_waiters_2926_);
lean_inc(v_producers_2925_);
lean_dec(v_s_2924_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2944_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2941_; 
v___x_2938_ = lean_box(0);
v___x_2939_ = l_Std_DTreeMap_Internal_Impl_Const_modify___redArg(v___f_2920_, v_receiverId_2921_, v___f_2922_, v_receivers_2923_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 7, v___x_2939_);
v___x_2941_ = v___x_2936_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_producers_2925_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_waiters_2926_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_capacity_2927_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_size_2928_);
lean_ctor_set(v_reuseFailAlloc_2943_, 4, v_buffer_2929_);
lean_ctor_set(v_reuseFailAlloc_2943_, 5, v_write_2930_);
lean_ctor_set(v_reuseFailAlloc_2943_, 6, v_read_2931_);
lean_ctor_set(v_reuseFailAlloc_2943_, 7, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2943_, 8, v_nextId_2932_);
lean_ctor_set(v_reuseFailAlloc_2943_, 9, v_pos_2934_);
lean_ctor_set_uint8(v_reuseFailAlloc_2943_, sizeof(void*)*10, v_closed_2933_);
v___x_2941_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2938_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2(lean_object* v_toApplicative_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_toPure_2949_; lean_object* v___x_2950_; 
v_toPure_2949_ = lean_ctor_get(v_toApplicative_2946_, 1);
lean_inc(v_toPure_2949_);
lean_dec_ref(v_toApplicative_2946_);
v___x_2950_ = lean_apply_2(v_toPure_2949_, lean_box(0), v_a_2947_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(lean_object* v_toApplicative_2951_, lean_object* v_a_2952_, lean_object* v___f_2953_, lean_object* v_inst_2954_, lean_object* v_toBind_2955_, lean_object* v_a_2956_){
_start:
{
if (lean_obj_tag(v_a_2956_) == 1)
{
lean_object* v___f_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___f_2957_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2957_, 0, v_toApplicative_2951_);
lean_closure_set(v___f_2957_, 1, v_a_2956_);
lean_inc(v_a_2952_);
v___x_2958_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_2958_, 0, lean_box(0));
lean_closure_set(v___x_2958_, 1, lean_box(0));
lean_closure_set(v___x_2958_, 2, lean_box(0));
lean_closure_set(v___x_2958_, 3, v_a_2952_);
lean_closure_set(v___x_2958_, 4, v___f_2953_);
v___x_2959_ = lean_apply_2(v_inst_2954_, lean_box(0), v___x_2958_);
v___x_2960_ = lean_apply_4(v_toBind_2955_, lean_box(0), lean_box(0), v___x_2959_, v___f_2957_);
return v___x_2960_;
}
else
{
lean_object* v_toPure_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
lean_dec(v_a_2956_);
lean_dec(v_toBind_2955_);
lean_dec(v_inst_2954_);
lean_dec_ref(v___f_2953_);
v_toPure_2961_ = lean_ctor_get(v_toApplicative_2951_, 1);
lean_inc(v_toPure_2961_);
lean_dec_ref(v_toApplicative_2951_);
v___x_2962_ = lean_box(0);
v___x_2963_ = lean_apply_2(v_toPure_2961_, lean_box(0), v___x_2962_);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed(lean_object* v_toApplicative_2964_, lean_object* v_a_2965_, lean_object* v___f_2966_, lean_object* v_inst_2967_, lean_object* v_toBind_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4(v_toApplicative_2964_, v_a_2965_, v___f_2966_, v_inst_2967_, v_toBind_2968_, v_a_2969_);
lean_dec(v_a_2965_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(lean_object* v___f_2971_, lean_object* v_receiverId_2972_, lean_object* v___f_2973_, lean_object* v___f_2974_, lean_object* v_toApplicative_2975_, lean_object* v_a_2976_, lean_object* v_inst_2977_, lean_object* v_toBind_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_, lean_object* v_a_2981_){
_start:
{
lean_object* v_receivers_2982_; lean_object* v___x_2983_; 
v_receivers_2982_ = lean_ctor_get(v_a_2981_, 7);
lean_inc_n(v_receivers_2982_, 2);
lean_dec_ref(v_a_2981_);
lean_inc(v_receiverId_2972_);
v___x_2983_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2971_, v_receivers_2982_, v_receiverId_2972_);
if (lean_obj_tag(v___x_2983_) == 1)
{
lean_object* v_val_2984_; lean_object* v___f_2985_; lean_object* v___f_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_val_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_val_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___f_2985_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2985_, 0, v___f_2973_);
lean_closure_set(v___f_2985_, 1, v_receiverId_2972_);
lean_closure_set(v___f_2985_, 2, v___f_2974_);
lean_closure_set(v___f_2985_, 3, v_receivers_2982_);
lean_inc(v_toBind_2978_);
lean_inc(v_inst_2977_);
lean_inc(v_a_2976_);
v___f_2986_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_2986_, 0, v_toApplicative_2975_);
lean_closure_set(v___f_2986_, 1, v_a_2976_);
lean_closure_set(v___f_2986_, 2, v___f_2985_);
lean_closure_set(v___f_2986_, 3, v_inst_2977_);
lean_closure_set(v___f_2986_, 4, v_toBind_2978_);
v___x_2987_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___redArg(v_inst_2979_, v_inst_2977_, v_inst_2980_, v_val_2984_, v_a_2976_);
v___x_2988_ = lean_apply_4(v_toBind_2978_, lean_box(0), lean_box(0), v___x_2987_, v___f_2986_);
return v___x_2988_;
}
else
{
lean_object* v_toPure_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_dec(v___x_2983_);
lean_dec(v_receivers_2982_);
lean_dec(v_inst_2980_);
lean_dec_ref(v_inst_2979_);
lean_dec(v_toBind_2978_);
lean_dec(v_inst_2977_);
lean_dec_ref(v___f_2974_);
lean_dec_ref(v___f_2973_);
lean_dec(v_receiverId_2972_);
v_toPure_2989_ = lean_ctor_get(v_toApplicative_2975_, 1);
lean_inc(v_toPure_2989_);
lean_dec_ref(v_toApplicative_2975_);
v___x_2990_ = lean_box(0);
v___x_2991_ = lean_apply_2(v_toPure_2989_, lean_box(0), v___x_2990_);
return v___x_2991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed(lean_object* v___f_2992_, lean_object* v_receiverId_2993_, lean_object* v___f_2994_, lean_object* v___f_2995_, lean_object* v_toApplicative_2996_, lean_object* v_a_2997_, lean_object* v_inst_2998_, lean_object* v_toBind_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v_a_3002_){
_start:
{
lean_object* v_res_3003_; 
v_res_3003_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5(v___f_2992_, v_receiverId_2993_, v___f_2994_, v___f_2995_, v_toApplicative_2996_, v_a_2997_, v_inst_2998_, v_toBind_2999_, v_inst_3000_, v_inst_3001_, v_a_3002_);
lean_dec(v_a_2997_);
return v_res_3003_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(lean_object* v_inst_3006_, lean_object* v_inst_3007_, lean_object* v_inst_3008_, lean_object* v_receiverId_3009_, lean_object* v_a_3010_){
_start:
{
lean_object* v_toApplicative_3011_; lean_object* v_toBind_3012_; lean_object* v___f_3013_; lean_object* v___f_3014_; lean_object* v___f_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_toApplicative_3011_ = lean_ctor_get(v_inst_3006_, 0);
lean_inc_ref(v_toApplicative_3011_);
v_toBind_3012_ = lean_ctor_get(v_inst_3006_, 1);
lean_inc_n(v_toBind_3012_, 2);
v___f_3013_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
v___f_3014_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__1));
lean_inc(v_inst_3007_);
lean_inc_n(v_a_3010_, 2);
v___f_3015_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___lam__5___boxed), 11, 10);
lean_closure_set(v___f_3015_, 0, v___f_3013_);
lean_closure_set(v___f_3015_, 1, v_receiverId_3009_);
lean_closure_set(v___f_3015_, 2, v___f_3013_);
lean_closure_set(v___f_3015_, 3, v___f_3014_);
lean_closure_set(v___f_3015_, 4, v_toApplicative_3011_);
lean_closure_set(v___f_3015_, 5, v_a_3010_);
lean_closure_set(v___f_3015_, 6, v_inst_3007_);
lean_closure_set(v___f_3015_, 7, v_toBind_3012_);
lean_closure_set(v___f_3015_, 8, v_inst_3006_);
lean_closure_set(v___f_3015_, 9, v_inst_3008_);
v___x_3016_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3016_, 0, lean_box(0));
lean_closure_set(v___x_3016_, 1, lean_box(0));
lean_closure_set(v___x_3016_, 2, v_a_3010_);
v___x_3017_ = lean_apply_2(v_inst_3007_, lean_box(0), v___x_3016_);
v___x_3018_ = lean_apply_4(v_toBind_3012_, lean_box(0), lean_box(0), v___x_3017_, v___f_3015_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___boxed(lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_inst_3021_, lean_object* v_receiverId_3022_, lean_object* v_a_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_3019_, v_inst_3020_, v_inst_3021_, v_receiverId_3022_, v_a_3023_);
lean_dec(v_a_3023_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(lean_object* v_m_3025_, lean_object* v_00_u03b1_3026_, lean_object* v_inst_3027_, lean_object* v_inst_3028_, lean_object* v_inst_3029_, lean_object* v_receiverId_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg(v_inst_3027_, v_inst_3028_, v_inst_3029_, v_receiverId_3030_, v_a_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___boxed(lean_object* v_m_3033_, lean_object* v_00_u03b1_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_receiverId_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27(v_m_3033_, v_00_u03b1_3034_, v_inst_3035_, v_inst_3036_, v_inst_3037_, v_receiverId_3038_, v_a_3039_);
lean_dec(v_a_3039_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(lean_object* v_k_3041_, lean_object* v_t_3042_){
_start:
{
if (lean_obj_tag(v_t_3042_) == 0)
{
lean_object* v_size_3043_; lean_object* v_k_3044_; lean_object* v_v_3045_; lean_object* v_l_3046_; lean_object* v_r_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3066_; 
v_size_3043_ = lean_ctor_get(v_t_3042_, 0);
v_k_3044_ = lean_ctor_get(v_t_3042_, 1);
v_v_3045_ = lean_ctor_get(v_t_3042_, 2);
v_l_3046_ = lean_ctor_get(v_t_3042_, 3);
v_r_3047_ = lean_ctor_get(v_t_3042_, 4);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_t_3042_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3049_ = v_t_3042_;
v_isShared_3050_ = v_isSharedCheck_3066_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_r_3047_);
lean_inc(v_l_3046_);
lean_inc(v_v_3045_);
lean_inc(v_k_3044_);
lean_inc(v_size_3043_);
lean_dec(v_t_3042_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3066_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_nat_dec_lt(v_k_3041_, v_k_3044_);
if (v___x_3051_ == 0)
{
uint8_t v___x_3052_; 
v___x_3052_ = lean_nat_dec_eq(v_k_3041_, v_k_3044_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3053_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_3041_, v_r_3047_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 4, v___x_3053_);
v___x_3055_ = v___x_3049_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_size_3043_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_k_3044_);
lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_v_3045_);
lean_ctor_set(v_reuseFailAlloc_3056_, 3, v_l_3046_);
lean_ctor_set(v_reuseFailAlloc_3056_, 4, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
else
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3060_; 
lean_dec(v_k_3044_);
v___x_3057_ = lean_unsigned_to_nat(1u);
v___x_3058_ = lean_nat_add(v_v_3045_, v___x_3057_);
lean_dec(v_v_3045_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 2, v___x_3058_);
lean_ctor_set(v___x_3049_, 1, v_k_3041_);
v___x_3060_ = v___x_3049_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_size_3043_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_k_3041_);
lean_ctor_set(v_reuseFailAlloc_3061_, 2, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3061_, 3, v_l_3046_);
lean_ctor_set(v_reuseFailAlloc_3061_, 4, v_r_3047_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
else
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_k_3041_, v_l_3046_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 3, v___x_3062_);
v___x_3064_ = v___x_3049_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_size_3043_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_k_3044_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v_v_3045_);
lean_ctor_set(v_reuseFailAlloc_3065_, 3, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3065_, 4, v_r_3047_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
else
{
lean_dec(v_k_3041_);
return v_t_3042_;
}
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_3067_, lean_object* v_next_3068_){
_start:
{
lean_object* v___x_3070_; lean_object* v_fst_3072_; lean_object* v_snd_3073_; lean_object* v_value_3075_; lean_object* v_pos_3076_; lean_object* v_remaining_3077_; uint8_t v___x_3078_; 
v___x_3070_ = lean_st_ref_take(v_slot_3067_);
v_value_3075_ = lean_ctor_get(v___x_3070_, 0);
v_pos_3076_ = lean_ctor_get(v___x_3070_, 1);
v_remaining_3077_ = lean_ctor_get(v___x_3070_, 2);
v___x_3078_ = lean_nat_dec_eq(v_next_3068_, v_pos_3076_);
if (v___x_3078_ == 0)
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_box(0);
v___x_3080_ = lean_box(v___x_3078_);
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v_fst_3072_ = v___x_3081_;
v_snd_3073_ = v___x_3070_;
goto v___jp_3071_;
}
else
{
lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3100_; 
lean_inc(v_remaining_3077_);
lean_inc(v_pos_3076_);
lean_inc(v_value_3075_);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; lean_object* v_unused_3102_; lean_object* v_unused_3103_; 
v_unused_3101_ = lean_ctor_get(v___x_3070_, 2);
lean_dec(v_unused_3101_);
v_unused_3102_ = lean_ctor_get(v___x_3070_, 1);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v___x_3070_, 0);
lean_dec(v_unused_3103_);
v___x_3083_ = v___x_3070_;
v_isShared_3084_ = v_isSharedCheck_3100_;
goto v_resetjp_3082_;
}
else
{
lean_dec(v___x_3070_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3100_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3085_ = lean_unsigned_to_nat(1u);
v___x_3086_ = lean_nat_dec_eq(v_remaining_3077_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v___x_3087_ = lean_box(v___x_3086_);
lean_inc(v_value_3075_);
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v_value_3075_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = lean_nat_sub(v_remaining_3077_, v___x_3085_);
lean_dec(v_remaining_3077_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 2, v___x_3089_);
v___x_3091_ = v___x_3083_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_value_3075_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_pos_3076_);
lean_ctor_set(v_reuseFailAlloc_3092_, 2, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
v_fst_3072_ = v___x_3088_;
v_snd_3073_ = v___x_3091_;
goto v___jp_3071_;
}
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
lean_dec(v_remaining_3077_);
v___x_3093_ = lean_box(v___x_3078_);
v___x_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3094_, 0, v_value_3075_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
v___x_3095_ = lean_box(0);
v___x_3096_ = lean_unsigned_to_nat(0u);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 2, v___x_3096_);
lean_ctor_set(v___x_3083_, 0, v___x_3095_);
v___x_3098_ = v___x_3083_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3095_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_pos_3076_);
lean_ctor_set(v_reuseFailAlloc_3099_, 2, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
v_fst_3072_ = v___x_3094_;
v_snd_3073_ = v___x_3098_;
goto v___jp_3071_;
}
}
}
}
v___jp_3071_:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_st_ref_put(v_slot_3067_, v_snd_3073_);
return v_fst_3072_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_slot_3067_ = stack[0].m_obj;
lean_object* v_next_3068_ = stack[1].m_obj;
lean_object* v_res_3104_;
v_res_3104_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3067_, v_next_3068_);
stack->m_obj
 = v_res_3104_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_3105_, lean_object* v_next_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3105_, v_next_3106_);
lean_dec(v_next_3106_);
lean_dec(v_slot_3105_);
return v_res_3108_;
}
}
uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(lean_object* v_a_3109_){
_start:
{
lean_object* v___x_3111_; lean_object* v_size_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v___x_3111_ = lean_st_ref_get(v_a_3109_);
v_size_3112_ = lean_ctor_get(v___x_3111_, 3);
lean_inc(v_size_3112_);
lean_dec(v___x_3111_);
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = lean_nat_dec_eq(v_size_3112_, v___x_3113_);
lean_dec(v_size_3112_);
return v___x_3114_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3109_ = stack[0].m_obj;
uint8_t v_res_3115_;
v_res_3115_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3109_);
stack->m_num = v_res_3115_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_3116_, lean_object* v___y_3117_){
_start:
{
uint8_t v_res_3118_; lean_object* v_r_3119_; 
v_res_3118_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3116_);
lean_dec(v_a_3116_);
v_r_3119_ = lean_box(v_res_3118_);
return v_r_3119_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(lean_object* v_place_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v___x_3123_; lean_object* v_capacity_3124_; lean_object* v_buffer_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3123_ = lean_st_ref_get(v_a_3121_);
v_capacity_3124_ = lean_ctor_get(v___x_3123_, 2);
lean_inc(v_capacity_3124_);
v_buffer_3125_ = lean_ctor_get(v___x_3123_, 4);
lean_inc_ref(v_buffer_3125_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_nat_mod(v_place_3120_, v_capacity_3124_);
lean_dec(v_capacity_3124_);
v___x_3127_ = lean_array_fget(v_buffer_3125_, v___x_3126_);
lean_dec(v___x_3126_);
lean_dec_ref(v_buffer_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_place_3120_ = stack[0].m_obj;
lean_object* v_a_3121_ = stack[1].m_obj;
lean_object* v_res_3128_;
v_res_3128_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3120_, v_a_3121_);
stack->m_obj
 = v_res_3128_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_place_3129_, lean_object* v_a_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v_res_3132_; 
v_res_3132_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3129_, v_a_3130_);
lean_dec(v_a_3130_);
lean_dec(v_place_3129_);
return v_res_3132_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(lean_object* v_next_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3136_ = lean_st_ref_get(v_a_3134_);
v___x_3137_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3134_);
if (v___x_3137_ == 0)
{
lean_object* v_capacity_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v_fst_3143_; lean_object* v_snd_3144_; lean_object* v_st_3146_; lean_object* v___y_3147_; 
v_capacity_3138_ = lean_ctor_get(v___x_3136_, 2);
v___x_3139_ = 1;
v___x_3140_ = lean_nat_mod(v_next_3133_, v_capacity_3138_);
v___x_3141_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v___x_3140_, v_a_3134_);
lean_dec(v___x_3140_);
v___x_3142_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v___x_3141_, v_next_3133_);
lean_dec(v___x_3141_);
v_fst_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_fst_3143_);
v_snd_3144_ = lean_ctor_get(v___x_3142_, 1);
lean_inc(v_snd_3144_);
lean_dec_ref(v___x_3142_);
if (lean_obj_tag(v_fst_3143_) == 1)
{
uint8_t v___x_3149_; 
v___x_3149_ = lean_unbox(v_snd_3144_);
lean_dec(v_snd_3144_);
if (v___x_3149_ == 0)
{
v_st_3146_ = v___x_3136_;
v___y_3147_ = v_a_3134_;
goto v___jp_3145_;
}
else
{
lean_object* v___x_3150_; lean_object* v_producers_3151_; lean_object* v_waiters_3152_; lean_object* v_capacity_3153_; lean_object* v_size_3154_; lean_object* v_buffer_3155_; lean_object* v_write_3156_; lean_object* v_read_3157_; lean_object* v_receivers_3158_; lean_object* v_nextId_3159_; uint8_t v_closed_3160_; lean_object* v_pos_3161_; lean_object* v___x_3162_; 
v___x_3150_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v___x_3136_);
v_producers_3151_ = lean_ctor_get(v___x_3150_, 0);
v_waiters_3152_ = lean_ctor_get(v___x_3150_, 1);
v_capacity_3153_ = lean_ctor_get(v___x_3150_, 2);
v_size_3154_ = lean_ctor_get(v___x_3150_, 3);
v_buffer_3155_ = lean_ctor_get(v___x_3150_, 4);
v_write_3156_ = lean_ctor_get(v___x_3150_, 5);
v_read_3157_ = lean_ctor_get(v___x_3150_, 6);
v_receivers_3158_ = lean_ctor_get(v___x_3150_, 7);
v_nextId_3159_ = lean_ctor_get(v___x_3150_, 8);
v_closed_3160_ = lean_ctor_get_uint8(v___x_3150_, sizeof(void*)*10);
v_pos_3161_ = lean_ctor_get(v___x_3150_, 9);
lean_inc_ref(v_producers_3151_);
v___x_3162_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_3151_);
if (lean_obj_tag(v___x_3162_) == 1)
{
lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3174_; 
lean_inc(v_pos_3161_);
lean_inc(v_nextId_3159_);
lean_inc(v_receivers_3158_);
lean_inc(v_read_3157_);
lean_inc(v_write_3156_);
lean_inc_ref(v_buffer_3155_);
lean_inc(v_size_3154_);
lean_inc(v_capacity_3153_);
lean_inc_ref(v_waiters_3152_);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; lean_object* v_unused_3176_; lean_object* v_unused_3177_; lean_object* v_unused_3178_; lean_object* v_unused_3179_; lean_object* v_unused_3180_; lean_object* v_unused_3181_; lean_object* v_unused_3182_; lean_object* v_unused_3183_; lean_object* v_unused_3184_; 
v_unused_3175_ = lean_ctor_get(v___x_3150_, 9);
lean_dec(v_unused_3175_);
v_unused_3176_ = lean_ctor_get(v___x_3150_, 8);
lean_dec(v_unused_3176_);
v_unused_3177_ = lean_ctor_get(v___x_3150_, 7);
lean_dec(v_unused_3177_);
v_unused_3178_ = lean_ctor_get(v___x_3150_, 6);
lean_dec(v_unused_3178_);
v_unused_3179_ = lean_ctor_get(v___x_3150_, 5);
lean_dec(v_unused_3179_);
v_unused_3180_ = lean_ctor_get(v___x_3150_, 4);
lean_dec(v_unused_3180_);
v_unused_3181_ = lean_ctor_get(v___x_3150_, 3);
lean_dec(v_unused_3181_);
v_unused_3182_ = lean_ctor_get(v___x_3150_, 2);
lean_dec(v_unused_3182_);
v_unused_3183_ = lean_ctor_get(v___x_3150_, 1);
lean_dec(v_unused_3183_);
v_unused_3184_ = lean_ctor_get(v___x_3150_, 0);
lean_dec(v_unused_3184_);
v___x_3164_ = v___x_3150_;
v_isShared_3165_ = v_isSharedCheck_3174_;
goto v_resetjp_3163_;
}
else
{
lean_dec(v___x_3150_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3174_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v_val_3166_; lean_object* v_fst_3167_; lean_object* v_snd_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3172_; 
v_val_3166_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_val_3166_);
lean_dec_ref_known(v___x_3162_, 1);
v_fst_3167_ = lean_ctor_get(v_val_3166_, 0);
lean_inc(v_fst_3167_);
v_snd_3168_ = lean_ctor_get(v_val_3166_, 1);
lean_inc(v_snd_3168_);
lean_dec(v_val_3166_);
v___x_3169_ = lean_box(v___x_3139_);
v___x_3170_ = lean_io_promise_resolve(v___x_3169_, v_fst_3167_);
lean_dec(v_fst_3167_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v_snd_3168_);
v___x_3172_ = v___x_3164_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_snd_3168_);
lean_ctor_set(v_reuseFailAlloc_3173_, 1, v_waiters_3152_);
lean_ctor_set(v_reuseFailAlloc_3173_, 2, v_capacity_3153_);
lean_ctor_set(v_reuseFailAlloc_3173_, 3, v_size_3154_);
lean_ctor_set(v_reuseFailAlloc_3173_, 4, v_buffer_3155_);
lean_ctor_set(v_reuseFailAlloc_3173_, 5, v_write_3156_);
lean_ctor_set(v_reuseFailAlloc_3173_, 6, v_read_3157_);
lean_ctor_set(v_reuseFailAlloc_3173_, 7, v_receivers_3158_);
lean_ctor_set(v_reuseFailAlloc_3173_, 8, v_nextId_3159_);
lean_ctor_set(v_reuseFailAlloc_3173_, 9, v_pos_3161_);
lean_ctor_set_uint8(v_reuseFailAlloc_3173_, sizeof(void*)*10, v_closed_3160_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
v_st_3146_ = v___x_3172_;
v___y_3147_ = v_a_3134_;
goto v___jp_3145_;
}
}
}
else
{
lean_dec(v___x_3162_);
v_st_3146_ = v___x_3150_;
v___y_3147_ = v_a_3134_;
goto v___jp_3145_;
}
}
}
else
{
lean_object* v___x_3185_; 
lean_dec(v_snd_3144_);
lean_dec(v_fst_3143_);
lean_dec(v___x_3136_);
v___x_3185_ = lean_box(0);
return v___x_3185_;
}
v___jp_3145_:
{
lean_object* v___x_3148_; 
v___x_3148_ = lean_st_ref_swap(v___y_3147_, v_st_3146_);
lean_dec(v___x_3148_);
return v_fst_3143_;
}
}
else
{
lean_object* v___x_3186_; 
lean_dec(v___x_3136_);
v___x_3186_ = lean_box(0);
return v___x_3186_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_next_3133_ = stack[0].m_obj;
lean_object* v_a_3134_ = stack[1].m_obj;
lean_object* v_res_3187_;
v_res_3187_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3133_, v_a_3134_);
stack->m_obj
 = v_res_3187_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg___boxed(lean_object* v_next_3188_, lean_object* v_a_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3188_, v_a_3189_);
lean_dec(v_a_3189_);
lean_dec(v_next_3188_);
return v_res_3191_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(lean_object* v_receiverId_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v___x_3195_; lean_object* v_receivers_3196_; lean_object* v___x_3197_; 
v___x_3195_ = lean_st_ref_get(v_a_3193_);
v_receivers_3196_ = lean_ctor_get(v___x_3195_, 7);
lean_inc(v_receivers_3196_);
lean_dec(v___x_3195_);
v___x_3197_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3196_, v_receiverId_3192_);
if (lean_obj_tag(v___x_3197_) == 1)
{
lean_object* v_val_3198_; lean_object* v___x_3199_; 
v_val_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_val_3198_);
lean_dec_ref_known(v___x_3197_, 1);
v___x_3199_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_val_3198_, v_a_3193_);
lean_dec(v_val_3198_);
if (lean_obj_tag(v___x_3199_) == 1)
{
lean_object* v___x_3200_; lean_object* v_producers_3201_; lean_object* v_waiters_3202_; lean_object* v_capacity_3203_; lean_object* v_size_3204_; lean_object* v_buffer_3205_; lean_object* v_write_3206_; lean_object* v_read_3207_; lean_object* v_nextId_3208_; uint8_t v_closed_3209_; lean_object* v_pos_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3219_; 
v___x_3200_ = lean_st_ref_take(v_a_3193_);
v_producers_3201_ = lean_ctor_get(v___x_3200_, 0);
v_waiters_3202_ = lean_ctor_get(v___x_3200_, 1);
v_capacity_3203_ = lean_ctor_get(v___x_3200_, 2);
v_size_3204_ = lean_ctor_get(v___x_3200_, 3);
v_buffer_3205_ = lean_ctor_get(v___x_3200_, 4);
v_write_3206_ = lean_ctor_get(v___x_3200_, 5);
v_read_3207_ = lean_ctor_get(v___x_3200_, 6);
v_nextId_3208_ = lean_ctor_get(v___x_3200_, 8);
v_closed_3209_ = lean_ctor_get_uint8(v___x_3200_, sizeof(void*)*10);
v_pos_3210_ = lean_ctor_get(v___x_3200_, 9);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3219_ == 0)
{
lean_object* v_unused_3220_; 
v_unused_3220_ = lean_ctor_get(v___x_3200_, 7);
lean_dec(v_unused_3220_);
v___x_3212_ = v___x_3200_;
v_isShared_3213_ = v_isSharedCheck_3219_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_pos_3210_);
lean_inc(v_nextId_3208_);
lean_inc(v_read_3207_);
lean_inc(v_write_3206_);
lean_inc(v_buffer_3205_);
lean_inc(v_size_3204_);
lean_inc(v_capacity_3203_);
lean_inc(v_waiters_3202_);
lean_inc(v_producers_3201_);
lean_dec(v___x_3200_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3219_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3214_; lean_object* v___x_3216_; 
v___x_3214_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3192_, v_receivers_3196_);
if (v_isShared_3213_ == 0)
{
lean_ctor_set(v___x_3212_, 7, v___x_3214_);
v___x_3216_ = v___x_3212_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_producers_3201_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v_waiters_3202_);
lean_ctor_set(v_reuseFailAlloc_3218_, 2, v_capacity_3203_);
lean_ctor_set(v_reuseFailAlloc_3218_, 3, v_size_3204_);
lean_ctor_set(v_reuseFailAlloc_3218_, 4, v_buffer_3205_);
lean_ctor_set(v_reuseFailAlloc_3218_, 5, v_write_3206_);
lean_ctor_set(v_reuseFailAlloc_3218_, 6, v_read_3207_);
lean_ctor_set(v_reuseFailAlloc_3218_, 7, v___x_3214_);
lean_ctor_set(v_reuseFailAlloc_3218_, 8, v_nextId_3208_);
lean_ctor_set(v_reuseFailAlloc_3218_, 9, v_pos_3210_);
lean_ctor_set_uint8(v_reuseFailAlloc_3218_, sizeof(void*)*10, v_closed_3209_);
v___x_3216_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_st_ref_put(v_a_3193_, v___x_3216_);
return v___x_3199_;
}
}
}
else
{
lean_object* v___x_3221_; 
lean_dec(v___x_3199_);
lean_dec(v_receivers_3196_);
lean_dec(v_receiverId_3192_);
v___x_3221_ = lean_box(0);
return v___x_3221_;
}
}
else
{
lean_object* v___x_3222_; 
lean_dec(v___x_3197_);
lean_dec(v_receivers_3196_);
lean_dec(v_receiverId_3192_);
v___x_3222_ = lean_box(0);
return v___x_3222_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_receiverId_3192_ = stack[0].m_obj;
lean_object* v_a_3193_ = stack[1].m_obj;
lean_object* v_res_3223_;
v_res_3223_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3192_, v_a_3193_);
stack->m_obj
 = v_res_3223_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg___boxed(lean_object* v_receiverId_3224_, lean_object* v_a_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3224_, v_a_3225_);
lean_dec(v_a_3225_);
return v_res_3227_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(lean_object* v_id_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3228_, v___y_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3228_ = stack[0].m_obj;
lean_object* v___y_3229_ = stack[1].m_obj;
lean_object* v_res_3232_;
v_res_3232_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(v_id_3228_, v___y_3229_);
stack->m_obj
 = v_res_3232_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed(lean_object* v_id_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0(v_id_3233_, v___y_3234_);
lean_dec(v___y_3234_);
return v_res_3236_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(lean_object* v_ch_3237_){
_start:
{
lean_object* v_state_3239_; lean_object* v_id_3240_; lean_object* v___f_3241_; lean_object* v___x_3242_; 
v_state_3239_ = lean_ctor_get(v_ch_3237_, 0);
lean_inc_ref(v_state_3239_);
v_id_3240_ = lean_ctor_get(v_ch_3237_, 1);
lean_inc(v_id_3240_);
lean_dec_ref(v_ch_3237_);
v___f_3241_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3241_, 0, v_id_3240_);
v___x_3242_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3239_, v___f_3241_);
return v___x_3242_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3237_ = stack[0].m_obj;
lean_object* v_res_3243_;
v_res_3243_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3237_);
stack->m_obj
 = v_res_3243_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_3244_, lean_object* v_a_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3244_);
return v_res_3246_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_object* v_00_u03b1_3247_, lean_object* v_ch_3248_){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_3248_);
return v___x_3250_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3248_ = stack[1].m_obj;
lean_object* v_res_3251_;
v_res_3251_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(lean_box(0), v_ch_3248_);
stack->m_obj
 = v_res_3251_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_3252_, lean_object* v_ch_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv(v_00_u03b1_3252_, v_ch_3253_);
return v_res_3255_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_object* v_00_u03b1_3256_, lean_object* v_receiverId_3257_, lean_object* v_a_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_receiverId_3257_, v_a_3258_);
return v___x_3260_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_receiverId_3257_ = stack[1].m_obj;
lean_object* v_a_3258_ = stack[2].m_obj;
lean_object* v_res_3261_;
v_res_3261_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(lean_box(0), v_receiverId_3257_, v_a_3258_);
stack->m_obj
 = v_res_3261_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___boxed(lean_object* v_00_u03b1_3262_, lean_object* v_receiverId_3263_, lean_object* v_a_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0(v_00_u03b1_3262_, v_receiverId_3263_, v_a_3264_);
lean_dec(v_a_3264_);
return v_res_3266_;
}
}
uint8_t l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_3267_, lean_object* v_a_3268_){
_start:
{
uint8_t v___x_3270_; 
v___x_3270_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___redArg(v_a_3268_);
return v___x_3270_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3268_ = stack[1].m_obj;
uint8_t v_res_3271_;
v_res_3271_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(lean_box(0), v_a_3268_);
stack->m_num = v_res_3271_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_3272_, lean_object* v_a_3273_, lean_object* v___y_3274_){
_start:
{
uint8_t v_res_3275_; lean_object* v_r_3276_; 
v_res_3275_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__1(v_00_u03b1_3272_, v_a_3273_);
lean_dec(v_a_3273_);
v_r_3276_ = lean_box(v_res_3275_);
return v_r_3276_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_3277_, lean_object* v_place_3278_, lean_object* v_a_3279_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___redArg(v_place_3278_, v_a_3279_);
return v___x_3281_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_place_3278_ = stack[1].m_obj;
lean_object* v_a_3279_ = stack[2].m_obj;
lean_object* v_res_3282_;
v_res_3282_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(lean_box(0), v_place_3278_, v_a_3279_);
stack->m_obj
 = v_res_3282_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3283_, lean_object* v_place_3284_, lean_object* v_a_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__2(v_00_u03b1_3283_, v_place_3284_, v_a_3285_);
lean_dec(v_a_3285_);
lean_dec(v_place_3284_);
return v_res_3287_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_3288_, lean_object* v_slot_3289_, lean_object* v_next_3290_, lean_object* v_a_3291_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___redArg(v_slot_3289_, v_next_3290_);
return v___x_3293_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_slot_3289_ = stack[1].m_obj;
lean_object* v_next_3290_ = stack[2].m_obj;
lean_object* v_a_3291_ = stack[3].m_obj;
lean_object* v_res_3294_;
v_res_3294_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(lean_box(0), v_slot_3289_, v_next_3290_, v_a_3291_);
stack->m_obj
 = v_res_3294_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_3295_, lean_object* v_slot_3296_, lean_object* v_next_3297_, lean_object* v_a_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_spec__3(v_00_u03b1_3295_, v_slot_3296_, v_next_3297_, v_a_3298_);
lean_dec(v_a_3298_);
lean_dec(v_next_3297_);
lean_dec(v_slot_3296_);
return v_res_3300_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_object* v_00_u03b1_3301_, lean_object* v_next_3302_, lean_object* v_a_3303_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___redArg(v_next_3302_, v_a_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_next_3302_ = stack[1].m_obj;
lean_object* v_a_3303_ = stack[2].m_obj;
lean_object* v_res_3306_;
v_res_3306_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(lean_box(0), v_next_3302_, v_a_3303_);
stack->m_obj
 = v_res_3306_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3307_, lean_object* v_next_3308_, lean_object* v_a_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__0(v_00_u03b1_3307_, v_next_3308_, v_a_3309_);
lean_dec(v_a_3309_);
lean_dec(v_next_3308_);
return v_res_3311_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(lean_object* v_k_3312_, lean_object* v_t_3313_){
_start:
{
if (lean_obj_tag(v_t_3313_) == 0)
{
lean_object* v_k_3314_; lean_object* v_l_3315_; lean_object* v_r_3316_; uint8_t v___x_3317_; 
v_k_3314_ = lean_ctor_get(v_t_3313_, 1);
v_l_3315_ = lean_ctor_get(v_t_3313_, 3);
v_r_3316_ = lean_ctor_get(v_t_3313_, 4);
v___x_3317_ = lean_nat_dec_lt(v_k_3312_, v_k_3314_);
if (v___x_3317_ == 0)
{
uint8_t v___x_3318_; 
v___x_3318_ = lean_nat_dec_eq(v_k_3312_, v_k_3314_);
if (v___x_3318_ == 0)
{
v_t_3313_ = v_r_3316_;
goto _start;
}
else
{
return v___x_3318_;
}
}
else
{
v_t_3313_ = v_l_3315_;
goto _start;
}
}
else
{
uint8_t v___x_3321_; 
v___x_3321_ = 0;
return v___x_3321_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3312_ = stack[0].m_obj;
lean_object* v_t_3313_ = stack[1].m_obj;
uint8_t v_res_3322_;
v_res_3322_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3312_, v_t_3313_);
stack->m_num = v_res_3322_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg___boxed(lean_object* v_k_3323_, lean_object* v_t_3324_){
_start:
{
uint8_t v_res_3325_; lean_object* v_r_3326_; 
v_res_3325_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3323_, v_t_3324_);
lean_dec(v_t_3324_);
lean_dec(v_k_3323_);
v_r_3326_ = lean_box(v_res_3325_);
return v_r_3326_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = lean_box(0);
v___x_3328_ = lean_task_pure(v___x_3327_);
return v___x_3328_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(lean_object* v_id_3329_, lean_object* v___f_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v___x_3333_; lean_object* v_receivers_3334_; uint8_t v___x_3335_; 
v___x_3333_ = lean_st_ref_get(v___y_3331_);
v_receivers_3334_ = lean_ctor_get(v___x_3333_, 7);
lean_inc(v_receivers_3334_);
lean_dec(v___x_3333_);
v___x_3335_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_id_3329_, v_receivers_3334_);
lean_dec(v_receivers_3334_);
if (v___x_3335_ == 0)
{
lean_object* v___x_3336_; 
lean_dec_ref(v___f_3330_);
lean_dec(v_id_3329_);
v___x_3336_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3336_;
}
else
{
lean_object* v___x_3337_; 
v___x_3337_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0___redArg(v_id_3329_, v___y_3331_);
if (lean_obj_tag(v___x_3337_) == 1)
{
lean_object* v___x_3338_; 
lean_dec_ref(v___f_3330_);
v___x_3338_ = lean_task_pure(v___x_3337_);
return v___x_3338_;
}
else
{
lean_object* v___x_3339_; uint8_t v_closed_3340_; 
lean_dec(v___x_3337_);
v___x_3339_ = lean_st_ref_get(v___y_3331_);
v_closed_3340_ = lean_ctor_get_uint8(v___x_3339_, sizeof(void*)*10);
lean_dec(v___x_3339_);
if (v_closed_3340_ == 0)
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v_producers_3343_; lean_object* v_waiters_3344_; lean_object* v_capacity_3345_; lean_object* v_size_3346_; lean_object* v_buffer_3347_; lean_object* v_write_3348_; lean_object* v_read_3349_; lean_object* v_receivers_3350_; lean_object* v_nextId_3351_; uint8_t v_closed_3352_; lean_object* v_pos_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3367_; 
v___x_3341_ = lean_io_promise_new();
v___x_3342_ = lean_st_ref_take(v___y_3331_);
v_producers_3343_ = lean_ctor_get(v___x_3342_, 0);
v_waiters_3344_ = lean_ctor_get(v___x_3342_, 1);
v_capacity_3345_ = lean_ctor_get(v___x_3342_, 2);
v_size_3346_ = lean_ctor_get(v___x_3342_, 3);
v_buffer_3347_ = lean_ctor_get(v___x_3342_, 4);
v_write_3348_ = lean_ctor_get(v___x_3342_, 5);
v_read_3349_ = lean_ctor_get(v___x_3342_, 6);
v_receivers_3350_ = lean_ctor_get(v___x_3342_, 7);
v_nextId_3351_ = lean_ctor_get(v___x_3342_, 8);
v_closed_3352_ = lean_ctor_get_uint8(v___x_3342_, sizeof(void*)*10);
v_pos_3353_ = lean_ctor_get(v___x_3342_, 9);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3355_ = v___x_3342_;
v_isShared_3356_ = v_isSharedCheck_3367_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_pos_3353_);
lean_inc(v_nextId_3351_);
lean_inc(v_receivers_3350_);
lean_inc(v_read_3349_);
lean_inc(v_write_3348_);
lean_inc(v_buffer_3347_);
lean_inc(v_size_3346_);
lean_inc(v_capacity_3345_);
lean_inc(v_waiters_3344_);
lean_inc(v_producers_3343_);
lean_dec(v___x_3342_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3367_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3361_; 
v___x_3357_ = lean_box(0);
lean_inc(v___x_3341_);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3341_);
lean_ctor_set(v___x_3358_, 1, v___x_3357_);
v___x_3359_ = l_Std_Queue_enqueue___redArg(v___x_3358_, v_waiters_3344_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 1, v___x_3359_);
v___x_3361_ = v___x_3355_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_producers_3343_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v___x_3359_);
lean_ctor_set(v_reuseFailAlloc_3366_, 2, v_capacity_3345_);
lean_ctor_set(v_reuseFailAlloc_3366_, 3, v_size_3346_);
lean_ctor_set(v_reuseFailAlloc_3366_, 4, v_buffer_3347_);
lean_ctor_set(v_reuseFailAlloc_3366_, 5, v_write_3348_);
lean_ctor_set(v_reuseFailAlloc_3366_, 6, v_read_3349_);
lean_ctor_set(v_reuseFailAlloc_3366_, 7, v_receivers_3350_);
lean_ctor_set(v_reuseFailAlloc_3366_, 8, v_nextId_3351_);
lean_ctor_set(v_reuseFailAlloc_3366_, 9, v_pos_3353_);
lean_ctor_set_uint8(v_reuseFailAlloc_3366_, sizeof(void*)*10, v_closed_3352_);
v___x_3361_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3362_ = lean_st_ref_put(v___y_3331_, v___x_3361_);
v___x_3363_ = lean_io_promise_result_opt(v___x_3341_);
lean_dec(v___x_3341_);
v___x_3364_ = lean_unsigned_to_nat(0u);
v___x_3365_ = lean_io_bind_task(v___x_3363_, v___f_3330_, v___x_3364_, v_closed_3340_);
return v___x_3365_;
}
}
}
else
{
lean_object* v___x_3368_; 
lean_dec_ref(v___f_3330_);
v___x_3368_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3368_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3329_ = stack[0].m_obj;
lean_object* v___f_3330_ = stack[1].m_obj;
lean_object* v___y_3331_ = stack[2].m_obj;
lean_object* v_res_3369_;
v_res_3369_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(v_id_3329_, v___f_3330_, v___y_3331_);
stack->m_obj
 = v_res_3369_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed(lean_object* v_id_3370_, lean_object* v___f_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1(v_id_3370_, v___f_3371_, v___y_3372_);
lean_dec(v___y_3372_);
return v_res_3374_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(lean_object* v_ch_3375_, lean_object* v_res_3376_){
_start:
{
if (lean_obj_tag(v_res_3376_) == 0)
{
lean_dec_ref(v_ch_3375_);
goto v___jp_3378_;
}
else
{
lean_object* v_val_3380_; uint8_t v___x_3381_; 
v_val_3380_ = lean_ctor_get(v_res_3376_, 0);
v___x_3381_ = lean_unbox(v_val_3380_);
if (v___x_3381_ == 0)
{
lean_dec_ref(v_ch_3375_);
goto v___jp_3378_;
}
else
{
lean_object* v___x_3382_; 
v___x_3382_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3375_);
return v___x_3382_;
}
}
v___jp_3378_:
{
lean_object* v___x_3379_; 
v___x_3379_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___closed__0);
return v___x_3379_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3375_ = stack[0].m_obj;
lean_object* v_res_3376_ = stack[1].m_obj;
lean_object* v_res_3383_;
v_res_3383_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(v_ch_3375_, v_res_3376_);
stack->m_obj
 = v_res_3383_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed(lean_object* v_ch_3384_, lean_object* v_res_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0(v_ch_3384_, v_res_3385_);
lean_dec(v_res_3385_);
return v_res_3387_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(lean_object* v_ch_3388_){
_start:
{
lean_object* v_state_3390_; lean_object* v_id_3391_; lean_object* v___f_3392_; lean_object* v___f_3393_; lean_object* v___x_3394_; 
v_state_3390_ = lean_ctor_get(v_ch_3388_, 0);
lean_inc_ref(v_state_3390_);
v_id_3391_ = lean_ctor_get(v_ch_3388_, 1);
lean_inc(v_id_3391_);
v___f_3392_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3392_, 0, v_ch_3388_);
v___f_3393_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3393_, 0, v_id_3391_);
lean_closure_set(v___f_3393_, 1, v___f_3392_);
v___x_3394_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_trySend_spec__0___redArg(v_state_3390_, v___f_3393_);
return v___x_3394_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3388_ = stack[0].m_obj;
lean_object* v_res_3395_;
v_res_3395_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3388_);
stack->m_obj
 = v_res_3395_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg___boxed(lean_object* v_ch_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3396_);
return v_res_3398_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_object* v_00_u03b1_3399_, lean_object* v_ch_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3400_);
return v___x_3402_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3400_ = stack[1].m_obj;
lean_object* v_res_3403_;
v_res_3403_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(lean_box(0), v_ch_3400_);
stack->m_obj
 = v_res_3403_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___boxed(lean_object* v_00_u03b1_3404_, lean_object* v_ch_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv(v_00_u03b1_3404_, v_ch_3405_);
return v_res_3407_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_object* v_00_u03b2_3408_, lean_object* v_k_3409_, lean_object* v_t_3410_){
_start:
{
uint8_t v___x_3411_; 
v___x_3411_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___redArg(v_k_3409_, v_t_3410_);
return v___x_3411_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3409_ = stack[1].m_obj;
lean_object* v_t_3410_ = stack[2].m_obj;
uint8_t v_res_3412_;
v_res_3412_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(lean_box(0), v_k_3409_, v_t_3410_);
stack->m_num = v_res_3412_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0___boxed(lean_object* v_00_u03b2_3413_, lean_object* v_k_3414_, lean_object* v_t_3415_){
_start:
{
uint8_t v_res_3416_; lean_object* v_r_3417_; 
v_res_3416_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv_spec__0(v_00_u03b2_3413_, v_k_3414_, v_t_3415_);
lean_dec(v_t_3415_);
lean_dec(v_k_3414_);
v_r_3417_ = lean_box(v_res_3416_);
return v_r_3417_;
}
}
static lean_object* _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = lean_box(0);
v___x_3419_ = lean_task_pure(v___x_3418_);
return v___x_3419_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(lean_object* v_f_3420_, lean_object* v_ch_3421_, lean_object* v_prio_3422_, lean_object* v_x_3423_){
_start:
{
if (lean_obj_tag(v_x_3423_) == 0)
{
lean_object* v___x_3425_; 
lean_dec(v_prio_3422_);
lean_dec_ref(v_ch_3421_);
lean_dec_ref(v_f_3420_);
v___x_3425_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0, &l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___closed__0);
return v___x_3425_;
}
else
{
lean_object* v_val_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_val_3426_ = lean_ctor_get(v_x_3423_, 0);
lean_inc(v_val_3426_);
lean_dec_ref_known(v_x_3423_, 1);
lean_inc_ref(v_f_3420_);
v___x_3427_ = lean_apply_2(v_f_3420_, v_val_3426_, lean_box(0));
v___x_3428_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3420_, v_ch_3421_, v_prio_3422_);
return v___x_3428_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3420_ = stack[0].m_obj;
lean_object* v_ch_3421_ = stack[1].m_obj;
lean_object* v_prio_3422_ = stack[2].m_obj;
lean_object* v_x_3423_ = stack[3].m_obj;
lean_object* v_res_3429_;
v_res_3429_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(v_f_3420_, v_ch_3421_, v_prio_3422_, v_x_3423_);
stack->m_obj
 = v_res_3429_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed(lean_object* v_f_3430_, lean_object* v_ch_3431_, lean_object* v_prio_3432_, lean_object* v_x_3433_, lean_object* v___y_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0(v_f_3430_, v_ch_3431_, v_prio_3432_, v_x_3433_);
return v_res_3435_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(lean_object* v_f_3436_, lean_object* v_ch_3437_, lean_object* v_prio_3438_){
_start:
{
lean_object* v___f_3440_; lean_object* v___x_3441_; uint8_t v___x_3442_; lean_object* v___x_3443_; 
lean_inc(v_prio_3438_);
lean_inc_ref(v_ch_3437_);
v___f_3440_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3440_, 0, v_f_3436_);
lean_closure_set(v___f_3440_, 1, v_ch_3437_);
lean_closure_set(v___f_3440_, 2, v_prio_3438_);
v___x_3441_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_3437_);
v___x_3442_ = 0;
v___x_3443_ = lean_io_bind_task(v___x_3441_, v___f_3440_, v_prio_3438_, v___x_3442_);
return v___x_3443_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3436_ = stack[0].m_obj;
lean_object* v_ch_3437_ = stack[1].m_obj;
lean_object* v_prio_3438_ = stack[2].m_obj;
lean_object* v_res_3444_;
v_res_3444_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3436_, v_ch_3437_, v_prio_3438_);
stack->m_obj
 = v_res_3444_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg___boxed(lean_object* v_f_3445_, lean_object* v_ch_3446_, lean_object* v_prio_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3445_, v_ch_3446_, v_prio_3447_);
return v_res_3449_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_object* v_00_u03b1_3450_, lean_object* v_f_3451_, lean_object* v_ch_3452_, lean_object* v_prio_3453_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_3451_, v_ch_3452_, v_prio_3453_);
return v___x_3455_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_3451_ = stack[1].m_obj;
lean_object* v_ch_3452_ = stack[2].m_obj;
lean_object* v_prio_3453_ = stack[3].m_obj;
lean_object* v_res_3456_;
v_res_3456_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(lean_box(0), v_f_3451_, v_ch_3452_, v_prio_3453_);
stack->m_obj
 = v_res_3456_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___boxed(lean_object* v_00_u03b1_3457_, lean_object* v_f_3458_, lean_object* v_ch_3459_, lean_object* v_prio_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync(v_00_u03b1_3457_, v_f_3458_, v_ch_3459_, v_prio_3460_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(lean_object* v_toApplicative_3463_, lean_object* v_val_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v_pos_3466_; lean_object* v_toPure_3467_; uint8_t v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
v_pos_3466_ = lean_ctor_get(v_a_3465_, 1);
v_toPure_3467_ = lean_ctor_get(v_toApplicative_3463_, 1);
lean_inc(v_toPure_3467_);
lean_dec_ref(v_toApplicative_3463_);
v___x_3468_ = lean_nat_dec_eq(v_pos_3466_, v_val_3464_);
v___x_3469_ = lean_box(v___x_3468_);
v___x_3470_ = lean_apply_2(v_toPure_3467_, lean_box(0), v___x_3469_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed(lean_object* v_toApplicative_3471_, lean_object* v_val_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1(v_toApplicative_3471_, v_val_3472_, v_a_3473_);
lean_dec_ref(v_a_3473_);
lean_dec(v_val_3472_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0(lean_object* v_inst_3475_, lean_object* v_toBind_3476_, lean_object* v___f_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; 
v___x_3479_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3479_, 0, lean_box(0));
lean_closure_set(v___x_3479_, 1, lean_box(0));
lean_closure_set(v___x_3479_, 2, v_a_3478_);
v___x_3480_ = lean_apply_2(v_inst_3475_, lean_box(0), v___x_3479_);
v___x_3481_ = lean_apply_4(v_toBind_3476_, lean_box(0), lean_box(0), v___x_3480_, v___f_3477_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(lean_object* v___f_3482_, lean_object* v_receiverId_3483_, lean_object* v_toApplicative_3484_, lean_object* v_inst_3485_, lean_object* v_toBind_3486_, lean_object* v_inst_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
uint8_t v_closed_3490_; 
v_closed_3490_ = lean_ctor_get_uint8(v_a_3489_, sizeof(void*)*10);
if (v_closed_3490_ == 0)
{
lean_object* v_capacity_3491_; lean_object* v_size_3492_; lean_object* v_receivers_3493_; lean_object* v___x_3494_; 
v_capacity_3491_ = lean_ctor_get(v_a_3489_, 2);
lean_inc(v_capacity_3491_);
v_size_3492_ = lean_ctor_get(v_a_3489_, 3);
lean_inc(v_size_3492_);
v_receivers_3493_ = lean_ctor_get(v_a_3489_, 7);
lean_inc(v_receivers_3493_);
lean_dec_ref(v_a_3489_);
v___x_3494_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_3482_, v_receivers_3493_, v_receiverId_3483_);
if (lean_obj_tag(v___x_3494_) == 1)
{
lean_object* v_val_3495_; lean_object* v___x_3496_; uint8_t v___x_3497_; 
v_val_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_val_3495_);
lean_dec_ref_known(v___x_3494_, 1);
v___x_3496_ = lean_unsigned_to_nat(0u);
v___x_3497_ = lean_nat_dec_eq(v_size_3492_, v___x_3496_);
lean_dec(v_size_3492_);
if (v___x_3497_ == 0)
{
lean_object* v___f_3498_; lean_object* v___f_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
lean_inc(v_val_3495_);
v___f_3498_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3498_, 0, v_toApplicative_3484_);
lean_closure_set(v___f_3498_, 1, v_val_3495_);
lean_inc(v_toBind_3486_);
lean_inc(v_inst_3485_);
v___f_3499_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__0), 4, 3);
lean_closure_set(v___f_3499_, 0, v_inst_3485_);
lean_closure_set(v___f_3499_, 1, v_toBind_3486_);
lean_closure_set(v___f_3499_, 2, v___f_3498_);
v___x_3500_ = lean_nat_mod(v_val_3495_, v_capacity_3491_);
lean_dec(v_capacity_3491_);
lean_dec(v_val_3495_);
v___x_3501_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___redArg(v_inst_3487_, v_inst_3485_, v___x_3500_, v_a_3488_);
v___x_3502_ = lean_apply_4(v_toBind_3486_, lean_box(0), lean_box(0), v___x_3501_, v___f_3499_);
return v___x_3502_;
}
else
{
lean_object* v_toPure_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
lean_dec(v_val_3495_);
lean_dec(v_capacity_3491_);
lean_dec_ref(v_inst_3487_);
lean_dec(v_toBind_3486_);
lean_dec(v_inst_3485_);
v_toPure_3503_ = lean_ctor_get(v_toApplicative_3484_, 1);
lean_inc(v_toPure_3503_);
lean_dec_ref(v_toApplicative_3484_);
v___x_3504_ = lean_box(v_closed_3490_);
v___x_3505_ = lean_apply_2(v_toPure_3503_, lean_box(0), v___x_3504_);
return v___x_3505_;
}
}
else
{
lean_object* v_toPure_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
lean_dec(v___x_3494_);
lean_dec(v_size_3492_);
lean_dec(v_capacity_3491_);
lean_dec_ref(v_inst_3487_);
lean_dec(v_toBind_3486_);
lean_dec(v_inst_3485_);
v_toPure_3506_ = lean_ctor_get(v_toApplicative_3484_, 1);
lean_inc(v_toPure_3506_);
lean_dec_ref(v_toApplicative_3484_);
v___x_3507_ = lean_box(v_closed_3490_);
v___x_3508_ = lean_apply_2(v_toPure_3506_, lean_box(0), v___x_3507_);
return v___x_3508_;
}
}
else
{
lean_object* v_toPure_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_dec_ref(v_a_3489_);
lean_dec_ref(v_inst_3487_);
lean_dec(v_toBind_3486_);
lean_dec(v_inst_3485_);
lean_dec(v_receiverId_3483_);
lean_dec_ref(v___f_3482_);
v_toPure_3509_ = lean_ctor_get(v_toApplicative_3484_, 1);
lean_inc(v_toPure_3509_);
lean_dec_ref(v_toApplicative_3484_);
v___x_3510_ = lean_box(v_closed_3490_);
v___x_3511_ = lean_apply_2(v_toPure_3509_, lean_box(0), v___x_3510_);
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed(lean_object* v___f_3512_, lean_object* v_receiverId_3513_, lean_object* v_toApplicative_3514_, lean_object* v_inst_3515_, lean_object* v_toBind_3516_, lean_object* v_inst_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2(v___f_3512_, v_receiverId_3513_, v_toApplicative_3514_, v_inst_3515_, v_toBind_3516_, v_inst_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(lean_object* v_inst_3521_, lean_object* v_inst_3522_, lean_object* v_receiverId_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v_toApplicative_3525_; lean_object* v_toBind_3526_; lean_object* v___f_3527_; lean_object* v___f_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v_toApplicative_3525_ = lean_ctor_get(v_inst_3521_, 0);
lean_inc_ref(v_toApplicative_3525_);
v_toBind_3526_ = lean_ctor_get(v_inst_3521_, 1);
lean_inc_n(v_toBind_3526_, 2);
v___f_3527_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3524_, 2);
lean_inc(v_inst_3522_);
v___f_3528_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3528_, 0, v___f_3527_);
lean_closure_set(v___f_3528_, 1, v_receiverId_3523_);
lean_closure_set(v___f_3528_, 2, v_toApplicative_3525_);
lean_closure_set(v___f_3528_, 3, v_inst_3522_);
lean_closure_set(v___f_3528_, 4, v_toBind_3526_);
lean_closure_set(v___f_3528_, 5, v_inst_3521_);
lean_closure_set(v___f_3528_, 6, v_a_3524_);
v___x_3529_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3529_, 0, lean_box(0));
lean_closure_set(v___x_3529_, 1, lean_box(0));
lean_closure_set(v___x_3529_, 2, v_a_3524_);
v___x_3530_ = lean_apply_2(v_inst_3522_, lean_box(0), v___x_3529_);
v___x_3531_ = lean_apply_4(v_toBind_3526_, lean_box(0), lean_box(0), v___x_3530_, v___f_3528_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___boxed(lean_object* v_inst_3532_, lean_object* v_inst_3533_, lean_object* v_receiverId_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg(v_inst_3532_, v_inst_3533_, v_receiverId_3534_, v_a_3535_);
lean_dec(v_a_3535_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(lean_object* v_m_3537_, lean_object* v_00_u03b1_3538_, lean_object* v_inst_3539_, lean_object* v_inst_3540_, lean_object* v_inst_3541_, lean_object* v_inst_3542_, lean_object* v_receiverId_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v_toApplicative_3545_; lean_object* v_toBind_3546_; lean_object* v___f_3547_; lean_object* v___f_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
v_toApplicative_3545_ = lean_ctor_get(v_inst_3539_, 0);
lean_inc_ref(v_toApplicative_3545_);
v_toBind_3546_ = lean_ctor_get(v_inst_3539_, 1);
lean_inc_n(v_toBind_3546_, 2);
v___f_3547_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___redArg___closed__0));
lean_inc_n(v_a_3544_, 2);
lean_inc(v_inst_3540_);
v___f_3548_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_3548_, 0, v___f_3547_);
lean_closure_set(v___f_3548_, 1, v_receiverId_3543_);
lean_closure_set(v___f_3548_, 2, v_toApplicative_3545_);
lean_closure_set(v___f_3548_, 3, v_inst_3540_);
lean_closure_set(v___f_3548_, 4, v_toBind_3546_);
lean_closure_set(v___f_3548_, 5, v_inst_3539_);
lean_closure_set(v___f_3548_, 6, v_a_3544_);
v___x_3549_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3549_, 0, lean_box(0));
lean_closure_set(v___x_3549_, 1, lean_box(0));
lean_closure_set(v___x_3549_, 2, v_a_3544_);
v___x_3550_ = lean_apply_2(v_inst_3540_, lean_box(0), v___x_3549_);
v___x_3551_ = lean_apply_4(v_toBind_3546_, lean_box(0), lean_box(0), v___x_3550_, v___f_3548_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27___boxed(lean_object* v_m_3552_, lean_object* v_00_u03b1_3553_, lean_object* v_inst_3554_, lean_object* v_inst_3555_, lean_object* v_inst_3556_, lean_object* v_inst_3557_, lean_object* v_receiverId_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvReady_x27(v_m_3552_, v_00_u03b1_3553_, v_inst_3554_, v_inst_3555_, v_inst_3556_, v_inst_3557_, v_receiverId_3558_, v_a_3559_);
lean_dec(v_a_3559_);
lean_dec(v_inst_3557_);
lean_dec(v_inst_3556_);
return v_res_3560_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(lean_object* v_w_3563_, lean_object* v_lose_3564_){
_start:
{
lean_object* v_finished_3566_; lean_object* v_promise_3567_; lean_object* v___x_3568_; uint8_t v___y_3570_; uint8_t v___x_3578_; 
v_finished_3566_ = lean_ctor_get(v_w_3563_, 0);
v_promise_3567_ = lean_ctor_get(v_w_3563_, 1);
v___x_3568_ = lean_st_ref_take(v_finished_3566_);
v___x_3578_ = lean_unbox(v___x_3568_);
lean_dec(v___x_3568_);
if (v___x_3578_ == 0)
{
uint8_t v___x_3579_; 
v___x_3579_ = 1;
v___y_3570_ = v___x_3579_;
goto v___jp_3569_;
}
else
{
uint8_t v___x_3580_; 
v___x_3580_ = 0;
v___y_3570_ = v___x_3580_;
goto v___jp_3569_;
}
v___jp_3569_:
{
uint8_t v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3571_ = 1;
v___x_3572_ = lean_box(v___x_3571_);
v___x_3573_ = lean_st_ref_put(v_finished_3566_, v___x_3572_);
if (v___y_3570_ == 0)
{
lean_object* v___x_3574_; 
v___x_3574_ = lean_apply_1(v_lose_3564_, lean_box(0));
return v___x_3574_;
}
else
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
lean_dec_ref(v_lose_3564_);
v___x_3575_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___closed__0));
v___x_3576_ = lean_io_promise_resolve(v___x_3575_, v_promise_3567_);
v___x_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
return v___x_3577_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_3563_ = stack[0].m_obj;
lean_object* v_lose_3564_ = stack[1].m_obj;
lean_object* v_res_3581_;
v_res_3581_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3563_, v_lose_3564_);
stack->m_obj
 = v_res_3581_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg___boxed(lean_object* v_w_3582_, lean_object* v_lose_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3582_, v_lose_3583_);
lean_dec_ref(v_w_3582_);
return v_res_3585_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_object* v_00_u03b1_3586_, lean_object* v_w_3587_, lean_object* v_lose_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_w_3587_, v_lose_3588_);
return v___x_3590_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_3587_ = stack[1].m_obj;
lean_object* v_lose_3588_ = stack[2].m_obj;
lean_object* v_res_3591_;
v_res_3591_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(lean_box(0), v_w_3587_, v_lose_3588_);
stack->m_obj
 = v_res_3591_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___boxed(lean_object* v_00_u03b1_3592_, lean_object* v_w_3593_, lean_object* v_lose_3594_, lean_object* v___y_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0(v_00_u03b1_3592_, v_w_3593_, v_lose_3594_);
lean_dec_ref(v_w_3593_);
return v_res_3596_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(lean_object* v_receiverId_3597_, lean_object* v_a_3598_){
_start:
{
lean_object* v___x_3600_; lean_object* v_receivers_3601_; lean_object* v___x_3602_; 
v___x_3600_ = lean_st_ref_get(v_a_3598_);
v_receivers_3601_ = lean_ctor_get(v___x_3600_, 7);
lean_inc(v_receivers_3601_);
lean_dec(v___x_3600_);
v___x_3602_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3601_, v_receiverId_3597_);
if (lean_obj_tag(v___x_3602_) == 1)
{
lean_object* v_val_3603_; lean_object* v___x_3604_; 
v_val_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_val_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v___x_3604_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0___redArg(v_val_3603_, v_a_3598_);
lean_dec(v_val_3603_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3637_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3607_ = v___x_3604_;
v_isShared_3608_ = v_isSharedCheck_3637_;
goto v_resetjp_3606_;
}
else
{
lean_inc(v_a_3605_);
lean_dec(v___x_3604_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3637_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
if (lean_obj_tag(v_a_3605_) == 1)
{
lean_object* v___x_3609_; lean_object* v_producers_3610_; lean_object* v_waiters_3611_; lean_object* v_capacity_3612_; lean_object* v_size_3613_; lean_object* v_buffer_3614_; lean_object* v_write_3615_; lean_object* v_read_3616_; lean_object* v_nextId_3617_; uint8_t v_closed_3618_; lean_object* v_pos_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3631_; 
v___x_3609_ = lean_st_ref_take(v_a_3598_);
v_producers_3610_ = lean_ctor_get(v___x_3609_, 0);
v_waiters_3611_ = lean_ctor_get(v___x_3609_, 1);
v_capacity_3612_ = lean_ctor_get(v___x_3609_, 2);
v_size_3613_ = lean_ctor_get(v___x_3609_, 3);
v_buffer_3614_ = lean_ctor_get(v___x_3609_, 4);
v_write_3615_ = lean_ctor_get(v___x_3609_, 5);
v_read_3616_ = lean_ctor_get(v___x_3609_, 6);
v_nextId_3617_ = lean_ctor_get(v___x_3609_, 8);
v_closed_3618_ = lean_ctor_get_uint8(v___x_3609_, sizeof(void*)*10);
v_pos_3619_ = lean_ctor_get(v___x_3609_, 9);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; 
v_unused_3632_ = lean_ctor_get(v___x_3609_, 7);
lean_dec(v_unused_3632_);
v___x_3621_ = v___x_3609_;
v_isShared_3622_ = v_isSharedCheck_3631_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_pos_3619_);
lean_inc(v_nextId_3617_);
lean_inc(v_read_3616_);
lean_inc(v_write_3615_);
lean_inc(v_buffer_3614_);
lean_inc(v_size_3613_);
lean_inc(v_capacity_3612_);
lean_inc(v_waiters_3611_);
lean_inc(v_producers_3610_);
lean_dec(v___x_3609_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3631_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3625_; 
v___x_3623_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_3597_, v_receivers_3601_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set(v___x_3621_, 7, v___x_3623_);
v___x_3625_ = v___x_3621_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_producers_3610_);
lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_waiters_3611_);
lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_capacity_3612_);
lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_size_3613_);
lean_ctor_set(v_reuseFailAlloc_3630_, 4, v_buffer_3614_);
lean_ctor_set(v_reuseFailAlloc_3630_, 5, v_write_3615_);
lean_ctor_set(v_reuseFailAlloc_3630_, 6, v_read_3616_);
lean_ctor_set(v_reuseFailAlloc_3630_, 7, v___x_3623_);
lean_ctor_set(v_reuseFailAlloc_3630_, 8, v_nextId_3617_);
lean_ctor_set(v_reuseFailAlloc_3630_, 9, v_pos_3619_);
lean_ctor_set_uint8(v_reuseFailAlloc_3630_, sizeof(void*)*10, v_closed_3618_);
v___x_3625_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3626_ = lean_st_ref_put(v_a_3598_, v___x_3625_);
if (v_isShared_3608_ == 0)
{
v___x_3628_ = v___x_3607_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3605_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_object* v___x_3633_; lean_object* v___x_3635_; 
lean_dec(v_a_3605_);
lean_dec(v_receivers_3601_);
lean_dec(v_receiverId_3597_);
v___x_3633_ = lean_box(0);
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3633_);
v___x_3635_ = v___x_3607_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3633_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
else
{
lean_dec(v_receivers_3601_);
lean_dec(v_receiverId_3597_);
return v___x_3604_;
}
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
lean_dec(v___x_3602_);
lean_dec(v_receivers_3601_);
lean_dec(v_receiverId_3597_);
v___x_3638_ = lean_box(0);
v___x_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
return v___x_3639_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_receiverId_3597_ = stack[0].m_obj;
lean_object* v_a_3598_ = stack[1].m_obj;
lean_object* v_res_3640_;
v_res_3640_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3597_, v_a_3598_);
stack->m_obj
 = v_res_3640_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg___boxed(lean_object* v_receiverId_3641_, lean_object* v_a_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3641_, v_a_3642_);
lean_dec(v_a_3642_);
return v_res_3644_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(lean_object* v___x_3645_, lean_object* v_w_3646_, lean_object* v_lose_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v_finished_3650_; lean_object* v_promise_3651_; lean_object* v___x_3652_; uint8_t v___y_3654_; uint8_t v___x_3678_; 
v_finished_3650_ = lean_ctor_get(v_w_3646_, 0);
v_promise_3651_ = lean_ctor_get(v_w_3646_, 1);
v___x_3652_ = lean_st_ref_take(v_finished_3650_);
v___x_3678_ = lean_unbox(v___x_3652_);
lean_dec(v___x_3652_);
if (v___x_3678_ == 0)
{
uint8_t v___x_3679_; 
v___x_3679_ = 1;
v___y_3654_ = v___x_3679_;
goto v___jp_3653_;
}
else
{
uint8_t v___x_3680_; 
v___x_3680_ = 0;
v___y_3654_ = v___x_3680_;
goto v___jp_3653_;
}
v___jp_3653_:
{
uint8_t v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = 1;
v___x_3656_ = lean_box(v___x_3655_);
v___x_3657_ = lean_st_ref_put(v_finished_3650_, v___x_3656_);
if (v___y_3654_ == 0)
{
lean_object* v___x_3658_; 
lean_dec(v___x_3645_);
lean_inc(v___y_3648_);
v___x_3658_ = lean_apply_2(v_lose_3647_, v___y_3648_, lean_box(0));
return v___x_3658_;
}
else
{
lean_object* v___x_3659_; 
lean_dec_ref(v_lose_3647_);
v___x_3659_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v___x_3645_, v___y_3648_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3669_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3662_ = v___x_3659_;
v_isShared_3663_ = v_isSharedCheck_3669_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3659_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3669_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
v___x_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3664_, 0, v_a_3660_);
v___x_3665_ = lean_io_promise_resolve(v___x_3664_, v_promise_3651_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 0, v___x_3665_);
v___x_3667_ = v___x_3662_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
v_a_3670_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3659_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3659_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3645_ = stack[0].m_obj;
lean_object* v_w_3646_ = stack[1].m_obj;
lean_object* v_lose_3647_ = stack[2].m_obj;
lean_object* v___y_3648_ = stack[3].m_obj;
lean_object* v_res_3681_;
v_res_3681_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3645_, v_w_3646_, v_lose_3647_, v___y_3648_);
stack->m_obj
 = v_res_3681_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg___boxed(lean_object* v___x_3682_, lean_object* v_w_3683_, lean_object* v_lose_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3682_, v_w_3683_, v_lose_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v_w_3683_);
return v_res_3687_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_object* v_00_u03b1_3688_, lean_object* v___x_3689_, lean_object* v_w_3690_, lean_object* v_lose_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v___x_3689_, v_w_3690_, v_lose_3691_, v___y_3692_);
return v___x_3694_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3689_ = stack[1].m_obj;
lean_object* v_w_3690_ = stack[2].m_obj;
lean_object* v_lose_3691_ = stack[3].m_obj;
lean_object* v___y_3692_ = stack[4].m_obj;
lean_object* v_res_3695_;
v_res_3695_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(lean_box(0), v___x_3689_, v_w_3690_, v_lose_3691_, v___y_3692_);
stack->m_obj
 = v_res_3695_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___boxed(lean_object* v_00_u03b1_3696_, lean_object* v___x_3697_, lean_object* v_w_3698_, lean_object* v_lose_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2(v_00_u03b1_3696_, v___x_3697_, v_w_3698_, v_lose_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v_w_3698_);
return v_res_3702_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(lean_object* v___x_3703_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3703_);
return v___x_3705_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3703_ = stack[0].m_obj;
lean_object* v_res_3706_;
v_res_3706_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(v___x_3703_);
stack->m_obj
 = v_res_3706_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0___boxed(lean_object* v___x_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__0(v___x_3707_);
return v_res_3709_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(lean_object* v_id_3710_, lean_object* v___f_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v___x_3714_; uint8_t v_closed_3715_; 
v___x_3714_ = lean_st_ref_get(v___y_3712_);
v_closed_3715_ = lean_ctor_get_uint8(v___x_3714_, sizeof(void*)*10);
if (v_closed_3715_ == 0)
{
lean_object* v_capacity_3716_; lean_object* v_size_3717_; lean_object* v_receivers_3718_; lean_object* v___x_3719_; 
v_capacity_3716_ = lean_ctor_get(v___x_3714_, 2);
lean_inc(v_capacity_3716_);
v_size_3717_ = lean_ctor_get(v___x_3714_, 3);
lean_inc(v_size_3717_);
v_receivers_3718_ = lean_ctor_get(v___x_3714_, 7);
lean_inc(v_receivers_3718_);
lean_dec(v___x_3714_);
v___x_3719_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_3718_, v_id_3710_);
lean_dec(v_receivers_3718_);
if (lean_obj_tag(v___x_3719_) == 1)
{
lean_object* v_val_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; 
v_val_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_val_3720_);
lean_dec_ref_known(v___x_3719_, 1);
v___x_3721_ = lean_unsigned_to_nat(0u);
v___x_3722_ = lean_nat_dec_eq(v_size_3717_, v___x_3721_);
lean_dec(v_size_3717_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = lean_nat_mod(v_val_3720_, v_capacity_3716_);
lean_dec(v_capacity_3716_);
v___x_3724_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__0_spec__1___redArg(v___x_3723_, v___y_3712_);
lean_dec(v___x_3723_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3726_; lean_object* v_pos_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref_known(v___x_3724_, 1);
v___x_3726_ = lean_st_ref_get(v_a_3725_);
lean_dec(v_a_3725_);
v_pos_3727_ = lean_ctor_get(v___x_3726_, 1);
lean_inc(v_pos_3727_);
lean_dec(v___x_3726_);
v___x_3728_ = lean_nat_dec_eq(v_pos_3727_, v_val_3720_);
lean_dec(v_val_3720_);
lean_dec(v_pos_3727_);
v___x_3729_ = lean_box(v___x_3728_);
lean_inc(v___y_3712_);
v___x_3730_ = lean_apply_3(v___f_3711_, v___x_3729_, v___y_3712_, lean_box(0));
return v___x_3730_;
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec(v_val_3720_);
lean_dec_ref(v___f_3711_);
v_a_3731_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3724_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3724_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_dec(v_val_3720_);
lean_dec(v_capacity_3716_);
v___x_3739_ = lean_box(v_closed_3715_);
lean_inc(v___y_3712_);
v___x_3740_ = lean_apply_3(v___f_3711_, v___x_3739_, v___y_3712_, lean_box(0));
return v___x_3740_;
}
}
else
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
lean_dec(v___x_3719_);
lean_dec(v_size_3717_);
lean_dec(v_capacity_3716_);
v___x_3741_ = lean_box(v_closed_3715_);
lean_inc(v___y_3712_);
v___x_3742_ = lean_apply_3(v___f_3711_, v___x_3741_, v___y_3712_, lean_box(0));
return v___x_3742_;
}
}
else
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
lean_dec(v___x_3714_);
v___x_3743_ = lean_box(v_closed_3715_);
lean_inc(v___y_3712_);
v___x_3744_ = lean_apply_3(v___f_3711_, v___x_3743_, v___y_3712_, lean_box(0));
return v___x_3744_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_3710_ = stack[0].m_obj;
lean_object* v___f_3711_ = stack[1].m_obj;
lean_object* v___y_3712_ = stack[2].m_obj;
lean_object* v_res_3745_;
v_res_3745_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(v_id_3710_, v___f_3711_, v___y_3712_);
stack->m_obj
 = v_res_3745_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed(lean_object* v_id_3746_, lean_object* v___f_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4(v_id_3746_, v___f_3747_, v___y_3748_);
lean_dec(v___y_3748_);
lean_dec(v_id_3746_);
return v_res_3750_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(uint8_t v_____do__lift_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; lean_object* v_producers_3755_; lean_object* v_waiters_3756_; lean_object* v_capacity_3757_; lean_object* v_size_3758_; lean_object* v_buffer_3759_; lean_object* v_write_3760_; lean_object* v_read_3761_; lean_object* v_receivers_3762_; lean_object* v_nextId_3763_; uint8_t v_closed_3764_; lean_object* v_pos_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3788_; 
v___x_3754_ = lean_st_ref_get(v___y_3752_);
v_producers_3755_ = lean_ctor_get(v___x_3754_, 0);
v_waiters_3756_ = lean_ctor_get(v___x_3754_, 1);
v_capacity_3757_ = lean_ctor_get(v___x_3754_, 2);
v_size_3758_ = lean_ctor_get(v___x_3754_, 3);
v_buffer_3759_ = lean_ctor_get(v___x_3754_, 4);
v_write_3760_ = lean_ctor_get(v___x_3754_, 5);
v_read_3761_ = lean_ctor_get(v___x_3754_, 6);
v_receivers_3762_ = lean_ctor_get(v___x_3754_, 7);
v_nextId_3763_ = lean_ctor_get(v___x_3754_, 8);
v_closed_3764_ = lean_ctor_get_uint8(v___x_3754_, sizeof(void*)*10);
v_pos_3765_ = lean_ctor_get(v___x_3754_, 9);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3767_ = v___x_3754_;
v_isShared_3768_ = v_isSharedCheck_3788_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_pos_3765_);
lean_inc(v_nextId_3763_);
lean_inc(v_receivers_3762_);
lean_inc(v_read_3761_);
lean_inc(v_write_3760_);
lean_inc(v_buffer_3759_);
lean_inc(v_size_3758_);
lean_inc(v_capacity_3757_);
lean_inc(v_waiters_3756_);
lean_inc(v_producers_3755_);
lean_dec(v___x_3754_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3788_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_3756_);
if (lean_obj_tag(v___x_3769_) == 1)
{
lean_object* v_val_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3785_; 
v_val_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3785_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_val_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3785_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v_fst_3774_; lean_object* v_snd_3775_; lean_object* v___x_3776_; lean_object* v___x_3778_; 
v_fst_3774_ = lean_ctor_get(v_val_3770_, 0);
lean_inc(v_fst_3774_);
v_snd_3775_ = lean_ctor_get(v_val_3770_, 1);
lean_inc(v_snd_3775_);
lean_dec(v_val_3770_);
v___x_3776_ = l___private_Std_Sync_Broadcast_0__Std_Broadcast_Consumer_resolve___redArg(v_fst_3774_, v_____do__lift_3751_);
lean_dec(v_fst_3774_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 1, v_snd_3775_);
v___x_3778_ = v___x_3767_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_producers_3755_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_snd_3775_);
lean_ctor_set(v_reuseFailAlloc_3784_, 2, v_capacity_3757_);
lean_ctor_set(v_reuseFailAlloc_3784_, 3, v_size_3758_);
lean_ctor_set(v_reuseFailAlloc_3784_, 4, v_buffer_3759_);
lean_ctor_set(v_reuseFailAlloc_3784_, 5, v_write_3760_);
lean_ctor_set(v_reuseFailAlloc_3784_, 6, v_read_3761_);
lean_ctor_set(v_reuseFailAlloc_3784_, 7, v_receivers_3762_);
lean_ctor_set(v_reuseFailAlloc_3784_, 8, v_nextId_3763_);
lean_ctor_set(v_reuseFailAlloc_3784_, 9, v_pos_3765_);
lean_ctor_set_uint8(v_reuseFailAlloc_3784_, sizeof(void*)*10, v_closed_3764_);
v___x_3778_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
v___x_3779_ = lean_box(0);
v___x_3780_ = lean_st_ref_swap(v___y_3752_, v___x_3778_);
lean_dec(v___x_3780_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set_tag(v___x_3772_, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3779_);
v___x_3782_ = v___x_3772_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3779_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_dec(v___x_3769_);
lean_del_object(v___x_3767_);
lean_dec(v_pos_3765_);
lean_dec(v_nextId_3763_);
lean_dec(v_receivers_3762_);
lean_dec(v_read_3761_);
lean_dec(v_write_3760_);
lean_dec_ref(v_buffer_3759_);
lean_dec(v_size_3758_);
lean_dec(v_capacity_3757_);
lean_dec_ref(v_producers_3755_);
v___x_3786_ = lean_box(0);
v___x_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3787_, 0, v___x_3786_);
return v___x_3787_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_____do__lift_3751_ = stack[0].m_num;
lean_object* v___y_3752_ = stack[1].m_obj;
lean_object* v_res_3789_;
v_res_3789_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3751_, v___y_3752_);
stack->m_obj
 = v_res_3789_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed(lean_object* v_____do__lift_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
uint8_t v_____do__lift_3893__boxed_3793_; lean_object* v_res_3794_; 
v_____do__lift_3893__boxed_3793_ = lean_unbox(v_____do__lift_3790_);
v_res_3794_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3893__boxed_3793_, v___y_3791_);
lean_dec(v___y_3791_);
return v_res_3794_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(lean_object* v_waiter_3795_, lean_object* v___f_3796_, lean_object* v_id_3797_, uint8_t v_____do__lift_3798_, lean_object* v___y_3799_){
_start:
{
if (v_____do__lift_3798_ == 0)
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v_producers_3803_; lean_object* v_waiters_3804_; lean_object* v_capacity_3805_; lean_object* v_size_3806_; lean_object* v_buffer_3807_; lean_object* v_write_3808_; lean_object* v_read_3809_; lean_object* v_receivers_3810_; lean_object* v_nextId_3811_; uint8_t v_closed_3812_; lean_object* v_pos_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3827_; 
lean_dec(v_id_3797_);
v___x_3801_ = lean_io_promise_new();
v___x_3802_ = lean_st_ref_take(v___y_3799_);
v_producers_3803_ = lean_ctor_get(v___x_3802_, 0);
v_waiters_3804_ = lean_ctor_get(v___x_3802_, 1);
v_capacity_3805_ = lean_ctor_get(v___x_3802_, 2);
v_size_3806_ = lean_ctor_get(v___x_3802_, 3);
v_buffer_3807_ = lean_ctor_get(v___x_3802_, 4);
v_write_3808_ = lean_ctor_get(v___x_3802_, 5);
v_read_3809_ = lean_ctor_get(v___x_3802_, 6);
v_receivers_3810_ = lean_ctor_get(v___x_3802_, 7);
v_nextId_3811_ = lean_ctor_get(v___x_3802_, 8);
v_closed_3812_ = lean_ctor_get_uint8(v___x_3802_, sizeof(void*)*10);
v_pos_3813_ = lean_ctor_get(v___x_3802_, 9);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3815_ = v___x_3802_;
v_isShared_3816_ = v_isSharedCheck_3827_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_pos_3813_);
lean_inc(v_nextId_3811_);
lean_inc(v_receivers_3810_);
lean_inc(v_read_3809_);
lean_inc(v_write_3808_);
lean_inc(v_buffer_3807_);
lean_inc(v_size_3806_);
lean_inc(v_capacity_3805_);
lean_inc(v_waiters_3804_);
lean_inc(v_producers_3803_);
lean_dec(v___x_3802_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3827_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
v___x_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3817_, 0, v_waiter_3795_);
lean_inc(v___x_3801_);
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3801_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = l_Std_Queue_enqueue___redArg(v___x_3818_, v_waiters_3804_);
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 1, v___x_3819_);
v___x_3821_ = v___x_3815_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_producers_3803_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v___x_3819_);
lean_ctor_set(v_reuseFailAlloc_3826_, 2, v_capacity_3805_);
lean_ctor_set(v_reuseFailAlloc_3826_, 3, v_size_3806_);
lean_ctor_set(v_reuseFailAlloc_3826_, 4, v_buffer_3807_);
lean_ctor_set(v_reuseFailAlloc_3826_, 5, v_write_3808_);
lean_ctor_set(v_reuseFailAlloc_3826_, 6, v_read_3809_);
lean_ctor_set(v_reuseFailAlloc_3826_, 7, v_receivers_3810_);
lean_ctor_set(v_reuseFailAlloc_3826_, 8, v_nextId_3811_);
lean_ctor_set(v_reuseFailAlloc_3826_, 9, v_pos_3813_);
lean_ctor_set_uint8(v_reuseFailAlloc_3826_, sizeof(void*)*10, v_closed_3812_);
v___x_3821_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3822_ = lean_st_ref_put(v___y_3799_, v___x_3821_);
v___x_3823_ = lean_io_promise_result_opt(v___x_3801_);
lean_dec(v___x_3801_);
v___x_3824_ = lean_unsigned_to_nat(0u);
v___x_3825_ = l_EIO_chainTask___redArg(v___x_3823_, v___f_3796_, v___x_3824_, v_____do__lift_3798_);
return v___x_3825_;
}
}
}
else
{
lean_object* v___x_3828_; lean_object* v_lose_3829_; lean_object* v___x_3830_; 
lean_dec_ref(v___f_3796_);
v___x_3828_ = lean_box(v_____do__lift_3798_);
v_lose_3829_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__2___boxed), 3, 1);
lean_closure_set(v_lose_3829_, 0, v___x_3828_);
v___x_3830_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__2___redArg(v_id_3797_, v_waiter_3795_, v_lose_3829_, v___y_3799_);
lean_dec_ref(v_waiter_3795_);
return v___x_3830_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_3795_ = stack[0].m_obj;
lean_object* v___f_3796_ = stack[1].m_obj;
lean_object* v_id_3797_ = stack[2].m_obj;
uint8_t v_____do__lift_3798_ = stack[3].m_num;
lean_object* v___y_3799_ = stack[4].m_obj;
lean_object* v_res_3831_;
v_res_3831_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3795_, v___f_3796_, v_id_3797_, v_____do__lift_3798_, v___y_3799_);
stack->m_obj
 = v_res_3831_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed(lean_object* v_waiter_3832_, lean_object* v___f_3833_, lean_object* v_id_3834_, lean_object* v_____do__lift_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
uint8_t v_____do__lift_3981__boxed_3838_; lean_object* v_res_3839_; 
v_____do__lift_3981__boxed_3838_ = lean_unbox(v_____do__lift_3835_);
v_res_3839_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3(v_waiter_3832_, v___f_3833_, v_id_3834_, v_____do__lift_3981__boxed_3838_, v___y_3836_);
lean_dec(v___y_3836_);
return v_res_3839_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(lean_object* v_waiter_3842_, lean_object* v_ch_3843_, lean_object* v_res_x3f_3844_){
_start:
{
if (lean_obj_tag(v_res_x3f_3844_) == 0)
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
lean_dec_ref(v_ch_3843_);
lean_dec_ref(v_waiter_3842_);
v___x_3846_ = lean_box(0);
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
return v___x_3847_;
}
else
{
lean_object* v_val_3848_; uint8_t v___x_3849_; 
v_val_3848_ = lean_ctor_get(v_res_x3f_3844_, 0);
v___x_3849_ = lean_unbox(v_val_3848_);
if (v___x_3849_ == 0)
{
lean_object* v___f_3850_; lean_object* v___x_3851_; 
lean_dec_ref(v_ch_3843_);
v___f_3850_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___closed__0));
v___x_3851_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__0___redArg(v_waiter_3842_, v___f_3850_);
lean_dec_ref(v_waiter_3842_);
return v___x_3851_;
}
else
{
lean_object* v___x_3852_; 
v___x_3852_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3843_, v_waiter_3842_);
return v___x_3852_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_3842_ = stack[0].m_obj;
lean_object* v_ch_3843_ = stack[1].m_obj;
lean_object* v_res_x3f_3844_ = stack[2].m_obj;
lean_object* v_res_3853_;
v_res_3853_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(v_waiter_3842_, v_ch_3843_, v_res_x3f_3844_);
stack->m_obj
 = v_res_3853_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed(lean_object* v_waiter_3854_, lean_object* v_ch_3855_, lean_object* v_res_x3f_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1(v_waiter_3854_, v_ch_3855_, v_res_x3f_3856_);
lean_dec(v_res_x3f_3856_);
return v_res_3858_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(lean_object* v_ch_3859_, lean_object* v_waiter_3860_){
_start:
{
lean_object* v_state_3862_; lean_object* v_id_3863_; lean_object* v___f_3864_; lean_object* v___f_3865_; lean_object* v___f_3866_; lean_object* v___x_3867_; 
v_state_3862_ = lean_ctor_get(v_ch_3859_, 0);
lean_inc_ref(v_state_3862_);
v_id_3863_ = lean_ctor_get(v_ch_3859_, 1);
lean_inc_n(v_id_3863_, 2);
lean_inc_ref(v_waiter_3860_);
v___f_3864_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3864_, 0, v_waiter_3860_);
lean_closure_set(v___f_3864_, 1, v_ch_3859_);
v___f_3865_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__3___boxed), 6, 3);
lean_closure_set(v___f_3865_, 0, v_waiter_3860_);
lean_closure_set(v___f_3865_, 1, v___f_3864_);
lean_closure_set(v___f_3865_, 2, v_id_3863_);
v___f_3866_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___lam__4___boxed), 4, 2);
lean_closure_set(v___f_3866_, 0, v_id_3863_);
lean_closure_set(v___f_3866_, 1, v___f_3865_);
v___x_3867_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_subscribe_spec__1___redArg(v_state_3862_, v___f_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3859_ = stack[0].m_obj;
lean_object* v_waiter_3860_ = stack[1].m_obj;
lean_object* v_res_3868_;
v_res_3868_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3859_, v_waiter_3860_);
stack->m_obj
 = v_res_3868_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg___boxed(lean_object* v_ch_3869_, lean_object* v_waiter_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3869_, v_waiter_3870_);
return v_res_3872_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_object* v_00_u03b1_3873_, lean_object* v_ch_3874_, lean_object* v_waiter_3875_){
_start:
{
lean_object* v___x_3877_; 
v___x_3877_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_3874_, v_waiter_3875_);
return v___x_3877_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_3874_ = stack[1].m_obj;
lean_object* v_waiter_3875_ = stack[2].m_obj;
lean_object* v_res_3878_;
v_res_3878_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(lean_box(0), v_ch_3874_, v_waiter_3875_);
stack->m_obj
 = v_res_3878_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___boxed(lean_object* v_00_u03b1_3879_, lean_object* v_ch_3880_, lean_object* v_waiter_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux(v_00_u03b1_3879_, v_ch_3880_, v_waiter_3881_);
return v_res_3883_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_object* v_00_u03b1_3884_, lean_object* v_receiverId_3885_, lean_object* v_a_3886_){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___redArg(v_receiverId_3885_, v_a_3886_);
return v___x_3888_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_receiverId_3885_ = stack[1].m_obj;
lean_object* v_a_3886_ = stack[2].m_obj;
lean_object* v_res_3889_;
v_res_3889_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(lean_box(0), v_receiverId_3885_, v_a_3886_);
stack->m_obj
 = v_res_3889_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1___boxed(lean_object* v_00_u03b1_3890_, lean_object* v_receiverId_3891_, lean_object* v_a_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux_spec__1(v_00_u03b1_3890_, v_receiverId_3891_, v_a_3892_);
lean_dec(v_a_3892_);
return v_res_3894_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(lean_object* v_place_3895_, lean_object* v_x_3896_){
_start:
{
if (lean_obj_tag(v_x_3896_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3906_; 
v_a_3898_ = lean_ctor_get(v_x_3896_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_x_3896_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3900_ = v_x_3896_;
v_isShared_3901_ = v_isSharedCheck_3906_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v_x_3896_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3906_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3904_; 
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3919_; 
v_a_3907_ = lean_ctor_get(v_x_3896_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v_x_3896_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3909_ = v_x_3896_;
v_isShared_3910_ = v_isSharedCheck_3919_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v_x_3896_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3919_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v_capacity_3911_; lean_object* v_buffer_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3916_; 
v_capacity_3911_ = lean_ctor_get(v_a_3907_, 2);
lean_inc(v_capacity_3911_);
v_buffer_3912_ = lean_ctor_get(v_a_3907_, 4);
lean_inc_ref(v_buffer_3912_);
lean_dec(v_a_3907_);
v___x_3913_ = lean_nat_mod(v_place_3895_, v_capacity_3911_);
lean_dec(v_capacity_3911_);
v___x_3914_ = lean_array_fget(v_buffer_3912_, v___x_3913_);
lean_dec(v___x_3913_);
lean_dec_ref(v_buffer_3912_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3914_);
v___x_3916_ = v___x_3909_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; 
v___x_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
return v___x_3917_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_place_3895_ = stack[0].m_obj;
lean_object* v_x_3896_ = stack[1].m_obj;
lean_object* v_res_3920_;
v_res_3920_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(v_place_3895_, v_x_3896_);
stack->m_obj
 = v_res_3920_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed(lean_object* v_place_3921_, lean_object* v_x_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0(v_place_3921_, v_x_3922_);
lean_dec(v_place_3921_);
return v_res_3924_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(lean_object* v_place_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v___f_3928_; lean_object* v___x_3929_; uint8_t v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___f_3928_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3928_, 0, v_place_3925_);
v___x_3929_ = lean_unsigned_to_nat(0u);
v___x_3930_ = 0;
v___x_3931_ = lean_st_ref_get(v_a_3926_);
v___x_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
v___x_3934_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_3929_, v___x_3930_, v___x_3933_, v___f_3928_);
return v___x_3934_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_place_3925_ = stack[0].m_obj;
lean_object* v_a_3926_ = stack[1].m_obj;
lean_object* v_res_3935_;
v_res_3935_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3925_, v_a_3926_);
stack->m_obj
 = v_res_3935_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg___boxed(lean_object* v_place_3936_, lean_object* v_a_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3936_, v_a_3937_);
lean_dec(v_a_3937_);
return v_res_3939_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_object* v_00_u03b1_3940_, lean_object* v_place_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v_place_3941_, v_a_3942_);
return v___x_3944_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_place_3941_ = stack[1].m_obj;
lean_object* v_a_3942_ = stack[2].m_obj;
lean_object* v_res_3945_;
v_res_3945_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(lean_box(0), v_place_3941_, v_a_3942_);
stack->m_obj
 = v_res_3945_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___boxed(lean_object* v_00_u03b1_3946_, lean_object* v_place_3947_, lean_object* v_a_3948_, lean_object* v___y_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1(v_00_u03b1_3946_, v_place_3947_, v_a_3948_);
lean_dec(v_a_3948_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__0(lean_object* v___y_3951_){
_start:
{
if (lean_obj_tag(v___y_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3959_; 
v_a_3952_ = lean_ctor_get(v___y_3951_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___y_3951_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3954_ = v___y_3951_;
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___y_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3968_; 
v_a_3960_ = lean_ctor_get(v___y_3951_, 0);
v_isSharedCheck_3968_ = !lean_is_exclusive(v___y_3951_);
if (v_isSharedCheck_3968_ == 0)
{
v___x_3962_ = v___y_3951_;
v_isShared_3963_ = v_isSharedCheck_3968_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___y_3951_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3968_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v_fst_3964_; lean_object* v___x_3966_; 
v_fst_3964_ = lean_ctor_get(v_a_3960_, 0);
lean_inc(v_fst_3964_);
lean_dec(v_a_3960_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v_fst_3964_);
v___x_3966_ = v___x_3962_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_fst_3964_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(lean_object* v_mutex_3969_, lean_object* v_x_3970_){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3972_ = lean_io_basemutex_unlock(v_mutex_3969_);
v___x_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_3969_ = stack[0].m_obj;
lean_object* v_x_3970_ = stack[1].m_obj;
lean_object* v_res_3975_;
v_res_3975_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(v_mutex_3969_, v_x_3970_);
stack->m_obj
 = v_res_3975_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed(lean_object* v_mutex_3976_, lean_object* v_x_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1(v_mutex_3976_, v_x_3977_);
lean_dec(v_x_3977_);
lean_dec(v_mutex_3976_);
return v_res_3979_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(lean_object* v_k_3980_, lean_object* v_ref_3981_, lean_object* v_x_3982_){
_start:
{
if (lean_obj_tag(v_x_3982_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3992_; 
lean_dec(v_ref_3981_);
lean_dec_ref(v_k_3980_);
v_a_3984_ = lean_ctor_get(v_x_3982_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v_x_3982_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3986_ = v_x_3982_;
v_isShared_3987_ = v_isSharedCheck_3992_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v_x_3982_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3992_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3984_);
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
}
else
{
lean_object* v___x_3993_; 
lean_dec_ref_known(v_x_3982_, 1);
v___x_3993_ = lean_apply_2(v_k_3980_, v_ref_3981_, lean_box(0));
return v___x_3993_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3980_ = stack[0].m_obj;
lean_object* v_ref_3981_ = stack[1].m_obj;
lean_object* v_x_3982_ = stack[2].m_obj;
lean_object* v_res_3994_;
v_res_3994_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(v_k_3980_, v_ref_3981_, v_x_3982_);
stack->m_obj
 = v_res_3994_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed(lean_object* v_k_3995_, lean_object* v_ref_3996_, lean_object* v_x_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2(v_k_3995_, v_ref_3996_, v_x_3997_);
return v_res_3999_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(lean_object* v_mutex_4000_, lean_object* v___f_4001_){
_start:
{
lean_object* v___x_4003_; uint8_t v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = 0;
v___x_4005_ = lean_io_basemutex_lock(v_mutex_4000_);
v___x_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
v___x_4008_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4003_, v___x_4004_, v___x_4007_, v___f_4001_);
return v___x_4008_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_4000_ = stack[0].m_obj;
lean_object* v___f_4001_ = stack[1].m_obj;
lean_object* v_res_4009_;
v_res_4009_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(v_mutex_4000_, v___f_4001_);
stack->m_obj
 = v_res_4009_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3___boxed(lean_object* v_mutex_4010_, lean_object* v___f_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3(v_mutex_4010_, v___f_4011_);
lean_dec(v_mutex_4010_);
return v_res_4013_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(lean_object* v_mutex_4015_, lean_object* v_k_4016_){
_start:
{
lean_object* v_ref_4018_; lean_object* v_mutex_4019_; lean_object* v___f_4020_; lean_object* v___f_4021_; lean_object* v___f_4022_; lean_object* v___f_4023_; lean_object* v___x_4024_; uint8_t v___x_4025_; lean_object* v___x_4026_; lean_object* v___y_4028_; 
v_ref_4018_ = lean_ctor_get(v_mutex_4015_, 0);
lean_inc(v_ref_4018_);
v_mutex_4019_ = lean_ctor_get(v_mutex_4015_, 1);
lean_inc_n(v_mutex_4019_, 2);
lean_dec_ref(v_mutex_4015_);
v___f_4020_ = ((lean_object*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___closed__0));
v___f_4021_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4021_, 0, v_mutex_4019_);
v___f_4022_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4022_, 0, v_k_4016_);
lean_closure_set(v___f_4022_, 1, v_ref_4018_);
v___f_4023_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_4023_, 0, v_mutex_4019_);
lean_closure_set(v___f_4023_, 1, v___f_4022_);
v___x_4024_ = lean_unsigned_to_nat(0u);
v___x_4025_ = 0;
v___x_4026_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_4023_, v___f_4021_, v___x_4024_, v___x_4025_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4030_; 
v_a_4030_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4026_, 1);
if (lean_obj_tag(v_a_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
v_a_4031_ = lean_ctor_get(v_a_4030_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v_a_4030_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v_a_4030_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v_a_4030_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
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
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
v___y_4028_ = v___x_4036_;
goto v___jp_4027_;
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4047_; 
v_a_4039_ = lean_ctor_get(v_a_4030_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v_a_4030_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4041_ = v_a_4030_;
v_isShared_4042_ = v_isSharedCheck_4047_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v_a_4030_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4047_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v_fst_4043_; lean_object* v___x_4045_; 
v_fst_4043_ = lean_ctor_get(v_a_4039_, 0);
lean_inc(v_fst_4043_);
lean_dec(v_a_4039_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 0, v_fst_4043_);
v___x_4045_ = v___x_4041_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_fst_4043_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
v___y_4028_ = v___x_4045_;
goto v___jp_4027_;
}
}
}
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4056_; 
v_a_4048_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4050_ = v___x_4026_;
v_isShared_4051_ = v_isSharedCheck_4056_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4026_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4056_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4052_; lean_object* v___x_4054_; 
v___x_4052_ = lean_task_map(v___f_4020_, v_a_4048_, v___x_4024_, v___x_4025_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v___x_4052_);
v___x_4054_ = v___x_4050_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v___x_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
v___jp_4027_:
{
lean_object* v___x_4029_; 
v___x_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___y_4028_);
return v___x_4029_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_4015_ = stack[0].m_obj;
lean_object* v_k_4016_ = stack[1].m_obj;
lean_object* v_res_4057_;
v_res_4057_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_4015_, v_k_4016_);
stack->m_obj
 = v_res_4057_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg___boxed(lean_object* v_mutex_4058_, lean_object* v_k_4059_, lean_object* v___y_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_4058_, v_k_4059_);
return v_res_4061_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_object* v_00_u03b1_4062_, lean_object* v_00_u03b2_4063_, lean_object* v_mutex_4064_, lean_object* v_k_4065_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___redArg(v_mutex_4064_, v_k_4065_);
return v___x_4067_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_4064_ = stack[2].m_obj;
lean_object* v_k_4065_ = stack[3].m_obj;
lean_object* v_res_4068_;
v_res_4068_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(lean_box(0), lean_box(0), v_mutex_4064_, v_k_4065_);
stack->m_obj
 = v_res_4068_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed(lean_object* v_00_u03b1_4069_, lean_object* v_00_u03b2_4070_, lean_object* v_mutex_4071_, lean_object* v_k_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2(v_00_u03b1_4069_, v_00_u03b2_4070_, v_mutex_4071_, v_k_4072_);
return v_res_4074_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(lean_object* v_producers_4079_, lean_object* v_capacity_4080_, lean_object* v_size_4081_, lean_object* v_buffer_4082_, lean_object* v_write_4083_, lean_object* v_read_4084_, lean_object* v_receivers_4085_, lean_object* v_nextId_4086_, uint8_t v_closed_4087_, lean_object* v_pos_4088_, lean_object* v___y_4089_, lean_object* v_x_4090_){
_start:
{
if (lean_obj_tag(v_x_4090_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4100_; 
lean_dec(v_pos_4088_);
lean_dec(v_nextId_4086_);
lean_dec(v_receivers_4085_);
lean_dec(v_read_4084_);
lean_dec(v_write_4083_);
lean_dec_ref(v_buffer_4082_);
lean_dec(v_size_4081_);
lean_dec(v_capacity_4080_);
lean_dec_ref(v_producers_4079_);
v_a_4092_ = lean_ctor_get(v_x_4090_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_x_4090_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4094_ = v_x_4090_;
v_isShared_4095_ = v_isSharedCheck_4100_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v_x_4090_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4100_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
lean_object* v___x_4098_; 
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
return v___x_4098_;
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v_a_4101_ = lean_ctor_get(v_x_4090_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v_x_4090_, 1);
v___x_4102_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4102_, 0, v_producers_4079_);
lean_ctor_set(v___x_4102_, 1, v_a_4101_);
lean_ctor_set(v___x_4102_, 2, v_capacity_4080_);
lean_ctor_set(v___x_4102_, 3, v_size_4081_);
lean_ctor_set(v___x_4102_, 4, v_buffer_4082_);
lean_ctor_set(v___x_4102_, 5, v_write_4083_);
lean_ctor_set(v___x_4102_, 6, v_read_4084_);
lean_ctor_set(v___x_4102_, 7, v_receivers_4085_);
lean_ctor_set(v___x_4102_, 8, v_nextId_4086_);
lean_ctor_set(v___x_4102_, 9, v_pos_4088_);
lean_ctor_set_uint8(v___x_4102_, sizeof(void*)*10, v_closed_4087_);
v___x_4103_ = lean_st_ref_swap(v___y_4089_, v___x_4102_);
lean_dec(v___x_4103_);
v___x_4104_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_4104_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_producers_4079_ = stack[0].m_obj;
lean_object* v_capacity_4080_ = stack[1].m_obj;
lean_object* v_size_4081_ = stack[2].m_obj;
lean_object* v_buffer_4082_ = stack[3].m_obj;
lean_object* v_write_4083_ = stack[4].m_obj;
lean_object* v_read_4084_ = stack[5].m_obj;
lean_object* v_receivers_4085_ = stack[6].m_obj;
lean_object* v_nextId_4086_ = stack[7].m_obj;
uint8_t v_closed_4087_ = stack[8].m_num;
lean_object* v_pos_4088_ = stack[9].m_obj;
lean_object* v___y_4089_ = stack[10].m_obj;
lean_object* v_x_4090_ = stack[11].m_obj;
lean_object* v_res_4105_;
v_res_4105_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(v_producers_4079_, v_capacity_4080_, v_size_4081_, v_buffer_4082_, v_write_4083_, v_read_4084_, v_receivers_4085_, v_nextId_4086_, v_closed_4087_, v_pos_4088_, v___y_4089_, v_x_4090_);
stack->m_obj
 = v_res_4105_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed(lean_object* v_producers_4106_, lean_object* v_capacity_4107_, lean_object* v_size_4108_, lean_object* v_buffer_4109_, lean_object* v_write_4110_, lean_object* v_read_4111_, lean_object* v_receivers_4112_, lean_object* v_nextId_4113_, lean_object* v_closed_4114_, lean_object* v_pos_4115_, lean_object* v___y_4116_, lean_object* v_x_4117_, lean_object* v___y_4118_){
_start:
{
uint8_t v_closed_boxed_4119_; lean_object* v_res_4120_; 
v_closed_boxed_4119_ = lean_unbox(v_closed_4114_);
v_res_4120_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0(v_producers_4106_, v_capacity_4107_, v_size_4108_, v_buffer_4109_, v_write_4110_, v_read_4111_, v_receivers_4112_, v_nextId_4113_, v_closed_boxed_4119_, v_pos_4115_, v___y_4116_, v_x_4117_);
lean_dec(v___y_4116_);
return v_res_4120_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(lean_object* v_x_4121_){
_start:
{
if (lean_obj_tag(v_x_4121_) == 0)
{
lean_object* v___x_4123_; 
v___x_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4123_, 0, v_x_4121_);
return v___x_4123_;
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4133_; 
v_a_4124_ = lean_ctor_get(v_x_4121_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v_x_4121_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4126_ = v_x_4121_;
v_isShared_4127_ = v_isSharedCheck_4133_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v_x_4121_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4133_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4128_; lean_object* v___x_4130_; 
v___x_4128_ = l_List_reverse___redArg(v_a_4124_);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 0, v___x_4128_);
v___x_4130_ = v___x_4126_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4128_);
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
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4121_ = stack[0].m_obj;
lean_object* v_res_4134_;
v_res_4134_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(v_x_4121_);
stack->m_obj
 = v_res_4134_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0___boxed(lean_object* v_x_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__0(v_x_4135_);
return v_res_4137_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(lean_object* v_a_4138_, lean_object* v___x_4139_, lean_object* v_x_4140_){
_start:
{
if (lean_obj_tag(v_x_4140_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4150_; 
lean_dec(v___x_4139_);
lean_dec(v_a_4138_);
v_a_4142_ = lean_ctor_get(v_x_4140_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v_x_4140_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4144_ = v_x_4140_;
v_isShared_4145_ = v_isSharedCheck_4150_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v_x_4140_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4150_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
lean_object* v___x_4148_; 
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
return v___x_4148_;
}
}
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4167_; 
v_a_4151_ = lean_ctor_get(v_x_4140_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v_x_4140_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4153_ = v_x_4140_;
v_isShared_4154_ = v_isSharedCheck_4167_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v_x_4140_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4167_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
uint8_t v___x_4155_; 
v___x_4155_ = l_List_isEmpty___redArg(v_a_4138_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4156_; lean_object* v___x_4158_; 
lean_dec(v___x_4139_);
v___x_4156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4156_, 0, v_a_4151_);
lean_ctor_set(v___x_4156_, 1, v_a_4138_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v___x_4156_);
v___x_4158_ = v___x_4153_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4156_);
v___x_4158_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
lean_object* v___x_4159_; 
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
return v___x_4159_;
}
}
else
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4164_; 
lean_dec(v_a_4138_);
v___x_4161_ = l_List_reverse___redArg(v_a_4151_);
v___x_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4139_);
lean_ctor_set(v___x_4162_, 1, v___x_4161_);
if (v_isShared_4154_ == 0)
{
lean_ctor_set(v___x_4153_, 0, v___x_4162_);
v___x_4164_ = v___x_4153_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4162_);
v___x_4164_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_object* v___x_4165_; 
v___x_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
return v___x_4165_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4138_ = stack[0].m_obj;
lean_object* v___x_4139_ = stack[1].m_obj;
lean_object* v_x_4140_ = stack[2].m_obj;
lean_object* v_res_4168_;
v_res_4168_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(v_a_4138_, v___x_4139_, v_x_4140_);
stack->m_obj
 = v_res_4168_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed(lean_object* v_a_4169_, lean_object* v___x_4170_, lean_object* v_x_4171_, lean_object* v___y_4172_){
_start:
{
lean_object* v_res_4173_; 
v_res_4173_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2(v_a_4169_, v___x_4170_, v_x_4171_);
return v_res_4173_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(lean_object* v_x_4174_){
_start:
{
uint8_t v___y_4177_; 
if (lean_obj_tag(v_x_4174_) == 0)
{
lean_object* v___x_4181_; 
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v_x_4174_);
return v___x_4181_;
}
else
{
lean_object* v_a_4182_; uint8_t v___x_4183_; 
v_a_4182_ = lean_ctor_get(v_x_4174_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v_x_4174_, 1);
v___x_4183_ = lean_unbox(v_a_4182_);
lean_dec(v_a_4182_);
if (v___x_4183_ == 0)
{
uint8_t v___x_4184_; 
v___x_4184_ = 1;
v___y_4177_ = v___x_4184_;
goto v___jp_4176_;
}
else
{
uint8_t v___x_4185_; 
v___x_4185_ = 0;
v___y_4177_ = v___x_4185_;
goto v___jp_4176_;
}
}
v___jp_4176_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4178_ = lean_box(v___y_4177_);
v___x_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
return v___x_4180_;
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4174_ = stack[0].m_obj;
lean_object* v_res_4186_;
v_res_4186_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(v_x_4174_);
stack->m_obj
 = v_res_4186_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1___boxed(lean_object* v_x_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_res_4189_; 
v_res_4189_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__1(v_x_4187_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed(lean_object* v_tail_4190_, lean_object* v_x_4191_, lean_object* v_head_4192_, lean_object* v_x_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(v_tail_4190_, v_x_4191_, v_head_4192_, v_x_4193_);
return v_res_4195_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(lean_object* v_x_4202_, lean_object* v_x_4203_){
_start:
{
if (lean_obj_tag(v_x_4202_) == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4205_, 0, v_x_4203_);
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
return v___x_4206_;
}
else
{
lean_object* v_head_4207_; lean_object* v_tail_4208_; lean_object* v_waiter_4209_; lean_object* v___f_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; 
v_head_4207_ = lean_ctor_get(v_x_4202_, 0);
lean_inc(v_head_4207_);
v_tail_4208_ = lean_ctor_get(v_x_4202_, 1);
lean_inc(v_tail_4208_);
lean_dec_ref_known(v_x_4202_, 2);
v_waiter_4209_ = lean_ctor_get(v_head_4207_, 1);
lean_inc(v_waiter_4209_);
v___f_4210_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4210_, 0, v_tail_4208_);
lean_closure_set(v___f_4210_, 1, v_x_4203_);
lean_closure_set(v___f_4210_, 2, v_head_4207_);
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4212_ = 0;
if (lean_obj_tag(v_waiter_4209_) == 0)
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
v___x_4213_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__1));
v___x_4214_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4211_, v___x_4212_, v___x_4213_, v___f_4210_);
return v___x_4214_;
}
else
{
lean_object* v_val_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4228_; 
v_val_4215_ = lean_ctor_get(v_waiter_4209_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v_waiter_4209_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4217_ = v_waiter_4209_;
v_isShared_4218_ = v_isSharedCheck_4228_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_val_4215_);
lean_dec(v_waiter_4209_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4228_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v_finished_4219_; lean_object* v___f_4220_; lean_object* v___x_4221_; lean_object* v___x_4223_; 
v_finished_4219_ = lean_ctor_get(v_val_4215_, 0);
lean_inc(v_finished_4219_);
lean_dec(v_val_4215_);
v___f_4220_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___closed__2));
v___x_4221_ = lean_st_ref_get(v_finished_4219_);
lean_dec(v_finished_4219_);
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 0, v___x_4221_);
v___x_4223_ = v___x_4217_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4221_);
v___x_4223_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4223_);
v___x_4225_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4211_, v___x_4212_, v___x_4224_, v___f_4220_);
v___x_4226_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4211_, v___x_4212_, v___x_4225_, v___f_4210_);
return v___x_4226_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4202_ = stack[0].m_obj;
lean_object* v_x_4203_ = stack[1].m_obj;
lean_object* v_res_4229_;
v_res_4229_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4202_, v_x_4203_);
stack->m_obj
 = v_res_4229_;
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(lean_object* v_tail_4230_, lean_object* v_x_4231_, lean_object* v_head_4232_, lean_object* v_x_4233_){
_start:
{
if (lean_obj_tag(v_x_4233_) == 0)
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4243_; 
lean_dec_ref(v_head_4232_);
lean_dec(v_x_4231_);
lean_dec(v_tail_4230_);
v_a_4235_ = lean_ctor_get(v_x_4233_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v_x_4233_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4237_ = v_x_4233_;
v_isShared_4238_ = v_isSharedCheck_4243_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v_x_4233_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4243_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
lean_object* v___x_4241_; 
v___x_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
return v___x_4241_;
}
}
}
else
{
lean_object* v_a_4244_; uint8_t v___x_4245_; 
v_a_4244_ = lean_ctor_get(v_x_4233_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v_x_4233_, 1);
v___x_4245_ = lean_unbox(v_a_4244_);
lean_dec(v_a_4244_);
if (v___x_4245_ == 0)
{
lean_object* v___x_4246_; 
lean_dec_ref(v_head_4232_);
v___x_4246_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4230_, v_x_4231_);
return v___x_4246_;
}
else
{
lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4247_, 0, v_head_4232_);
lean_ctor_set(v___x_4247_, 1, v_x_4231_);
v___x_4248_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_tail_4230_, v___x_4247_);
return v___x_4248_;
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_4230_ = stack[0].m_obj;
lean_object* v_x_4231_ = stack[1].m_obj;
lean_object* v_head_4232_ = stack[2].m_obj;
lean_object* v_x_4233_ = stack[3].m_obj;
lean_object* v_res_4249_;
v_res_4249_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___lam__0(v_tail_4230_, v_x_4231_, v_head_4232_, v_x_4233_);
stack->m_obj
 = v_res_4249_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg___boxed(lean_object* v_x_4250_, lean_object* v_x_4251_, lean_object* v___y_4252_){
_start:
{
lean_object* v_res_4253_; 
v_res_4253_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_4250_, v_x_4251_);
return v_res_4253_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(lean_object* v___x_4254_, lean_object* v_eList_4255_, lean_object* v___f_4256_, lean_object* v_x_4257_){
_start:
{
if (lean_obj_tag(v_x_4257_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4267_; 
lean_dec_ref(v___f_4256_);
lean_dec(v_eList_4255_);
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
lean_object* v_a_4268_; lean_object* v___f_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v_a_4268_ = lean_ctor_get(v_x_4257_, 0);
lean_inc(v_a_4268_);
lean_dec_ref_known(v_x_4257_, 1);
lean_inc(v___x_4254_);
v___f_4269_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4269_, 0, v_a_4268_);
lean_closure_set(v___f_4269_, 1, v___x_4254_);
v___x_4270_ = lean_unsigned_to_nat(0u);
v___x_4271_ = 0;
v___x_4272_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_eList_4255_, v___x_4254_);
v___x_4273_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4270_, v___x_4271_, v___x_4272_, v___f_4256_);
v___x_4274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4270_, v___x_4271_, v___x_4273_, v___f_4269_);
return v___x_4274_;
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4254_ = stack[0].m_obj;
lean_object* v_eList_4255_ = stack[1].m_obj;
lean_object* v___f_4256_ = stack[2].m_obj;
lean_object* v_x_4257_ = stack[3].m_obj;
lean_object* v_res_4275_;
v_res_4275_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(v___x_4254_, v_eList_4255_, v___f_4256_, v_x_4257_);
stack->m_obj
 = v_res_4275_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed(lean_object* v___x_4276_, lean_object* v_eList_4277_, lean_object* v___f_4278_, lean_object* v_x_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1(v___x_4276_, v_eList_4277_, v___f_4278_, v_x_4279_);
return v_res_4281_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(lean_object* v_q_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v_eList_4286_; lean_object* v_dList_4287_; lean_object* v___f_4288_; lean_object* v___x_4289_; lean_object* v___f_4290_; lean_object* v___x_4291_; uint8_t v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_eList_4286_ = lean_ctor_get(v_q_4283_, 0);
lean_inc(v_eList_4286_);
v_dList_4287_ = lean_ctor_get(v_q_4283_, 1);
lean_inc(v_dList_4287_);
lean_dec_ref(v_q_4283_);
v___f_4288_ = ((lean_object*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___closed__0));
v___x_4289_ = lean_box(0);
v___f_4290_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4290_, 0, v___x_4289_);
lean_closure_set(v___f_4290_, 1, v_eList_4286_);
lean_closure_set(v___f_4290_, 2, v___f_4288_);
v___x_4291_ = lean_unsigned_to_nat(0u);
v___x_4292_ = 0;
v___x_4293_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_dList_4287_, v___x_4289_);
v___x_4294_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4291_, v___x_4292_, v___x_4293_, v___f_4288_);
v___x_4295_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4291_, v___x_4292_, v___x_4294_, v___f_4290_);
return v___x_4295_;
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_4283_ = stack[0].m_obj;
lean_object* v___y_4284_ = stack[1].m_obj;
lean_object* v_res_4296_;
v_res_4296_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4283_, v___y_4284_);
stack->m_obj
 = v_res_4296_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg___boxed(lean_object* v_q_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_4297_, v___y_4298_);
lean_dec(v___y_4298_);
return v_res_4300_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(lean_object* v___y_4301_, lean_object* v_x_4302_){
_start:
{
if (lean_obj_tag(v_x_4302_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4312_; 
v_a_4304_ = lean_ctor_get(v_x_4302_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_x_4302_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4306_ = v_x_4302_;
v_isShared_4307_ = v_isSharedCheck_4312_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v_x_4302_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4312_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
lean_object* v___x_4310_; 
v___x_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4309_);
return v___x_4310_;
}
}
}
else
{
lean_object* v_a_4313_; lean_object* v_producers_4314_; lean_object* v_waiters_4315_; lean_object* v_capacity_4316_; lean_object* v_size_4317_; lean_object* v_buffer_4318_; lean_object* v_write_4319_; lean_object* v_read_4320_; lean_object* v_receivers_4321_; lean_object* v_nextId_4322_; uint8_t v_closed_4323_; lean_object* v_pos_4324_; lean_object* v___x_4325_; lean_object* v___f_4326_; lean_object* v___x_4327_; uint8_t v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; 
v_a_4313_ = lean_ctor_get(v_x_4302_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v_x_4302_, 1);
v_producers_4314_ = lean_ctor_get(v_a_4313_, 0);
lean_inc_ref(v_producers_4314_);
v_waiters_4315_ = lean_ctor_get(v_a_4313_, 1);
lean_inc_ref(v_waiters_4315_);
v_capacity_4316_ = lean_ctor_get(v_a_4313_, 2);
lean_inc(v_capacity_4316_);
v_size_4317_ = lean_ctor_get(v_a_4313_, 3);
lean_inc(v_size_4317_);
v_buffer_4318_ = lean_ctor_get(v_a_4313_, 4);
lean_inc_ref(v_buffer_4318_);
v_write_4319_ = lean_ctor_get(v_a_4313_, 5);
lean_inc(v_write_4319_);
v_read_4320_ = lean_ctor_get(v_a_4313_, 6);
lean_inc(v_read_4320_);
v_receivers_4321_ = lean_ctor_get(v_a_4313_, 7);
lean_inc(v_receivers_4321_);
v_nextId_4322_ = lean_ctor_get(v_a_4313_, 8);
lean_inc(v_nextId_4322_);
v_closed_4323_ = lean_ctor_get_uint8(v_a_4313_, sizeof(void*)*10);
v_pos_4324_ = lean_ctor_get(v_a_4313_, 9);
lean_inc(v_pos_4324_);
lean_dec(v_a_4313_);
v___x_4325_ = lean_box(v_closed_4323_);
lean_inc(v___y_4301_);
v___f_4326_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___boxed), 13, 11);
lean_closure_set(v___f_4326_, 0, v_producers_4314_);
lean_closure_set(v___f_4326_, 1, v_capacity_4316_);
lean_closure_set(v___f_4326_, 2, v_size_4317_);
lean_closure_set(v___f_4326_, 3, v_buffer_4318_);
lean_closure_set(v___f_4326_, 4, v_write_4319_);
lean_closure_set(v___f_4326_, 5, v_read_4320_);
lean_closure_set(v___f_4326_, 6, v_receivers_4321_);
lean_closure_set(v___f_4326_, 7, v_nextId_4322_);
lean_closure_set(v___f_4326_, 8, v___x_4325_);
lean_closure_set(v___f_4326_, 9, v_pos_4324_);
lean_closure_set(v___f_4326_, 10, v___y_4301_);
v___x_4327_ = lean_unsigned_to_nat(0u);
v___x_4328_ = 0;
v___x_4329_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_waiters_4315_, v___y_4301_);
v___x_4330_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4327_, v___x_4328_, v___x_4329_, v___f_4326_);
return v___x_4330_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4301_ = stack[0].m_obj;
lean_object* v_x_4302_ = stack[1].m_obj;
lean_object* v_res_4331_;
v_res_4331_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(v___y_4301_, v_x_4302_);
stack->m_obj
 = v_res_4331_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed(lean_object* v___y_4332_, lean_object* v_x_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1(v___y_4332_, v_x_4333_);
lean_dec(v___y_4332_);
return v_res_4335_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(lean_object* v___y_4336_){
_start:
{
lean_object* v___f_4338_; lean_object* v___x_4339_; uint8_t v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
lean_inc(v___y_4336_);
v___f_4338_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_4338_, 0, v___y_4336_);
v___x_4339_ = lean_unsigned_to_nat(0u);
v___x_4340_ = 0;
v___x_4341_ = lean_st_ref_get(v___y_4336_);
v___x_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4341_);
v___x_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
v___x_4344_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4339_, v___x_4340_, v___x_4343_, v___f_4338_);
return v___x_4344_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4336_ = stack[0].m_obj;
lean_object* v_res_4345_;
v_res_4345_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(v___y_4336_);
stack->m_obj
 = v_res_4345_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2___boxed(lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__2(v___y_4346_);
lean_dec(v___y_4346_);
return v_res_4348_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(lean_object* v_ch_4349_, lean_object* v_waiter_4350_){
_start:
{
lean_object* v_val_4353_; lean_object* v___x_4355_; 
v___x_4355_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_registerAux___redArg(v_ch_4349_, v_waiter_4350_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4363_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4363_ == 0)
{
v___x_4358_ = v___x_4355_;
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4355_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4363_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4361_; 
if (v_isShared_4359_ == 0)
{
lean_ctor_set_tag(v___x_4358_, 1);
v___x_4361_ = v___x_4358_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
v___x_4361_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
v_val_4353_ = v___x_4361_;
goto v___jp_4352_;
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
v_a_4364_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4355_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4355_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
lean_ctor_set_tag(v___x_4366_, 0);
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
v_val_4353_ = v___x_4369_;
goto v___jp_4352_;
}
}
}
v___jp_4352_:
{
lean_object* v___x_4354_; 
v___x_4354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4354_, 0, v_val_4353_);
return v___x_4354_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_4349_ = stack[0].m_obj;
lean_object* v_waiter_4350_ = stack[1].m_obj;
lean_object* v_res_4372_;
v_res_4372_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(v_ch_4349_, v_waiter_4350_);
stack->m_obj
 = v_res_4372_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed(lean_object* v_ch_4373_, lean_object* v_waiter_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v_res_4376_; 
v_res_4376_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3(v_ch_4373_, v_waiter_4374_);
return v_res_4376_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(lean_object* v_x_4377_){
_start:
{
if (lean_obj_tag(v_x_4377_) == 0)
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4387_; 
v_a_4379_ = lean_ctor_get(v_x_4377_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v_x_4377_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4381_ = v_x_4377_;
v_isShared_4382_ = v_isSharedCheck_4387_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v_x_4377_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4387_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
lean_object* v___x_4385_; 
v___x_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
return v___x_4385_;
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4397_; 
v_a_4388_ = lean_ctor_get(v_x_4377_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v_x_4377_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4390_ = v_x_4377_;
v_isShared_4391_ = v_isSharedCheck_4397_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v_x_4377_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4397_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4392_; lean_object* v___x_4394_; 
v___x_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4392_, 0, v_a_4388_);
if (v_isShared_4391_ == 0)
{
lean_ctor_set(v___x_4390_, 0, v___x_4392_);
v___x_4394_ = v___x_4390_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4392_);
v___x_4394_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
lean_object* v___x_4395_; 
v___x_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4394_);
return v___x_4395_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4377_ = stack[0].m_obj;
lean_object* v_res_4398_;
v_res_4398_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(v_x_4377_);
stack->m_obj
 = v_res_4398_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4___boxed(lean_object* v_x_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__4(v_x_4399_);
return v_res_4401_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(lean_object* v_x_4402_, lean_object* v_x_4403_){
_start:
{
if (lean_obj_tag(v_x_4403_) == 0)
{
lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4413_; 
lean_dec_ref(v_x_4402_);
v_a_4405_ = lean_ctor_get(v_x_4403_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v_x_4403_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4407_ = v_x_4403_;
v_isShared_4408_ = v_isSharedCheck_4413_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v_x_4403_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4413_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4410_; 
if (v_isShared_4408_ == 0)
{
v___x_4410_ = v___x_4407_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4405_);
v___x_4410_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
lean_object* v___x_4411_; 
v___x_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4410_);
return v___x_4411_;
}
}
}
else
{
lean_object* v___x_4414_; 
lean_dec_ref_known(v_x_4403_, 1);
v___x_4414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4414_, 0, v_x_4402_);
return v___x_4414_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4402_ = stack[0].m_obj;
lean_object* v_x_4403_ = stack[1].m_obj;
lean_object* v_res_4415_;
v_res_4415_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(v_x_4402_, v_x_4403_);
stack->m_obj
 = v_res_4415_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed(lean_object* v_x_4416_, lean_object* v_x_4417_, lean_object* v___y_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0(v_x_4416_, v_x_4417_);
return v_res_4419_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(lean_object* v_a_4422_, lean_object* v_receiverId_4423_, lean_object* v_receivers_4424_, lean_object* v_x_4425_){
_start:
{
if (lean_obj_tag(v_x_4425_) == 0)
{
lean_object* v___x_4427_; 
lean_dec(v_receivers_4424_);
lean_dec(v_receiverId_4423_);
v___x_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4427_, 0, v_x_4425_);
return v___x_4427_;
}
else
{
lean_object* v_a_4428_; 
v_a_4428_ = lean_ctor_get(v_x_4425_, 0);
if (lean_obj_tag(v_a_4428_) == 1)
{
lean_object* v___f_4429_; lean_object* v___x_4430_; uint8_t v___x_4431_; lean_object* v___x_4432_; lean_object* v_producers_4433_; lean_object* v_waiters_4434_; lean_object* v_capacity_4435_; lean_object* v_size_4436_; lean_object* v_buffer_4437_; lean_object* v_write_4438_; lean_object* v_read_4439_; lean_object* v_nextId_4440_; uint8_t v_closed_4441_; lean_object* v_pos_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4453_; 
v___f_4429_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4429_, 0, v_x_4425_);
v___x_4430_ = lean_unsigned_to_nat(0u);
v___x_4431_ = 0;
v___x_4432_ = lean_st_ref_take(v_a_4422_);
v_producers_4433_ = lean_ctor_get(v___x_4432_, 0);
v_waiters_4434_ = lean_ctor_get(v___x_4432_, 1);
v_capacity_4435_ = lean_ctor_get(v___x_4432_, 2);
v_size_4436_ = lean_ctor_get(v___x_4432_, 3);
v_buffer_4437_ = lean_ctor_get(v___x_4432_, 4);
v_write_4438_ = lean_ctor_get(v___x_4432_, 5);
v_read_4439_ = lean_ctor_get(v___x_4432_, 6);
v_nextId_4440_ = lean_ctor_get(v___x_4432_, 8);
v_closed_4441_ = lean_ctor_get_uint8(v___x_4432_, sizeof(void*)*10);
v_pos_4442_ = lean_ctor_get(v___x_4432_, 9);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4453_ == 0)
{
lean_object* v_unused_4454_; 
v_unused_4454_ = lean_ctor_get(v___x_4432_, 7);
lean_dec(v_unused_4454_);
v___x_4444_ = v___x_4432_;
v_isShared_4445_ = v_isSharedCheck_4453_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_pos_4442_);
lean_inc(v_nextId_4440_);
lean_inc(v_read_4439_);
lean_inc(v_write_4438_);
lean_inc(v_buffer_4437_);
lean_inc(v_size_4436_);
lean_inc(v_capacity_4435_);
lean_inc(v_waiters_4434_);
lean_inc(v_producers_4433_);
lean_dec(v___x_4432_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4453_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4446_; lean_object* v___x_4448_; 
v___x_4446_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_spec__0_spec__1(v_receiverId_4423_, v_receivers_4424_);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 7, v___x_4446_);
v___x_4448_ = v___x_4444_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_producers_4433_);
lean_ctor_set(v_reuseFailAlloc_4452_, 1, v_waiters_4434_);
lean_ctor_set(v_reuseFailAlloc_4452_, 2, v_capacity_4435_);
lean_ctor_set(v_reuseFailAlloc_4452_, 3, v_size_4436_);
lean_ctor_set(v_reuseFailAlloc_4452_, 4, v_buffer_4437_);
lean_ctor_set(v_reuseFailAlloc_4452_, 5, v_write_4438_);
lean_ctor_set(v_reuseFailAlloc_4452_, 6, v_read_4439_);
lean_ctor_set(v_reuseFailAlloc_4452_, 7, v___x_4446_);
lean_ctor_set(v_reuseFailAlloc_4452_, 8, v_nextId_4440_);
lean_ctor_set(v_reuseFailAlloc_4452_, 9, v_pos_4442_);
lean_ctor_set_uint8(v_reuseFailAlloc_4452_, sizeof(void*)*10, v_closed_4441_);
v___x_4448_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4449_ = lean_st_ref_put(v_a_4422_, v___x_4448_);
v___x_4450_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4451_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4430_, v___x_4431_, v___x_4450_, v___f_4429_);
return v___x_4451_;
}
}
}
else
{
lean_object* v___x_4455_; 
lean_dec_ref_known(v_x_4425_, 1);
lean_dec(v_receivers_4424_);
lean_dec(v_receiverId_4423_);
v___x_4455_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4455_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4422_ = stack[0].m_obj;
lean_object* v_receiverId_4423_ = stack[1].m_obj;
lean_object* v_receivers_4424_ = stack[2].m_obj;
lean_object* v_x_4425_ = stack[3].m_obj;
lean_object* v_res_4456_;
v_res_4456_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4422_, v_receiverId_4423_, v_receivers_4424_, v_x_4425_);
stack->m_obj
 = v_res_4456_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed(lean_object* v_a_4457_, lean_object* v_receiverId_4458_, lean_object* v_receivers_4459_, lean_object* v_x_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1(v_a_4457_, v_receiverId_4458_, v_receivers_4459_, v_x_4460_);
lean_dec(v_a_4457_);
return v_res_4462_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(lean_object* v_x_4463_){
_start:
{
if (lean_obj_tag(v_x_4463_) == 0)
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4473_; 
v_a_4465_ = lean_ctor_get(v_x_4463_, 0);
v_isSharedCheck_4473_ = !lean_is_exclusive(v_x_4463_);
if (v_isSharedCheck_4473_ == 0)
{
v___x_4467_ = v_x_4463_;
v_isShared_4468_ = v_isSharedCheck_4473_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v_x_4463_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4473_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4472_; 
v_reuseFailAlloc_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4472_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4472_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
lean_object* v___x_4471_; 
v___x_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
return v___x_4471_;
}
}
}
else
{
lean_object* v_a_4474_; lean_object* v___x_4476_; uint8_t v_isShared_4477_; uint8_t v_isSharedCheck_4486_; 
v_a_4474_ = lean_ctor_get(v_x_4463_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v_x_4463_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4476_ = v_x_4463_;
v_isShared_4477_ = v_isSharedCheck_4486_;
goto v_resetjp_4475_;
}
else
{
lean_inc(v_a_4474_);
lean_dec(v_x_4463_);
v___x_4476_ = lean_box(0);
v_isShared_4477_ = v_isSharedCheck_4486_;
goto v_resetjp_4475_;
}
v_resetjp_4475_:
{
lean_object* v_size_4478_; lean_object* v___x_4479_; uint8_t v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4483_; 
v_size_4478_ = lean_ctor_get(v_a_4474_, 3);
lean_inc(v_size_4478_);
lean_dec(v_a_4474_);
v___x_4479_ = lean_unsigned_to_nat(0u);
v___x_4480_ = lean_nat_dec_eq(v_size_4478_, v___x_4479_);
lean_dec(v_size_4478_);
v___x_4481_ = lean_box(v___x_4480_);
if (v_isShared_4477_ == 0)
{
lean_ctor_set(v___x_4476_, 0, v___x_4481_);
v___x_4483_ = v___x_4476_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4481_);
v___x_4483_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
lean_object* v___x_4484_; 
v___x_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4483_);
return v___x_4484_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4463_ = stack[0].m_obj;
lean_object* v_res_4487_;
v_res_4487_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4463_);
stack->m_obj
 = v_res_4487_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0___boxed(lean_object* v_x_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v_res_4490_; 
v_res_4490_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___lam__0(v_x_4488_);
return v_res_4490_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(lean_object* v_a_4492_){
_start:
{
lean_object* v___f_4494_; lean_object* v___x_4495_; uint8_t v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___f_4494_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___closed__0));
v___x_4495_ = lean_unsigned_to_nat(0u);
v___x_4496_ = 0;
v___x_4497_ = lean_st_ref_get(v_a_4492_);
v___x_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4498_, 0, v___x_4497_);
v___x_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
v___x_4500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4495_, v___x_4496_, v___x_4499_, v___f_4494_);
return v___x_4500_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4492_ = stack[0].m_obj;
lean_object* v_res_4501_;
v_res_4501_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4492_);
stack->m_obj
 = v_res_4501_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_a_4502_, lean_object* v___y_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4502_);
lean_dec(v_a_4502_);
return v_res_4504_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(lean_object* v_slot_4505_, lean_object* v_next_4506_){
_start:
{
lean_object* v___x_4508_; lean_object* v_fst_4510_; lean_object* v_snd_4511_; lean_object* v_value_4515_; lean_object* v_pos_4516_; lean_object* v_remaining_4517_; uint8_t v___x_4518_; 
v___x_4508_ = lean_st_ref_take(v_slot_4505_);
v_value_4515_ = lean_ctor_get(v___x_4508_, 0);
v_pos_4516_ = lean_ctor_get(v___x_4508_, 1);
v_remaining_4517_ = lean_ctor_get(v___x_4508_, 2);
v___x_4518_ = lean_nat_dec_eq(v_next_4506_, v_pos_4516_);
if (v___x_4518_ == 0)
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4519_ = lean_box(0);
v___x_4520_ = lean_box(v___x_4518_);
v___x_4521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4521_, 0, v___x_4519_);
lean_ctor_set(v___x_4521_, 1, v___x_4520_);
v_fst_4510_ = v___x_4521_;
v_snd_4511_ = v___x_4508_;
goto v___jp_4509_;
}
else
{
lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4540_; 
lean_inc(v_remaining_4517_);
lean_inc(v_pos_4516_);
lean_inc(v_value_4515_);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4540_ == 0)
{
lean_object* v_unused_4541_; lean_object* v_unused_4542_; lean_object* v_unused_4543_; 
v_unused_4541_ = lean_ctor_get(v___x_4508_, 2);
lean_dec(v_unused_4541_);
v_unused_4542_ = lean_ctor_get(v___x_4508_, 1);
lean_dec(v_unused_4542_);
v_unused_4543_ = lean_ctor_get(v___x_4508_, 0);
lean_dec(v_unused_4543_);
v___x_4523_ = v___x_4508_;
v_isShared_4524_ = v_isSharedCheck_4540_;
goto v_resetjp_4522_;
}
else
{
lean_dec(v___x_4508_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4540_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4525_ = lean_unsigned_to_nat(1u);
v___x_4526_ = lean_nat_dec_eq(v_remaining_4517_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4531_; 
v___x_4527_ = lean_box(v___x_4526_);
lean_inc(v_value_4515_);
v___x_4528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4528_, 0, v_value_4515_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
v___x_4529_ = lean_nat_sub(v_remaining_4517_, v___x_4525_);
lean_dec(v_remaining_4517_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 2, v___x_4529_);
v___x_4531_ = v___x_4523_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v_value_4515_);
lean_ctor_set(v_reuseFailAlloc_4532_, 1, v_pos_4516_);
lean_ctor_set(v_reuseFailAlloc_4532_, 2, v___x_4529_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
v_fst_4510_ = v___x_4528_;
v_snd_4511_ = v___x_4531_;
goto v___jp_4509_;
}
}
else
{
lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4538_; 
lean_dec(v_remaining_4517_);
v___x_4533_ = lean_box(v___x_4518_);
v___x_4534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4534_, 0, v_value_4515_);
lean_ctor_set(v___x_4534_, 1, v___x_4533_);
v___x_4535_ = lean_box(0);
v___x_4536_ = lean_unsigned_to_nat(0u);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 2, v___x_4536_);
lean_ctor_set(v___x_4523_, 0, v___x_4535_);
v___x_4538_ = v___x_4523_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4535_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_pos_4516_);
lean_ctor_set(v_reuseFailAlloc_4539_, 2, v___x_4536_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
v_fst_4510_ = v___x_4534_;
v_snd_4511_ = v___x_4538_;
goto v___jp_4509_;
}
}
}
}
v___jp_4509_:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4512_ = lean_st_ref_put(v_slot_4505_, v_snd_4511_);
v___x_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4513_, 0, v_fst_4510_);
v___x_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4513_);
return v___x_4514_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_slot_4505_ = stack[0].m_obj;
lean_object* v_next_4506_ = stack[1].m_obj;
lean_object* v_res_4544_;
v_res_4544_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4505_, v_next_4506_);
stack->m_obj
 = v_res_4544_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_slot_4545_, lean_object* v_next_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_4545_, v_next_4546_);
lean_dec(v_next_4546_);
lean_dec(v_slot_4545_);
return v_res_4548_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(lean_object* v_next_4549_, uint8_t v_a_4550_, lean_object* v___f_4551_, lean_object* v_x_4552_){
_start:
{
if (lean_obj_tag(v_x_4552_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4562_; 
lean_dec_ref(v___f_4551_);
v_a_4554_ = lean_ctor_get(v_x_4552_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_x_4552_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4556_ = v_x_4552_;
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v_x_4552_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4562_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
lean_object* v___x_4560_; 
v___x_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4560_, 0, v___x_4559_);
return v___x_4560_;
}
}
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; 
v_a_4563_ = lean_ctor_get(v_x_4552_, 0);
lean_inc(v_a_4563_);
lean_dec_ref_known(v_x_4552_, 1);
v___x_4564_ = lean_unsigned_to_nat(0u);
v___x_4565_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_a_4563_, v_next_4549_);
lean_dec(v_a_4563_);
v___x_4566_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4564_, v_a_4550_, v___x_4565_, v___f_4551_);
return v___x_4566_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_next_4549_ = stack[0].m_obj;
uint8_t v_a_4550_ = stack[1].m_num;
lean_object* v___f_4551_ = stack[2].m_obj;
lean_object* v_x_4552_ = stack[3].m_obj;
lean_object* v_res_4567_;
v_res_4567_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4549_, v_a_4550_, v___f_4551_, v_x_4552_);
stack->m_obj
 = v_res_4567_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed(lean_object* v_next_4568_, lean_object* v_a_4569_, lean_object* v___f_4570_, lean_object* v_x_4571_, lean_object* v___y_4572_){
_start:
{
uint8_t v_a_12528__boxed_4573_; lean_object* v_res_4574_; 
v_a_12528__boxed_4573_ = lean_unbox(v_a_4569_);
v_res_4574_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4(v_next_4568_, v_a_12528__boxed_4573_, v___f_4570_, v_x_4571_);
lean_dec(v_next_4568_);
return v_res_4574_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(uint8_t v_a_4575_, lean_object* v___f_4576_, lean_object* v_____r_4577_, lean_object* v_st_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4581_ = lean_unsigned_to_nat(0u);
v___x_4582_ = lean_st_ref_swap(v___y_4579_, v_st_4578_);
lean_dec(v___x_4582_);
v___x_4583_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
v___x_4584_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4581_, v_a_4575_, v___x_4583_, v___f_4576_);
return v___x_4584_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_4575_ = stack[0].m_num;
lean_object* v___f_4576_ = stack[1].m_obj;
lean_object* v_____r_4577_ = stack[2].m_obj;
lean_object* v_st_4578_ = stack[3].m_obj;
lean_object* v___y_4579_ = stack[4].m_obj;
lean_object* v_res_4585_;
v_res_4585_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4575_, v___f_4576_, v_____r_4577_, v_st_4578_, v___y_4579_);
stack->m_obj
 = v_res_4585_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_a_4586_, lean_object* v___f_4587_, lean_object* v_____r_4588_, lean_object* v_st_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
uint8_t v_a_12591__boxed_4592_; lean_object* v_res_4593_; 
v_a_12591__boxed_4592_ = lean_unbox(v_a_4586_);
v_res_4593_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_12591__boxed_4592_, v___f_4587_, v_____r_4588_, v_st_4589_, v___y_4590_);
lean_dec(v___y_4590_);
return v_res_4593_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(lean_object* v_snd_4594_, lean_object* v_waiters_4595_, lean_object* v_capacity_4596_, lean_object* v_size_4597_, lean_object* v_buffer_4598_, lean_object* v_write_4599_, lean_object* v_read_4600_, lean_object* v_receivers_4601_, lean_object* v_nextId_4602_, uint8_t v_closed_4603_, lean_object* v_pos_4604_, lean_object* v___f_4605_, lean_object* v_a_4606_, lean_object* v_x_4607_){
_start:
{
if (lean_obj_tag(v_x_4607_) == 0)
{
lean_object* v_a_4609_; lean_object* v___x_4611_; uint8_t v_isShared_4612_; uint8_t v_isSharedCheck_4617_; 
lean_dec_ref(v___f_4605_);
lean_dec(v_pos_4604_);
lean_dec(v_nextId_4602_);
lean_dec(v_receivers_4601_);
lean_dec(v_read_4600_);
lean_dec(v_write_4599_);
lean_dec_ref(v_buffer_4598_);
lean_dec(v_size_4597_);
lean_dec(v_capacity_4596_);
lean_dec_ref(v_waiters_4595_);
lean_dec_ref(v_snd_4594_);
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
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; 
lean_dec_ref_known(v_x_4607_, 1);
v___x_4618_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_4618_, 0, v_snd_4594_);
lean_ctor_set(v___x_4618_, 1, v_waiters_4595_);
lean_ctor_set(v___x_4618_, 2, v_capacity_4596_);
lean_ctor_set(v___x_4618_, 3, v_size_4597_);
lean_ctor_set(v___x_4618_, 4, v_buffer_4598_);
lean_ctor_set(v___x_4618_, 5, v_write_4599_);
lean_ctor_set(v___x_4618_, 6, v_read_4600_);
lean_ctor_set(v___x_4618_, 7, v_receivers_4601_);
lean_ctor_set(v___x_4618_, 8, v_nextId_4602_);
lean_ctor_set(v___x_4618_, 9, v_pos_4604_);
lean_ctor_set_uint8(v___x_4618_, sizeof(void*)*10, v_closed_4603_);
v___x_4619_ = lean_box(0);
lean_inc(v_a_4606_);
v___x_4620_ = lean_apply_4(v___f_4605_, v___x_4619_, v___x_4618_, v_a_4606_, lean_box(0));
return v___x_4620_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_4594_ = stack[0].m_obj;
lean_object* v_waiters_4595_ = stack[1].m_obj;
lean_object* v_capacity_4596_ = stack[2].m_obj;
lean_object* v_size_4597_ = stack[3].m_obj;
lean_object* v_buffer_4598_ = stack[4].m_obj;
lean_object* v_write_4599_ = stack[5].m_obj;
lean_object* v_read_4600_ = stack[6].m_obj;
lean_object* v_receivers_4601_ = stack[7].m_obj;
lean_object* v_nextId_4602_ = stack[8].m_obj;
uint8_t v_closed_4603_ = stack[9].m_num;
lean_object* v_pos_4604_ = stack[10].m_obj;
lean_object* v___f_4605_ = stack[11].m_obj;
lean_object* v_a_4606_ = stack[12].m_obj;
lean_object* v_x_4607_ = stack[13].m_obj;
lean_object* v_res_4621_;
v_res_4621_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4594_, v_waiters_4595_, v_capacity_4596_, v_size_4597_, v_buffer_4598_, v_write_4599_, v_read_4600_, v_receivers_4601_, v_nextId_4602_, v_closed_4603_, v_pos_4604_, v___f_4605_, v_a_4606_, v_x_4607_);
stack->m_obj
 = v_res_4621_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed(lean_object* v_snd_4622_, lean_object* v_waiters_4623_, lean_object* v_capacity_4624_, lean_object* v_size_4625_, lean_object* v_buffer_4626_, lean_object* v_write_4627_, lean_object* v_read_4628_, lean_object* v_receivers_4629_, lean_object* v_nextId_4630_, lean_object* v_closed_4631_, lean_object* v_pos_4632_, lean_object* v___f_4633_, lean_object* v_a_4634_, lean_object* v_x_4635_, lean_object* v___y_4636_){
_start:
{
uint8_t v_closed_boxed_4637_; lean_object* v_res_4638_; 
v_closed_boxed_4637_ = lean_unbox(v_closed_4631_);
v_res_4638_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2(v_snd_4622_, v_waiters_4623_, v_capacity_4624_, v_size_4625_, v_buffer_4626_, v_write_4627_, v_read_4628_, v_receivers_4629_, v_nextId_4630_, v_closed_boxed_4637_, v_pos_4632_, v___f_4633_, v_a_4634_, v_x_4635_);
lean_dec(v_a_4634_);
return v_res_4638_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(lean_object* v_fst_4639_, lean_object* v_x_4640_){
_start:
{
if (lean_obj_tag(v_x_4640_) == 0)
{
lean_object* v_a_4642_; lean_object* v___x_4644_; uint8_t v_isShared_4645_; uint8_t v_isSharedCheck_4650_; 
lean_dec(v_fst_4639_);
v_a_4642_ = lean_ctor_get(v_x_4640_, 0);
v_isSharedCheck_4650_ = !lean_is_exclusive(v_x_4640_);
if (v_isSharedCheck_4650_ == 0)
{
v___x_4644_ = v_x_4640_;
v_isShared_4645_ = v_isSharedCheck_4650_;
goto v_resetjp_4643_;
}
else
{
lean_inc(v_a_4642_);
lean_dec(v_x_4640_);
v___x_4644_ = lean_box(0);
v_isShared_4645_ = v_isSharedCheck_4650_;
goto v_resetjp_4643_;
}
v_resetjp_4643_:
{
lean_object* v___x_4647_; 
if (v_isShared_4645_ == 0)
{
v___x_4647_ = v___x_4644_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v_a_4642_);
v___x_4647_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
lean_object* v___x_4648_; 
v___x_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4647_);
return v___x_4648_;
}
}
}
else
{
lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4658_; 
v_isSharedCheck_4658_ = !lean_is_exclusive(v_x_4640_);
if (v_isSharedCheck_4658_ == 0)
{
lean_object* v_unused_4659_; 
v_unused_4659_ = lean_ctor_get(v_x_4640_, 0);
lean_dec(v_unused_4659_);
v___x_4652_ = v_x_4640_;
v_isShared_4653_ = v_isSharedCheck_4658_;
goto v_resetjp_4651_;
}
else
{
lean_dec(v_x_4640_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4658_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 0, v_fst_4639_);
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_fst_4639_);
v___x_4655_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
lean_object* v___x_4656_; 
v___x_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4655_);
return v___x_4656_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_4639_ = stack[0].m_obj;
lean_object* v_x_4640_ = stack[1].m_obj;
lean_object* v_res_4660_;
v_res_4660_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4639_, v_x_4640_);
stack->m_obj
 = v_res_4660_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_fst_4661_, lean_object* v_x_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_res_4664_; 
v_res_4664_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0(v_fst_4661_, v_x_4662_);
return v_res_4664_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(uint8_t v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, uint8_t v___x_4668_, lean_object* v_x_4669_){
_start:
{
if (lean_obj_tag(v_x_4669_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4679_; 
lean_dec_ref(v_a_4666_);
v_a_4671_ = lean_ctor_get(v_x_4669_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_x_4669_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4673_ = v_x_4669_;
v_isShared_4674_ = v_isSharedCheck_4679_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_a_4671_);
lean_dec(v_x_4669_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4679_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4676_; 
if (v_isShared_4674_ == 0)
{
v___x_4676_ = v___x_4673_;
goto v_reusejp_4675_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4671_);
v___x_4676_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4675_;
}
v_reusejp_4675_:
{
lean_object* v___x_4677_; 
v___x_4677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4676_);
return v___x_4677_;
}
}
}
else
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4727_; 
v_a_4680_ = lean_ctor_get(v_x_4669_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v_x_4669_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4682_ = v_x_4669_;
v_isShared_4683_ = v_isSharedCheck_4727_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v_x_4669_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4727_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v_fst_4684_; 
v_fst_4684_ = lean_ctor_get(v_a_4680_, 0);
lean_inc(v_fst_4684_);
if (lean_obj_tag(v_fst_4684_) == 1)
{
lean_object* v_snd_4685_; lean_object* v___f_4686_; lean_object* v___x_4687_; lean_object* v___f_4688_; uint8_t v___x_4689_; 
v_snd_4685_ = lean_ctor_get(v_a_4680_, 1);
lean_inc(v_snd_4685_);
lean_dec(v_a_4680_);
v___f_4686_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_4686_, 0, v_fst_4684_);
v___x_4687_ = lean_box(v_a_4665_);
lean_inc_ref(v___f_4686_);
v___f_4688_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1___boxed), 6, 2);
lean_closure_set(v___f_4688_, 0, v___x_4687_);
lean_closure_set(v___f_4688_, 1, v___f_4686_);
v___x_4689_ = lean_unbox(v_snd_4685_);
lean_dec(v_snd_4685_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; lean_object* v___x_4691_; 
lean_dec_ref(v___f_4688_);
lean_del_object(v___x_4682_);
v___x_4690_ = lean_box(0);
v___x_4691_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4665_, v___f_4686_, v___x_4690_, v_a_4666_, v_a_4667_);
return v___x_4691_;
}
else
{
lean_object* v___x_4692_; lean_object* v_producers_4693_; lean_object* v_waiters_4694_; lean_object* v_capacity_4695_; lean_object* v_size_4696_; lean_object* v_buffer_4697_; lean_object* v_write_4698_; lean_object* v_read_4699_; lean_object* v_receivers_4700_; lean_object* v_nextId_4701_; uint8_t v_closed_4702_; lean_object* v_pos_4703_; lean_object* v___x_4704_; 
v___x_4692_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_dequeue___redArg(v_a_4666_);
v_producers_4693_ = lean_ctor_get(v___x_4692_, 0);
v_waiters_4694_ = lean_ctor_get(v___x_4692_, 1);
v_capacity_4695_ = lean_ctor_get(v___x_4692_, 2);
v_size_4696_ = lean_ctor_get(v___x_4692_, 3);
v_buffer_4697_ = lean_ctor_get(v___x_4692_, 4);
v_write_4698_ = lean_ctor_get(v___x_4692_, 5);
v_read_4699_ = lean_ctor_get(v___x_4692_, 6);
v_receivers_4700_ = lean_ctor_get(v___x_4692_, 7);
v_nextId_4701_ = lean_ctor_get(v___x_4692_, 8);
v_closed_4702_ = lean_ctor_get_uint8(v___x_4692_, sizeof(void*)*10);
v_pos_4703_ = lean_ctor_get(v___x_4692_, 9);
lean_inc_ref(v_producers_4693_);
v___x_4704_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_4693_);
if (lean_obj_tag(v___x_4704_) == 1)
{
lean_object* v_val_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4723_; 
lean_inc(v_pos_4703_);
lean_inc(v_nextId_4701_);
lean_inc(v_receivers_4700_);
lean_inc(v_read_4699_);
lean_inc(v_write_4698_);
lean_inc_ref(v_buffer_4697_);
lean_inc(v_size_4696_);
lean_inc(v_capacity_4695_);
lean_inc_ref(v_waiters_4694_);
lean_dec_ref(v___x_4692_);
lean_dec_ref(v___f_4686_);
v_val_4705_ = lean_ctor_get(v___x_4704_, 0);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4704_);
if (v_isSharedCheck_4723_ == 0)
{
v___x_4707_ = v___x_4704_;
v_isShared_4708_ = v_isSharedCheck_4723_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_val_4705_);
lean_dec(v___x_4704_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4723_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v_fst_4709_; lean_object* v_snd_4710_; lean_object* v___x_4711_; lean_object* v___f_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4717_; 
v_fst_4709_ = lean_ctor_get(v_val_4705_, 0);
lean_inc(v_fst_4709_);
v_snd_4710_ = lean_ctor_get(v_val_4705_, 1);
lean_inc(v_snd_4710_);
lean_dec(v_val_4705_);
v___x_4711_ = lean_box(v_closed_4702_);
lean_inc(v_a_4667_);
v___f_4712_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__2___boxed), 15, 13);
lean_closure_set(v___f_4712_, 0, v_snd_4710_);
lean_closure_set(v___f_4712_, 1, v_waiters_4694_);
lean_closure_set(v___f_4712_, 2, v_capacity_4695_);
lean_closure_set(v___f_4712_, 3, v_size_4696_);
lean_closure_set(v___f_4712_, 4, v_buffer_4697_);
lean_closure_set(v___f_4712_, 5, v_write_4698_);
lean_closure_set(v___f_4712_, 6, v_read_4699_);
lean_closure_set(v___f_4712_, 7, v_receivers_4700_);
lean_closure_set(v___f_4712_, 8, v_nextId_4701_);
lean_closure_set(v___f_4712_, 9, v___x_4711_);
lean_closure_set(v___f_4712_, 10, v_pos_4703_);
lean_closure_set(v___f_4712_, 11, v___f_4688_);
lean_closure_set(v___f_4712_, 12, v_a_4667_);
v___x_4713_ = lean_unsigned_to_nat(0u);
v___x_4714_ = lean_box(v___x_4668_);
v___x_4715_ = lean_io_promise_resolve(v___x_4714_, v_fst_4709_);
lean_dec(v_fst_4709_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v___x_4715_);
v___x_4717_ = v___x_4682_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4715_);
v___x_4717_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
lean_object* v___x_4719_; 
if (v_isShared_4708_ == 0)
{
lean_ctor_set_tag(v___x_4707_, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4717_);
v___x_4719_ = v___x_4707_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v___x_4717_);
v___x_4719_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
lean_object* v___x_4720_; 
v___x_4720_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4713_, v_a_4665_, v___x_4719_, v___f_4712_);
return v___x_4720_;
}
}
}
}
else
{
lean_object* v___x_4724_; lean_object* v___x_4725_; 
lean_dec(v___x_4704_);
lean_dec_ref(v___f_4688_);
lean_del_object(v___x_4682_);
v___x_4724_ = lean_box(0);
v___x_4725_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__1(v_a_4665_, v___f_4686_, v___x_4724_, v___x_4692_, v_a_4667_);
return v___x_4725_;
}
}
}
else
{
lean_object* v___x_4726_; 
lean_dec(v_fst_4684_);
lean_del_object(v___x_4682_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4666_);
v___x_4726_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4726_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_4665_ = stack[0].m_num;
lean_object* v_a_4666_ = stack[1].m_obj;
lean_object* v_a_4667_ = stack[2].m_obj;
uint8_t v___x_4668_ = stack[3].m_num;
lean_object* v_x_4669_ = stack[4].m_obj;
lean_object* v_res_4728_;
v_res_4728_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_4665_, v_a_4666_, v_a_4667_, v___x_4668_, v_x_4669_);
stack->m_obj
 = v_res_4728_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed(lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v___x_4732_, lean_object* v_x_4733_, lean_object* v___y_4734_){
_start:
{
uint8_t v_a_12761__boxed_4735_; uint8_t v___x_12763__boxed_4736_; lean_object* v_res_4737_; 
v_a_12761__boxed_4735_ = lean_unbox(v_a_4729_);
v___x_12763__boxed_4736_ = lean_unbox(v___x_4732_);
v_res_4737_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3(v_a_12761__boxed_4735_, v_a_4730_, v_a_4731_, v___x_12763__boxed_4736_, v_x_4733_);
lean_dec(v_a_4731_);
return v_res_4737_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_next_4740_, lean_object* v_x_4741_){
_start:
{
if (lean_obj_tag(v_x_4741_) == 0)
{
lean_object* v_a_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4751_; 
lean_dec(v_next_4740_);
lean_dec_ref(v_a_4738_);
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
lean_object* v_a_4752_; uint8_t v___x_4753_; 
v_a_4752_ = lean_ctor_get(v_x_4741_, 0);
lean_inc(v_a_4752_);
lean_dec_ref_known(v_x_4741_, 1);
v___x_4753_ = lean_unbox(v_a_4752_);
if (v___x_4753_ == 0)
{
lean_object* v_capacity_4754_; uint8_t v___x_4755_; lean_object* v___x_4756_; lean_object* v___f_4757_; lean_object* v___f_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; uint8_t v___x_4762_; lean_object* v___x_4763_; 
v_capacity_4754_ = lean_ctor_get(v_a_4738_, 2);
lean_inc(v_capacity_4754_);
v___x_4755_ = 1;
v___x_4756_ = lean_box(v___x_4755_);
lean_inc(v_a_4739_);
lean_inc_n(v_a_4752_, 2);
v___f_4757_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__3___boxed), 6, 4);
lean_closure_set(v___f_4757_, 0, v_a_4752_);
lean_closure_set(v___f_4757_, 1, v_a_4738_);
lean_closure_set(v___f_4757_, 2, v_a_4739_);
lean_closure_set(v___f_4757_, 3, v___x_4756_);
lean_inc(v_next_4740_);
v___f_4758_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__4___boxed), 5, 3);
lean_closure_set(v___f_4758_, 0, v_next_4740_);
lean_closure_set(v___f_4758_, 1, v_a_4752_);
lean_closure_set(v___f_4758_, 2, v___f_4757_);
v___x_4759_ = lean_nat_mod(v_next_4740_, v_capacity_4754_);
lean_dec(v_capacity_4754_);
lean_dec(v_next_4740_);
v___x_4760_ = lean_unsigned_to_nat(0u);
v___x_4761_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4759_, v_a_4739_);
v___x_4762_ = lean_unbox(v_a_4752_);
lean_dec(v_a_4752_);
v___x_4763_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4760_, v___x_4762_, v___x_4761_, v___f_4758_);
return v___x_4763_;
}
else
{
lean_object* v___x_4764_; 
lean_dec(v_a_4752_);
lean_dec(v_next_4740_);
lean_dec_ref(v_a_4738_);
v___x_4764_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4764_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4738_ = stack[0].m_obj;
lean_object* v_a_4739_ = stack[1].m_obj;
lean_object* v_next_4740_ = stack[2].m_obj;
lean_object* v_x_4741_ = stack[3].m_obj;
lean_object* v_res_4765_;
v_res_4765_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4738_, v_a_4739_, v_next_4740_, v_x_4741_);
stack->m_obj
 = v_res_4765_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed(lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_next_4768_, lean_object* v_x_4769_, lean_object* v___y_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5(v_a_4766_, v_a_4767_, v_next_4768_, v_x_4769_);
lean_dec(v_a_4767_);
return v_res_4771_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(lean_object* v_a_4772_, lean_object* v_next_4773_, lean_object* v_x_4774_){
_start:
{
if (lean_obj_tag(v_x_4774_) == 0)
{
lean_object* v_a_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4784_; 
lean_dec(v_next_4773_);
v_a_4776_ = lean_ctor_get(v_x_4774_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v_x_4774_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4778_ = v_x_4774_;
v_isShared_4779_ = v_isSharedCheck_4784_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_a_4776_);
lean_dec(v_x_4774_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4784_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4781_; 
if (v_isShared_4779_ == 0)
{
v___x_4781_ = v___x_4778_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4783_; 
v_reuseFailAlloc_4783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4783_, 0, v_a_4776_);
v___x_4781_ = v_reuseFailAlloc_4783_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4782_; 
v___x_4782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4781_);
return v___x_4782_;
}
}
}
else
{
lean_object* v_a_4785_; lean_object* v___f_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; 
v_a_4785_ = lean_ctor_get(v_x_4774_, 0);
lean_inc(v_a_4785_);
lean_dec_ref_known(v_x_4774_, 1);
lean_inc(v_a_4772_);
v___f_4786_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_4786_, 0, v_a_4785_);
lean_closure_set(v___f_4786_, 1, v_a_4772_);
lean_closure_set(v___f_4786_, 2, v_next_4773_);
v___x_4787_ = lean_unsigned_to_nat(0u);
v___x_4788_ = 0;
v___x_4789_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_4772_);
v___x_4790_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4787_, v___x_4788_, v___x_4789_, v___f_4786_);
return v___x_4790_;
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4772_ = stack[0].m_obj;
lean_object* v_next_4773_ = stack[1].m_obj;
lean_object* v_x_4774_ = stack[2].m_obj;
lean_object* v_res_4791_;
v_res_4791_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4772_, v_next_4773_, v_x_4774_);
stack->m_obj
 = v_res_4791_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed(lean_object* v_a_4792_, lean_object* v_next_4793_, lean_object* v_x_4794_, lean_object* v___y_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6(v_a_4792_, v_next_4793_, v_x_4794_);
lean_dec(v_a_4792_);
return v_res_4796_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(lean_object* v_next_4797_, lean_object* v_a_4798_){
_start:
{
lean_object* v___f_4800_; lean_object* v___x_4801_; uint8_t v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; 
lean_inc(v_a_4798_);
v___f_4800_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___lam__6___boxed), 4, 2);
lean_closure_set(v___f_4800_, 0, v_a_4798_);
lean_closure_set(v___f_4800_, 1, v_next_4797_);
v___x_4801_ = lean_unsigned_to_nat(0u);
v___x_4802_ = 0;
v___x_4803_ = lean_st_ref_get(v_a_4798_);
v___x_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4803_);
v___x_4805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4804_);
v___x_4806_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4801_, v___x_4802_, v___x_4805_, v___f_4800_);
return v___x_4806_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_next_4797_ = stack[0].m_obj;
lean_object* v_a_4798_ = stack[1].m_obj;
lean_object* v_res_4807_;
v_res_4807_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4797_, v_a_4798_);
stack->m_obj
 = v_res_4807_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg___boxed(lean_object* v_next_4808_, lean_object* v_a_4809_, lean_object* v___y_4810_){
_start:
{
lean_object* v_res_4811_; 
v_res_4811_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_4808_, v_a_4809_);
lean_dec(v_a_4809_);
return v_res_4811_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(lean_object* v_receiverId_4812_, lean_object* v_a_4813_, lean_object* v_x_4814_){
_start:
{
if (lean_obj_tag(v_x_4814_) == 0)
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4824_; 
lean_dec(v_receiverId_4812_);
v_a_4816_ = lean_ctor_get(v_x_4814_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v_x_4814_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4818_ = v_x_4814_;
v_isShared_4819_ = v_isSharedCheck_4824_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v_x_4814_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4824_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
lean_object* v___x_4822_; 
v___x_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4821_);
return v___x_4822_;
}
}
}
else
{
lean_object* v_a_4825_; lean_object* v_receivers_4826_; lean_object* v___x_4827_; 
v_a_4825_ = lean_ctor_get(v_x_4814_, 0);
lean_inc(v_a_4825_);
lean_dec_ref_known(v_x_4814_, 1);
v_receivers_4826_ = lean_ctor_get(v_a_4825_, 7);
lean_inc(v_receivers_4826_);
lean_dec(v_a_4825_);
v___x_4827_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4826_, v_receiverId_4812_);
if (lean_obj_tag(v___x_4827_) == 1)
{
lean_object* v_val_4828_; lean_object* v___f_4829_; lean_object* v___x_4830_; uint8_t v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v_val_4828_ = lean_ctor_get(v___x_4827_, 0);
lean_inc(v_val_4828_);
lean_dec_ref_known(v___x_4827_, 1);
lean_inc(v_a_4813_);
v___f_4829_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_4829_, 0, v_a_4813_);
lean_closure_set(v___f_4829_, 1, v_receiverId_4812_);
lean_closure_set(v___f_4829_, 2, v_receivers_4826_);
v___x_4830_ = lean_unsigned_to_nat(0u);
v___x_4831_ = 0;
v___x_4832_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_val_4828_, v_a_4813_);
v___x_4833_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4830_, v___x_4831_, v___x_4832_, v___f_4829_);
return v___x_4833_;
}
else
{
lean_object* v___x_4834_; 
lean_dec(v___x_4827_);
lean_dec(v_receivers_4826_);
lean_dec(v_receiverId_4812_);
v___x_4834_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__1___closed__0));
return v___x_4834_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_receiverId_4812_ = stack[0].m_obj;
lean_object* v_a_4813_ = stack[1].m_obj;
lean_object* v_x_4814_ = stack[2].m_obj;
lean_object* v_res_4835_;
v_res_4835_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4812_, v_a_4813_, v_x_4814_);
stack->m_obj
 = v_res_4835_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed(lean_object* v_receiverId_4836_, lean_object* v_a_4837_, lean_object* v_x_4838_, lean_object* v___y_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2(v_receiverId_4836_, v_a_4837_, v_x_4838_);
lean_dec(v_a_4837_);
return v_res_4840_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(lean_object* v_receiverId_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v___f_4844_; lean_object* v___x_4845_; uint8_t v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
lean_inc(v_a_4842_);
v___f_4844_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4844_, 0, v_receiverId_4841_);
lean_closure_set(v___f_4844_, 1, v_a_4842_);
v___x_4845_ = lean_unsigned_to_nat(0u);
v___x_4846_ = 0;
v___x_4847_ = lean_st_ref_get(v_a_4842_);
v___x_4848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
v___x_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
v___x_4850_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4845_, v___x_4846_, v___x_4849_, v___f_4844_);
return v___x_4850_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_receiverId_4841_ = stack[0].m_obj;
lean_object* v_a_4842_ = stack[1].m_obj;
lean_object* v_res_4851_;
v_res_4851_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4841_, v_a_4842_);
stack->m_obj
 = v_res_4851_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg___boxed(lean_object* v_receiverId_4852_, lean_object* v_a_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v_res_4855_; 
v_res_4855_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_4852_, v_a_4853_);
lean_dec(v_a_4853_);
return v_res_4855_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(lean_object* v_id_4860_, lean_object* v___y_4861_, lean_object* v___f_4862_, lean_object* v_x_4863_){
_start:
{
if (lean_obj_tag(v_x_4863_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4873_; 
lean_dec_ref(v___f_4862_);
lean_dec(v_id_4860_);
v_a_4865_ = lean_ctor_get(v_x_4863_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v_x_4863_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4867_ = v_x_4863_;
v_isShared_4868_ = v_isSharedCheck_4873_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v_x_4863_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4873_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4870_; 
if (v_isShared_4868_ == 0)
{
v___x_4870_ = v___x_4867_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4865_);
v___x_4870_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
lean_object* v___x_4871_; 
v___x_4871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4870_);
return v___x_4871_;
}
}
}
else
{
lean_object* v_a_4874_; uint8_t v___x_4875_; 
v_a_4874_ = lean_ctor_get(v_x_4863_, 0);
lean_inc(v_a_4874_);
lean_dec_ref_known(v_x_4863_, 1);
v___x_4875_ = lean_unbox(v_a_4874_);
lean_dec(v_a_4874_);
if (v___x_4875_ == 0)
{
lean_object* v___x_4876_; 
lean_dec_ref(v___f_4862_);
lean_dec(v_id_4860_);
v___x_4876_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___closed__1));
return v___x_4876_;
}
else
{
lean_object* v___x_4877_; uint8_t v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v___x_4877_ = lean_unsigned_to_nat(0u);
v___x_4878_ = 0;
v___x_4879_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_id_4860_, v___y_4861_);
v___x_4880_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4877_, v___x_4878_, v___x_4879_, v___f_4862_);
return v___x_4880_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_4860_ = stack[0].m_obj;
lean_object* v___y_4861_ = stack[1].m_obj;
lean_object* v___f_4862_ = stack[2].m_obj;
lean_object* v_x_4863_ = stack[3].m_obj;
lean_object* v_res_4881_;
v_res_4881_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(v_id_4860_, v___y_4861_, v___f_4862_, v_x_4863_);
stack->m_obj
 = v_res_4881_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed(lean_object* v_id_4882_, lean_object* v___y_4883_, lean_object* v___f_4884_, lean_object* v_x_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5(v_id_4882_, v___y_4883_, v___f_4884_, v_x_4885_);
lean_dec(v___y_4883_);
return v_res_4887_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(lean_object* v_val_4888_, lean_object* v_x_4889_){
_start:
{
if (lean_obj_tag(v_x_4889_) == 0)
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4899_; 
v_a_4891_ = lean_ctor_get(v_x_4889_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v_x_4889_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4893_ = v_x_4889_;
v_isShared_4894_ = v_isSharedCheck_4899_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v_x_4889_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4899_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
lean_object* v___x_4897_; 
v___x_4897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4896_);
return v___x_4897_;
}
}
}
else
{
lean_object* v_a_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4911_; 
v_a_4900_ = lean_ctor_get(v_x_4889_, 0);
v_isSharedCheck_4911_ = !lean_is_exclusive(v_x_4889_);
if (v_isSharedCheck_4911_ == 0)
{
v___x_4902_ = v_x_4889_;
v_isShared_4903_ = v_isSharedCheck_4911_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_a_4900_);
lean_dec(v_x_4889_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4911_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v_pos_4904_; uint8_t v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4908_; 
v_pos_4904_ = lean_ctor_get(v_a_4900_, 1);
lean_inc(v_pos_4904_);
lean_dec(v_a_4900_);
v___x_4905_ = lean_nat_dec_eq(v_pos_4904_, v_val_4888_);
lean_dec(v_pos_4904_);
v___x_4906_ = lean_box(v___x_4905_);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 0, v___x_4906_);
v___x_4908_ = v___x_4902_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4906_);
v___x_4908_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
lean_object* v___x_4909_; 
v___x_4909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4909_, 0, v___x_4908_);
return v___x_4909_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_4888_ = stack[0].m_obj;
lean_object* v_x_4889_ = stack[1].m_obj;
lean_object* v_res_4912_;
v_res_4912_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(v_val_4888_, v_x_4889_);
stack->m_obj
 = v_res_4912_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed(lean_object* v_val_4913_, lean_object* v_x_4914_, lean_object* v___y_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6(v_val_4913_, v_x_4914_);
lean_dec(v_val_4913_);
return v_res_4916_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(lean_object* v___x_4917_, uint8_t v_closed_4918_, lean_object* v___f_4919_, lean_object* v_x_4920_){
_start:
{
if (lean_obj_tag(v_x_4920_) == 0)
{
lean_object* v_a_4922_; lean_object* v___x_4924_; uint8_t v_isShared_4925_; uint8_t v_isSharedCheck_4930_; 
lean_dec_ref(v___f_4919_);
lean_dec(v___x_4917_);
v_a_4922_ = lean_ctor_get(v_x_4920_, 0);
v_isSharedCheck_4930_ = !lean_is_exclusive(v_x_4920_);
if (v_isSharedCheck_4930_ == 0)
{
v___x_4924_ = v_x_4920_;
v_isShared_4925_ = v_isSharedCheck_4930_;
goto v_resetjp_4923_;
}
else
{
lean_inc(v_a_4922_);
lean_dec(v_x_4920_);
v___x_4924_ = lean_box(0);
v_isShared_4925_ = v_isSharedCheck_4930_;
goto v_resetjp_4923_;
}
v_resetjp_4923_:
{
lean_object* v___x_4927_; 
if (v_isShared_4925_ == 0)
{
v___x_4927_ = v___x_4924_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4922_);
v___x_4927_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
lean_object* v___x_4928_; 
v___x_4928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4928_, 0, v___x_4927_);
return v___x_4928_;
}
}
}
else
{
lean_object* v_a_4931_; lean_object* v___x_4933_; uint8_t v_isShared_4934_; uint8_t v_isSharedCheck_4941_; 
v_a_4931_ = lean_ctor_get(v_x_4920_, 0);
v_isSharedCheck_4941_ = !lean_is_exclusive(v_x_4920_);
if (v_isSharedCheck_4941_ == 0)
{
v___x_4933_ = v_x_4920_;
v_isShared_4934_ = v_isSharedCheck_4941_;
goto v_resetjp_4932_;
}
else
{
lean_inc(v_a_4931_);
lean_dec(v_x_4920_);
v___x_4933_ = lean_box(0);
v_isShared_4934_ = v_isSharedCheck_4941_;
goto v_resetjp_4932_;
}
v_resetjp_4932_:
{
lean_object* v___x_4935_; lean_object* v___x_4937_; 
v___x_4935_ = lean_st_ref_get(v_a_4931_);
lean_dec(v_a_4931_);
if (v_isShared_4934_ == 0)
{
lean_ctor_set(v___x_4933_, 0, v___x_4935_);
v___x_4937_ = v___x_4933_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4935_);
v___x_4937_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
lean_object* v___x_4938_; lean_object* v___x_4939_; 
v___x_4938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
v___x_4939_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4917_, v_closed_4918_, v___x_4938_, v___f_4919_);
return v___x_4939_;
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4917_ = stack[0].m_obj;
uint8_t v_closed_4918_ = stack[1].m_num;
lean_object* v___f_4919_ = stack[2].m_obj;
lean_object* v_x_4920_ = stack[3].m_obj;
lean_object* v_res_4942_;
v_res_4942_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(v___x_4917_, v_closed_4918_, v___f_4919_, v_x_4920_);
stack->m_obj
 = v_res_4942_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed(lean_object* v___x_4943_, lean_object* v_closed_4944_, lean_object* v___f_4945_, lean_object* v_x_4946_, lean_object* v___y_4947_){
_start:
{
uint8_t v_closed_boxed_4948_; lean_object* v_res_4949_; 
v_closed_boxed_4948_ = lean_unbox(v_closed_4944_);
v_res_4949_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7(v___x_4943_, v_closed_boxed_4948_, v___f_4945_, v_x_4946_);
return v_res_4949_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(lean_object* v_id_4950_, lean_object* v___x_4951_, lean_object* v___y_4952_, lean_object* v_x_4953_){
_start:
{
if (lean_obj_tag(v_x_4953_) == 0)
{
lean_object* v_a_4955_; lean_object* v___x_4957_; uint8_t v_isShared_4958_; uint8_t v_isSharedCheck_4963_; 
lean_dec(v___x_4951_);
v_a_4955_ = lean_ctor_get(v_x_4953_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v_x_4953_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4957_ = v_x_4953_;
v_isShared_4958_ = v_isSharedCheck_4963_;
goto v_resetjp_4956_;
}
else
{
lean_inc(v_a_4955_);
lean_dec(v_x_4953_);
v___x_4957_ = lean_box(0);
v_isShared_4958_ = v_isSharedCheck_4963_;
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
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4955_);
v___x_4960_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4959_;
}
v_reusejp_4959_:
{
lean_object* v___x_4961_; 
v___x_4961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4961_, 0, v___x_4960_);
return v___x_4961_;
}
}
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_5002_; 
v_a_4964_ = lean_ctor_get(v_x_4953_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v_x_4953_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4966_ = v_x_4953_;
v_isShared_4967_ = v_isSharedCheck_5002_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v_x_4953_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_5002_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
uint8_t v_closed_4968_; 
v_closed_4968_ = lean_ctor_get_uint8(v_a_4964_, sizeof(void*)*10);
if (v_closed_4968_ == 0)
{
lean_object* v_capacity_4969_; lean_object* v_size_4970_; lean_object* v_receivers_4971_; lean_object* v___x_4972_; 
v_capacity_4969_ = lean_ctor_get(v_a_4964_, 2);
lean_inc(v_capacity_4969_);
v_size_4970_ = lean_ctor_get(v_a_4964_, 3);
lean_inc(v_size_4970_);
v_receivers_4971_ = lean_ctor_get(v_a_4964_, 7);
lean_inc(v_receivers_4971_);
lean_dec(v_a_4964_);
v___x_4972_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe_spec__1___redArg(v_receivers_4971_, v_id_4950_);
lean_dec(v_receivers_4971_);
if (lean_obj_tag(v___x_4972_) == 1)
{
lean_object* v_val_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4991_; 
v_val_4973_ = lean_ctor_get(v___x_4972_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4975_ = v___x_4972_;
v_isShared_4976_ = v_isSharedCheck_4991_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_val_4973_);
lean_dec(v___x_4972_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4991_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
uint8_t v___x_4977_; 
v___x_4977_ = lean_nat_dec_eq(v_size_4970_, v___x_4951_);
lean_dec(v_size_4970_);
if (v___x_4977_ == 0)
{
lean_object* v___f_4978_; lean_object* v___x_4979_; lean_object* v___f_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
lean_del_object(v___x_4975_);
lean_del_object(v___x_4966_);
lean_inc(v_val_4973_);
v___f_4978_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__6___boxed), 3, 1);
lean_closure_set(v___f_4978_, 0, v_val_4973_);
v___x_4979_ = lean_box(v_closed_4968_);
lean_inc(v___x_4951_);
v___f_4980_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__7___boxed), 5, 3);
lean_closure_set(v___f_4980_, 0, v___x_4951_);
lean_closure_set(v___f_4980_, 1, v___x_4979_);
lean_closure_set(v___f_4980_, 2, v___f_4978_);
v___x_4981_ = lean_nat_mod(v_val_4973_, v_capacity_4969_);
lean_dec(v_capacity_4969_);
lean_dec(v_val_4973_);
v___x_4982_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_getSlot___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__1___redArg(v___x_4981_, v___y_4952_);
v___x_4983_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_4951_, v___x_4977_, v___x_4982_, v___f_4980_);
return v___x_4983_;
}
else
{
lean_object* v___x_4984_; lean_object* v___x_4986_; 
lean_dec(v_val_4973_);
lean_dec(v_capacity_4969_);
lean_dec(v___x_4951_);
v___x_4984_ = lean_box(v_closed_4968_);
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 0, v___x_4984_);
v___x_4986_ = v___x_4966_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4984_);
v___x_4986_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
lean_object* v___x_4988_; 
if (v_isShared_4976_ == 0)
{
lean_ctor_set_tag(v___x_4975_, 0);
lean_ctor_set(v___x_4975_, 0, v___x_4986_);
v___x_4988_ = v___x_4975_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v___x_4986_);
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
else
{
lean_object* v___x_4992_; lean_object* v___x_4994_; 
lean_dec(v___x_4972_);
lean_dec(v_size_4970_);
lean_dec(v_capacity_4969_);
lean_dec(v___x_4951_);
v___x_4992_ = lean_box(v_closed_4968_);
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 0, v___x_4992_);
v___x_4994_ = v___x_4966_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4996_; 
v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4992_);
v___x_4994_ = v_reuseFailAlloc_4996_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
lean_object* v___x_4995_; 
v___x_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4994_);
return v___x_4995_;
}
}
}
else
{
lean_object* v___x_4997_; lean_object* v___x_4999_; 
lean_dec(v_a_4964_);
lean_dec(v___x_4951_);
v___x_4997_ = lean_box(v_closed_4968_);
if (v_isShared_4967_ == 0)
{
lean_ctor_set(v___x_4966_, 0, v___x_4997_);
v___x_4999_ = v___x_4966_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v___x_4997_);
v___x_4999_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
lean_object* v___x_5000_; 
v___x_5000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5000_, 0, v___x_4999_);
return v___x_5000_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_4950_ = stack[0].m_obj;
lean_object* v___x_4951_ = stack[1].m_obj;
lean_object* v___y_4952_ = stack[2].m_obj;
lean_object* v_x_4953_ = stack[3].m_obj;
lean_object* v_res_5003_;
v_res_5003_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_4950_, v___x_4951_, v___y_4952_, v_x_4953_);
stack->m_obj
 = v_res_5003_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed(lean_object* v_id_5004_, lean_object* v___x_5005_, lean_object* v___y_5006_, lean_object* v_x_5007_, lean_object* v___y_5008_){
_start:
{
lean_object* v_res_5009_; 
v_res_5009_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8(v_id_5004_, v___x_5005_, v___y_5006_, v_x_5007_);
lean_dec(v___y_5006_);
lean_dec(v_id_5004_);
return v_res_5009_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(lean_object* v_id_5010_, lean_object* v___f_5011_, lean_object* v___y_5012_){
_start:
{
lean_object* v___f_5014_; lean_object* v___x_5015_; lean_object* v___f_5016_; uint8_t v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; 
lean_inc_n(v___y_5012_, 2);
lean_inc(v_id_5010_);
v___f_5014_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__5___boxed), 5, 3);
lean_closure_set(v___f_5014_, 0, v_id_5010_);
lean_closure_set(v___f_5014_, 1, v___y_5012_);
lean_closure_set(v___f_5014_, 2, v___f_5011_);
v___x_5015_ = lean_unsigned_to_nat(0u);
v___f_5016_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__8___boxed), 5, 3);
lean_closure_set(v___f_5016_, 0, v_id_5010_);
lean_closure_set(v___f_5016_, 1, v___x_5015_);
lean_closure_set(v___f_5016_, 2, v___y_5012_);
v___x_5017_ = 0;
v___x_5018_ = lean_st_ref_get(v___y_5012_);
v___x_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
v___x_5020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5019_);
v___x_5021_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5015_, v___x_5017_, v___x_5020_, v___f_5016_);
v___x_5022_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5015_, v___x_5017_, v___x_5021_, v___f_5014_);
return v___x_5022_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_id_5010_ = stack[0].m_obj;
lean_object* v___f_5011_ = stack[1].m_obj;
lean_object* v___y_5012_ = stack[2].m_obj;
lean_object* v_res_5023_;
v_res_5023_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_5010_, v___f_5011_, v___y_5012_);
stack->m_obj
 = v_res_5023_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed(lean_object* v_id_5024_, lean_object* v___f_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9(v_id_5024_, v___f_5025_, v___y_5026_);
lean_dec(v___y_5026_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(lean_object* v_ch_5031_){
_start:
{
lean_object* v_state_5032_; lean_object* v_id_5033_; lean_object* v___f_5034_; lean_object* v___f_5035_; lean_object* v___f_5036_; lean_object* v___f_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v_state_5032_ = lean_ctor_get(v_ch_5031_, 0);
lean_inc_ref_n(v_state_5032_, 2);
v_id_5033_ = lean_ctor_get(v_ch_5031_, 1);
lean_inc(v_id_5033_);
v___f_5034_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__0));
v___f_5035_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_5035_, 0, v_ch_5031_);
v___f_5036_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___closed__1));
v___f_5037_ = lean_alloc_closure((void*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__9___boxed), 4, 2);
lean_closure_set(v___f_5037_, 0, v_id_5033_);
lean_closure_set(v___f_5037_, 1, v___f_5036_);
v___x_5038_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_5038_, 0, lean_box(0));
lean_closure_set(v___x_5038_, 1, lean_box(0));
lean_closure_set(v___x_5038_, 2, v_state_5032_);
lean_closure_set(v___x_5038_, 3, v___f_5037_);
v___x_5039_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__2___boxed), 5, 4);
lean_closure_set(v___x_5039_, 0, lean_box(0));
lean_closure_set(v___x_5039_, 1, lean_box(0));
lean_closure_set(v___x_5039_, 2, v_state_5032_);
lean_closure_set(v___x_5039_, 3, v___f_5034_);
v___x_5040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5040_, 0, v___x_5038_);
lean_ctor_set(v___x_5040_, 1, v___f_5035_);
lean_ctor_set(v___x_5040_, 2, v___x_5039_);
return v___x_5040_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector(lean_object* v_00_u03b1_5041_, lean_object* v_ch_5042_){
_start:
{
lean_object* v___x_5043_; 
v___x_5043_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5042_);
return v___x_5043_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_object* v_00_u03b1_5044_, lean_object* v_receiverId_5045_, lean_object* v_a_5046_){
_start:
{
lean_object* v___x_5048_; 
v___x_5048_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___redArg(v_receiverId_5045_, v_a_5046_);
return v___x_5048_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_receiverId_5045_ = stack[1].m_obj;
lean_object* v_a_5046_ = stack[2].m_obj;
lean_object* v_res_5049_;
v_res_5049_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(lean_box(0), v_receiverId_5045_, v_a_5046_);
stack->m_obj
 = v_res_5049_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0___boxed(lean_object* v_00_u03b1_5050_, lean_object* v_receiverId_5051_, lean_object* v_a_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0(v_00_u03b1_5050_, v_receiverId_5051_, v_a_5052_);
lean_dec(v_a_5052_);
return v_res_5054_;
}
}
lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_object* v_00_u03b1_5055_, lean_object* v_q_5056_, lean_object* v___y_5057_){
_start:
{
lean_object* v___x_5059_; 
v___x_5059_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___redArg(v_q_5056_, v___y_5057_);
return v___x_5059_;
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_5056_ = stack[1].m_obj;
lean_object* v___y_5057_ = stack[2].m_obj;
lean_object* v_res_5060_;
v_res_5060_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(lean_box(0), v_q_5056_, v___y_5057_);
stack->m_obj
 = v_res_5060_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3___boxed(lean_object* v_00_u03b1_5061_, lean_object* v_q_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_){
_start:
{
lean_object* v_res_5065_; 
v_res_5065_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3(v_00_u03b1_5061_, v_q_5062_, v___y_5063_);
lean_dec(v___y_5063_);
return v_res_5065_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_5066_, lean_object* v_slot_5067_, lean_object* v_next_5068_, lean_object* v_a_5069_){
_start:
{
lean_object* v___x_5071_; 
v___x_5071_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___redArg(v_slot_5067_, v_next_5068_);
return v___x_5071_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_slot_5067_ = stack[1].m_obj;
lean_object* v_next_5068_ = stack[2].m_obj;
lean_object* v_a_5069_ = stack[3].m_obj;
lean_object* v_res_5072_;
v_res_5072_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(lean_box(0), v_slot_5067_, v_next_5068_, v_a_5069_);
stack->m_obj
 = v_res_5072_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_5073_, lean_object* v_slot_5074_, lean_object* v_next_5075_, lean_object* v_a_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getSlotValue___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__3(v_00_u03b1_5073_, v_slot_5074_, v_next_5075_, v_a_5076_);
lean_dec(v_a_5076_);
lean_dec(v_next_5075_);
lean_dec(v_slot_5074_);
return v_res_5078_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_5079_, lean_object* v_a_5080_){
_start:
{
lean_object* v___x_5082_; 
v___x_5082_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___redArg(v_a_5080_);
return v___x_5082_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_5080_ = stack[1].m_obj;
lean_object* v_res_5083_;
v_res_5083_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(lean_box(0), v_a_5080_);
stack->m_obj
 = v_res_5083_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_5084_, lean_object* v_a_5085_, lean_object* v___y_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_isEmpty___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_spec__4(v_00_u03b1_5084_, v_a_5085_);
lean_dec(v_a_5085_);
return v_res_5087_;
}
}
lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_object* v_00_u03b1_5088_, lean_object* v_next_5089_, lean_object* v_a_5090_){
_start:
{
lean_object* v___x_5092_; 
v___x_5092_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___redArg(v_next_5089_, v_a_5090_);
return v___x_5092_;
}
}
LEAN_EXPORT void l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_next_5089_ = stack[1].m_obj;
lean_object* v_a_5090_ = stack[2].m_obj;
lean_object* v_res_5093_;
v_res_5093_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(lean_box(0), v_next_5089_, v_a_5090_);
stack->m_obj
 = v_res_5093_;
}
LEAN_EXPORT lean_object* l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5094_, lean_object* v_next_5095_, lean_object* v_a_5096_, lean_object* v___y_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_getValueByPosition___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv_x27___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__0_spec__0(v_00_u03b1_5094_, v_next_5095_, v_a_5096_);
lean_dec(v_a_5096_);
return v_res_5098_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_object* v_00_u03b1_5099_, lean_object* v_x_5100_, lean_object* v_x_5101_, lean_object* v___y_5102_){
_start:
{
lean_object* v___x_5104_; 
v___x_5104_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___redArg(v_x_5100_, v_x_5101_);
return v___x_5104_;
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5100_ = stack[1].m_obj;
lean_object* v_x_5101_ = stack[2].m_obj;
lean_object* v___y_5102_ = stack[3].m_obj;
lean_object* v_res_5105_;
v_res_5105_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(lean_box(0), v_x_5100_, v_x_5101_, v___y_5102_);
stack->m_obj
 = v_res_5105_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4___boxed(lean_object* v_00_u03b1_5106_, lean_object* v_x_5107_, lean_object* v_x_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector_spec__3_spec__4(v_00_u03b1_5106_, v_x_5107_, v_x_5108_, v___y_5109_);
lean_dec(v___y_5109_);
return v_res_5111_;
}
}
static lean_object* _init_l_Std_Broadcast_new___auto__1(void){
_start:
{
lean_object* v___x_5112_; 
v___x_5112_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5112_;
}
}
lean_object* l_Std_Broadcast_new___redArg(lean_object* v_capacity_5113_){
_start:
{
lean_object* v___x_5115_; 
v___x_5115_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5113_);
return v___x_5115_;
}
}
LEAN_EXPORT void l_Std_Broadcast_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_5113_ = stack[0].m_obj;
lean_object* v_res_5116_;
v_res_5116_ = l_Std_Broadcast_new___redArg(v_capacity_5113_);
stack->m_obj
 = v_res_5116_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___redArg___boxed(lean_object* v_capacity_5117_, lean_object* v_a_5118_){
_start:
{
lean_object* v_res_5119_; 
v_res_5119_ = l_Std_Broadcast_new___redArg(v_capacity_5117_);
return v_res_5119_;
}
}
lean_object* l_Std_Broadcast_new(lean_object* v_00_u03b1_5120_, lean_object* v_capacity_5121_, lean_object* v_h_5122_){
_start:
{
lean_object* v___x_5124_; 
v___x_5124_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5121_);
return v___x_5124_;
}
}
LEAN_EXPORT void l_Std_Broadcast_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_5121_ = stack[1].m_obj;
lean_object* v_res_5125_;
v_res_5125_ = l_Std_Broadcast_new(lean_box(0), v_capacity_5121_, lean_box(0));
stack->m_obj
 = v_res_5125_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_new___boxed(lean_object* v_00_u03b1_5126_, lean_object* v_capacity_5127_, lean_object* v_h_5128_, lean_object* v_a_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l_Std_Broadcast_new(v_00_u03b1_5126_, v_capacity_5127_, v_h_5128_);
return v_res_5130_;
}
}
lean_object* l_Std_Broadcast_trySend___redArg(lean_object* v_ch_5131_, lean_object* v_v_5132_){
_start:
{
lean_object* v___x_5134_; 
v___x_5134_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5131_, v_v_5132_);
return v___x_5134_;
}
}
LEAN_EXPORT void l_Std_Broadcast_trySend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5131_ = stack[0].m_obj;
lean_object* v_v_5132_ = stack[1].m_obj;
lean_object* v_res_5135_;
v_res_5135_ = l_Std_Broadcast_trySend___redArg(v_ch_5131_, v_v_5132_);
stack->m_obj
 = v_res_5135_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___redArg___boxed(lean_object* v_ch_5136_, lean_object* v_v_5137_, lean_object* v_a_5138_){
_start:
{
lean_object* v_res_5139_; 
v_res_5139_ = l_Std_Broadcast_trySend___redArg(v_ch_5136_, v_v_5137_);
return v_res_5139_;
}
}
lean_object* l_Std_Broadcast_trySend(lean_object* v_00_u03b1_5140_, lean_object* v_ch_5141_, lean_object* v_v_5142_){
_start:
{
lean_object* v___x_5144_; 
v___x_5144_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5141_, v_v_5142_);
return v___x_5144_;
}
}
LEAN_EXPORT void l_Std_Broadcast_trySend_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5141_ = stack[1].m_obj;
lean_object* v_v_5142_ = stack[2].m_obj;
lean_object* v_res_5145_;
v_res_5145_ = l_Std_Broadcast_trySend(lean_box(0), v_ch_5141_, v_v_5142_);
stack->m_obj
 = v_res_5145_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_trySend___boxed(lean_object* v_00_u03b1_5146_, lean_object* v_ch_5147_, lean_object* v_v_5148_, lean_object* v_a_5149_){
_start:
{
lean_object* v_res_5150_; 
v_res_5150_ = l_Std_Broadcast_trySend(v_00_u03b1_5146_, v_ch_5147_, v_v_5148_);
return v_res_5150_;
}
}
lean_object* l_Std_Broadcast_subscribe___redArg(lean_object* v_ch_5151_){
_start:
{
lean_object* v___x_5153_; 
v___x_5153_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_5151_);
if (lean_obj_tag(v___x_5153_) == 0)
{
lean_object* v_a_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5161_; 
v_a_5154_ = lean_ctor_get(v___x_5153_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5153_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5156_ = v___x_5153_;
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_a_5154_);
lean_dec(v___x_5153_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v___x_5159_; 
if (v_isShared_5157_ == 0)
{
v___x_5159_ = v___x_5156_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_a_5154_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
}
else
{
lean_object* v_a_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5169_; 
v_a_5162_ = lean_ctor_get(v___x_5153_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5153_);
if (v_isSharedCheck_5169_ == 0)
{
v___x_5164_ = v___x_5153_;
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_a_5162_);
lean_dec(v___x_5153_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5169_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5167_; 
if (v_isShared_5165_ == 0)
{
v___x_5167_ = v___x_5164_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5162_);
v___x_5167_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
return v___x_5167_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Broadcast_subscribe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5151_ = stack[0].m_obj;
lean_object* v_res_5170_;
v_res_5170_ = l_Std_Broadcast_subscribe___redArg(v_ch_5151_);
stack->m_obj
 = v_res_5170_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___redArg___boxed(lean_object* v_ch_5171_, lean_object* v_a_5172_){
_start:
{
lean_object* v_res_5173_; 
v_res_5173_ = l_Std_Broadcast_subscribe___redArg(v_ch_5171_);
return v_res_5173_;
}
}
lean_object* l_Std_Broadcast_subscribe(lean_object* v_00_u03b1_5174_, lean_object* v_ch_5175_){
_start:
{
lean_object* v___x_5177_; 
v___x_5177_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_subscribe___redArg(v_ch_5175_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
v_a_5178_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5180_ = v___x_5177_;
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_5177_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5183_; 
if (v_isShared_5181_ == 0)
{
v___x_5183_ = v___x_5180_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
return v___x_5183_;
}
}
}
else
{
lean_object* v_a_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5193_; 
v_a_5186_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5188_ = v___x_5177_;
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_a_5186_);
lean_dec(v___x_5177_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
return v___x_5191_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Broadcast_subscribe_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5175_ = stack[1].m_obj;
lean_object* v_res_5194_;
v_res_5194_ = l_Std_Broadcast_subscribe(lean_box(0), v_ch_5175_);
stack->m_obj
 = v_res_5194_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_subscribe___boxed(lean_object* v_00_u03b1_5195_, lean_object* v_ch_5196_, lean_object* v_a_5197_){
_start:
{
lean_object* v_res_5198_; 
v_res_5198_ = l_Std_Broadcast_subscribe(v_00_u03b1_5195_, v_ch_5196_);
return v_res_5198_;
}
}
lean_object* l_Std_Broadcast_close___redArg(lean_object* v_ch_5199_){
_start:
{
lean_object* v___x_5201_; 
v___x_5201_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5199_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5209_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5204_ = v___x_5201_;
v_isShared_5205_ = v_isSharedCheck_5209_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_a_5202_);
lean_dec(v___x_5201_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5209_;
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
lean_object* v_reuseFailAlloc_5208_; 
v_reuseFailAlloc_5208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
v___x_5207_ = v_reuseFailAlloc_5208_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
return v___x_5207_;
}
}
}
else
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5227_; 
v_a_5210_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5212_ = v___x_5201_;
v_isShared_5213_ = v_isSharedCheck_5227_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5201_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5227_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
uint8_t v___x_5214_; 
v___x_5214_ = lean_unbox(v_a_5210_);
lean_dec(v_a_5210_);
switch(v___x_5214_)
{
case 0:
{
lean_object* v___x_5215_; lean_object* v___x_5217_; 
v___x_5215_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 0, v___x_5215_);
v___x_5217_ = v___x_5212_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v___x_5215_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
case 1:
{
lean_object* v___x_5219_; lean_object* v___x_5221_; 
v___x_5219_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 0, v___x_5219_);
v___x_5221_ = v___x_5212_;
goto v_reusejp_5220_;
}
else
{
lean_object* v_reuseFailAlloc_5222_; 
v_reuseFailAlloc_5222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5222_, 0, v___x_5219_);
v___x_5221_ = v_reuseFailAlloc_5222_;
goto v_reusejp_5220_;
}
v_reusejp_5220_:
{
return v___x_5221_;
}
}
default: 
{
lean_object* v___x_5223_; lean_object* v___x_5225_; 
v___x_5223_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5213_ == 0)
{
lean_ctor_set(v___x_5212_, 0, v___x_5223_);
v___x_5225_ = v___x_5212_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5223_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Broadcast_close___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5199_ = stack[0].m_obj;
lean_object* v_res_5228_;
v_res_5228_ = l_Std_Broadcast_close___redArg(v_ch_5199_);
stack->m_obj
 = v_res_5228_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___redArg___boxed(lean_object* v_ch_5229_, lean_object* v_a_5230_){
_start:
{
lean_object* v_res_5231_; 
v_res_5231_ = l_Std_Broadcast_close___redArg(v_ch_5229_);
return v_res_5231_;
}
}
lean_object* l_Std_Broadcast_close(lean_object* v_00_u03b1_5232_, lean_object* v_ch_5233_){
_start:
{
lean_object* v___x_5235_; 
v___x_5235_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_close___redArg(v_ch_5233_);
if (lean_obj_tag(v___x_5235_) == 0)
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
v_a_5236_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___x_5235_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___x_5235_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
else
{
lean_object* v_a_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5261_; 
v_a_5244_ = lean_ctor_get(v___x_5235_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5246_ = v___x_5235_;
v_isShared_5247_ = v_isSharedCheck_5261_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_a_5244_);
lean_dec(v___x_5235_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5261_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
uint8_t v___x_5248_; 
v___x_5248_ = lean_unbox(v_a_5244_);
lean_dec(v_a_5244_);
switch(v___x_5248_)
{
case 0:
{
lean_object* v___x_5249_; lean_object* v___x_5251_; 
v___x_5249_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__0));
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 0, v___x_5249_);
v___x_5251_ = v___x_5246_;
goto v_reusejp_5250_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
v___x_5251_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5250_;
}
v_reusejp_5250_:
{
return v___x_5251_;
}
}
case 1:
{
lean_object* v___x_5253_; lean_object* v___x_5255_; 
v___x_5253_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__1));
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 0, v___x_5253_);
v___x_5255_ = v___x_5246_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5256_; 
v_reuseFailAlloc_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5256_, 0, v___x_5253_);
v___x_5255_ = v_reuseFailAlloc_5256_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
return v___x_5255_;
}
}
default: 
{
lean_object* v___x_5257_; lean_object* v___x_5259_; 
v___x_5257_ = ((lean_object*)(l_Std_instMonadLiftBroadcastIO___lam__0___closed__2));
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 0, v___x_5257_);
v___x_5259_ = v___x_5246_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5257_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Broadcast_close_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5233_ = stack[1].m_obj;
lean_object* v_res_5262_;
v_res_5262_ = l_Std_Broadcast_close(lean_box(0), v_ch_5233_);
stack->m_obj
 = v_res_5262_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_close___boxed(lean_object* v_00_u03b1_5263_, lean_object* v_ch_5264_, lean_object* v_a_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l_Std_Broadcast_close(v_00_u03b1_5263_, v_ch_5264_);
return v_res_5266_;
}
}
lean_object* l_Std_Broadcast_send___redArg___lam__0(lean_object* v_x_5267_){
_start:
{
lean_object* v___y_5270_; 
if (lean_obj_tag(v_x_5267_) == 0)
{
lean_object* v_a_5274_; uint8_t v___x_5275_; 
v_a_5274_ = lean_ctor_get(v_x_5267_, 0);
lean_inc(v_a_5274_);
lean_dec_ref_known(v_x_5267_, 1);
v___x_5275_ = lean_unbox(v_a_5274_);
lean_dec(v_a_5274_);
switch(v___x_5275_)
{
case 0:
{
lean_object* v___x_5276_; 
v___x_5276_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__0));
v___y_5270_ = v___x_5276_;
goto v___jp_5269_;
}
case 1:
{
lean_object* v___x_5277_; 
v___x_5277_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__1));
v___y_5270_ = v___x_5277_;
goto v___jp_5269_;
}
default: 
{
lean_object* v___x_5278_; 
v___x_5278_ = ((lean_object*)(l_Std_instToStringBroadcastError___lam__0___closed__2));
v___y_5270_ = v___x_5278_;
goto v___jp_5269_;
}
}
}
else
{
lean_object* v_a_5279_; lean_object* v___x_5281_; uint8_t v_isShared_5282_; uint8_t v_isSharedCheck_5287_; 
v_a_5279_ = lean_ctor_get(v_x_5267_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v_x_5267_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5281_ = v_x_5267_;
v_isShared_5282_ = v_isSharedCheck_5287_;
goto v_resetjp_5280_;
}
else
{
lean_inc(v_a_5279_);
lean_dec(v_x_5267_);
v___x_5281_ = lean_box(0);
v_isShared_5282_ = v_isSharedCheck_5287_;
goto v_resetjp_5280_;
}
v_resetjp_5280_:
{
lean_object* v___x_5284_; 
if (v_isShared_5282_ == 0)
{
v___x_5284_ = v___x_5281_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5286_; 
v_reuseFailAlloc_5286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5286_, 0, v_a_5279_);
v___x_5284_ = v_reuseFailAlloc_5286_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
lean_object* v___x_5285_; 
v___x_5285_ = lean_task_pure(v___x_5284_);
return v___x_5285_;
}
}
}
v___jp_5269_:
{
lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; 
lean_inc_ref(v___y_5270_);
v___x_5271_ = lean_mk_io_user_error(v___y_5270_);
v___x_5272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5272_, 0, v___x_5271_);
v___x_5273_ = lean_task_pure(v___x_5272_);
return v___x_5273_;
}
}
}
LEAN_EXPORT void l_Std_Broadcast_send___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5267_ = stack[0].m_obj;
lean_object* v_res_5288_;
v_res_5288_ = l_Std_Broadcast_send___redArg___lam__0(v_x_5267_);
stack->m_obj
 = v_res_5288_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___lam__0___boxed(lean_object* v_x_5289_, lean_object* v___y_5290_){
_start:
{
lean_object* v_res_5291_; 
v_res_5291_ = l_Std_Broadcast_send___redArg___lam__0(v_x_5289_);
return v_res_5291_;
}
}
lean_object* l_Std_Broadcast_send___redArg(lean_object* v_ch_5293_, lean_object* v_v_5294_){
_start:
{
lean_object* v___f_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; uint8_t v___x_5299_; lean_object* v___x_5300_; 
v___f_5296_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5297_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5293_, v_v_5294_);
v___x_5298_ = lean_unsigned_to_nat(0u);
v___x_5299_ = 1;
v___x_5300_ = lean_io_bind_task(v___x_5297_, v___f_5296_, v___x_5298_, v___x_5299_);
return v___x_5300_;
}
}
LEAN_EXPORT void l_Std_Broadcast_send___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5293_ = stack[0].m_obj;
lean_object* v_v_5294_ = stack[1].m_obj;
lean_object* v_res_5301_;
v_res_5301_ = l_Std_Broadcast_send___redArg(v_ch_5293_, v_v_5294_);
stack->m_obj
 = v_res_5301_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___redArg___boxed(lean_object* v_ch_5302_, lean_object* v_v_5303_, lean_object* v_a_5304_){
_start:
{
lean_object* v_res_5305_; 
v_res_5305_ = l_Std_Broadcast_send___redArg(v_ch_5302_, v_v_5303_);
return v_res_5305_;
}
}
lean_object* l_Std_Broadcast_send(lean_object* v_00_u03b1_5306_, lean_object* v_ch_5307_, lean_object* v_v_5308_){
_start:
{
lean_object* v___f_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; uint8_t v___x_5313_; lean_object* v___x_5314_; 
v___f_5310_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5311_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5307_, v_v_5308_);
v___x_5312_ = lean_unsigned_to_nat(0u);
v___x_5313_ = 1;
v___x_5314_ = lean_io_bind_task(v___x_5311_, v___f_5310_, v___x_5312_, v___x_5313_);
return v___x_5314_;
}
}
LEAN_EXPORT void l_Std_Broadcast_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5307_ = stack[1].m_obj;
lean_object* v_v_5308_ = stack[2].m_obj;
lean_object* v_res_5315_;
v_res_5315_ = l_Std_Broadcast_send(lean_box(0), v_ch_5307_, v_v_5308_);
stack->m_obj
 = v_res_5315_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_send___boxed(lean_object* v_00_u03b1_5316_, lean_object* v_ch_5317_, lean_object* v_v_5318_, lean_object* v_a_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l_Std_Broadcast_send(v_00_u03b1_5316_, v_ch_5317_, v_v_5318_);
return v_res_5320_;
}
}
lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg(lean_object* v_ch_5321_){
_start:
{
lean_object* v___x_5323_; 
v___x_5323_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5321_);
return v___x_5323_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5321_ = stack[0].m_obj;
lean_object* v_res_5324_;
v_res_5324_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5321_);
stack->m_obj
 = v_res_5324_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5325_, lean_object* v_a_5326_){
_start:
{
lean_object* v_res_5327_; 
v_res_5327_ = l_Std_Broadcast_Receiver_tryRecv___redArg(v_ch_5325_);
return v_res_5327_;
}
}
lean_object* l_Std_Broadcast_Receiver_tryRecv(lean_object* v_00_u03b1_5328_, lean_object* v_ch_5329_){
_start:
{
lean_object* v___x_5331_; 
v___x_5331_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5329_);
return v___x_5331_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5329_ = stack[1].m_obj;
lean_object* v_res_5332_;
v_res_5332_ = l_Std_Broadcast_Receiver_tryRecv(lean_box(0), v_ch_5329_);
stack->m_obj
 = v_res_5332_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5333_, lean_object* v_ch_5334_, lean_object* v_a_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_Std_Broadcast_Receiver_tryRecv(v_00_u03b1_5333_, v_ch_5334_);
return v_res_5336_;
}
}
lean_object* l_Std_Broadcast_Receiver_recv___redArg(lean_object* v_ch_5337_){
_start:
{
lean_object* v___x_5339_; 
v___x_5339_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5337_);
return v___x_5339_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5337_ = stack[0].m_obj;
lean_object* v_res_5340_;
v_res_5340_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5337_);
stack->m_obj
 = v_res_5340_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___redArg___boxed(lean_object* v_ch_5341_, lean_object* v_a_5342_){
_start:
{
lean_object* v_res_5343_; 
v_res_5343_ = l_Std_Broadcast_Receiver_recv___redArg(v_ch_5341_);
return v_res_5343_;
}
}
lean_object* l_Std_Broadcast_Receiver_recv(lean_object* v_00_u03b1_5344_, lean_object* v_inst_5345_, lean_object* v_ch_5346_){
_start:
{
lean_object* v___x_5348_; 
v___x_5348_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5346_);
return v___x_5348_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5345_ = stack[1].m_obj;
lean_object* v_ch_5346_ = stack[2].m_obj;
lean_object* v_res_5349_;
v_res_5349_ = l_Std_Broadcast_Receiver_recv(lean_box(0), v_inst_5345_, v_ch_5346_);
stack->m_obj
 = v_res_5349_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recv___boxed(lean_object* v_00_u03b1_5350_, lean_object* v_inst_5351_, lean_object* v_ch_5352_, lean_object* v_a_5353_){
_start:
{
lean_object* v_res_5354_; 
v_res_5354_ = l_Std_Broadcast_Receiver_recv(v_00_u03b1_5350_, v_inst_5351_, v_ch_5352_);
lean_dec(v_inst_5351_);
return v_res_5354_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___redArg(lean_object* v_ch_5355_){
_start:
{
lean_object* v___x_5356_; 
v___x_5356_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5355_);
return v___x_5356_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector(lean_object* v_00_u03b1_5357_, lean_object* v_inst_5358_, lean_object* v_ch_5359_){
_start:
{
lean_object* v___x_5360_; 
v___x_5360_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg(v_ch_5359_);
return v___x_5360_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_recvSelector___boxed(lean_object* v_00_u03b1_5361_, lean_object* v_inst_5362_, lean_object* v_ch_5363_){
_start:
{
lean_object* v_res_5364_; 
v_res_5364_ = l_Std_Broadcast_Receiver_recvSelector(v_00_u03b1_5361_, v_inst_5362_, v_ch_5363_);
lean_dec(v_inst_5362_);
return v_res_5364_;
}
}
lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg(lean_object* v_ch_5365_){
_start:
{
lean_object* v___x_5367_; 
v___x_5367_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5365_);
return v___x_5367_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_unsubscribe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5365_ = stack[0].m_obj;
lean_object* v_res_5368_;
v_res_5368_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5365_);
stack->m_obj
 = v_res_5368_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___redArg___boxed(lean_object* v_ch_5369_, lean_object* v_a_5370_){
_start:
{
lean_object* v_res_5371_; 
v_res_5371_ = l_Std_Broadcast_Receiver_unsubscribe___redArg(v_ch_5369_);
return v_res_5371_;
}
}
lean_object* l_Std_Broadcast_Receiver_unsubscribe(lean_object* v_00_u03b1_5372_, lean_object* v_ch_5373_){
_start:
{
lean_object* v___x_5375_; 
v___x_5375_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_unsubscribe___redArg(v_ch_5373_);
return v___x_5375_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_unsubscribe_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5373_ = stack[1].m_obj;
lean_object* v_res_5376_;
v_res_5376_ = l_Std_Broadcast_Receiver_unsubscribe(lean_box(0), v_ch_5373_);
stack->m_obj
 = v_res_5376_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_unsubscribe___boxed(lean_object* v_00_u03b1_5377_, lean_object* v_ch_5378_, lean_object* v_a_5379_){
_start:
{
lean_object* v_res_5380_; 
v_res_5380_ = l_Std_Broadcast_Receiver_unsubscribe(v_00_u03b1_5377_, v_ch_5378_);
return v_res_5380_;
}
}
lean_object* l_Std_Broadcast_Receiver_forAsync___redArg(lean_object* v_f_5381_, lean_object* v_ch_5382_, lean_object* v_prio_5383_){
_start:
{
lean_object* v___x_5385_; 
v___x_5385_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5381_, v_ch_5382_, v_prio_5383_);
return v___x_5385_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_forAsync___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_5381_ = stack[0].m_obj;
lean_object* v_ch_5382_ = stack[1].m_obj;
lean_object* v_prio_5383_ = stack[2].m_obj;
lean_object* v_res_5386_;
v_res_5386_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5381_, v_ch_5382_, v_prio_5383_);
stack->m_obj
 = v_res_5386_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___redArg___boxed(lean_object* v_f_5387_, lean_object* v_ch_5388_, lean_object* v_prio_5389_, lean_object* v_a_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l_Std_Broadcast_Receiver_forAsync___redArg(v_f_5387_, v_ch_5388_, v_prio_5389_);
return v_res_5391_;
}
}
lean_object* l_Std_Broadcast_Receiver_forAsync(lean_object* v_00_u03b1_5392_, lean_object* v_f_5393_, lean_object* v_ch_5394_, lean_object* v_prio_5395_){
_start:
{
lean_object* v___x_5397_; 
v___x_5397_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_forAsync___redArg(v_f_5393_, v_ch_5394_, v_prio_5395_);
return v___x_5397_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_forAsync_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_5393_ = stack[1].m_obj;
lean_object* v_ch_5394_ = stack[2].m_obj;
lean_object* v_prio_5395_ = stack[3].m_obj;
lean_object* v_res_5398_;
v_res_5398_ = l_Std_Broadcast_Receiver_forAsync(lean_box(0), v_f_5393_, v_ch_5394_, v_prio_5395_);
stack->m_obj
 = v_res_5398_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_forAsync___boxed(lean_object* v_00_u03b1_5399_, lean_object* v_f_5400_, lean_object* v_ch_5401_, lean_object* v_prio_5402_, lean_object* v_a_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l_Std_Broadcast_Receiver_forAsync(v_00_u03b1_5399_, v_f_5400_, v_ch_5401_, v_prio_5402_);
return v_res_5404_;
}
}
lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg(){
_start:
{
lean_object* v___x_5411_; 
v___x_5411_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___closed__2));
return v___x_5411_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5412_;
v_res_5412_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg();
stack->m_obj
 = v_res_5412_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg___boxed(lean_object* v___dummy_5413_){
_start:
{
lean_object* v_res_5414_; 
v_res_5414_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg();
return v_res_5414_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5415_; 
v___x_5415_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___redArg();
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(lean_object* v_00_u03b1_5416_, lean_object* v_inst_5417_){
_start:
{
lean_object* v___x_5418_; 
v___x_5418_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___closed__0);
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited___boxed(lean_object* v_00_u03b1_5419_, lean_object* v_inst_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_Std_Broadcast_Receiver_instAsyncStreamOptionOfInhabited(v_00_u03b1_5419_, v_inst_5420_);
lean_dec(v_inst_5420_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__0(lean_object* v_a_5422_){
_start:
{
lean_object* v___x_5423_; 
v___x_5423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5423_, 0, v_a_5422_);
return v___x_5423_;
}
}
lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1(lean_object* v___f_5424_, lean_object* v_x_5425_){
_start:
{
if (lean_obj_tag(v_x_5425_) == 0)
{
lean_object* v_a_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5435_; 
lean_dec_ref(v___f_5424_);
v_a_5427_ = lean_ctor_get(v_x_5425_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v_x_5425_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5429_ = v_x_5425_;
v_isShared_5430_ = v_isSharedCheck_5435_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_a_5427_);
lean_dec(v_x_5425_);
v___x_5429_ = lean_box(0);
v_isShared_5430_ = v_isSharedCheck_5435_;
goto v_resetjp_5428_;
}
v_resetjp_5428_:
{
lean_object* v___x_5432_; 
if (v_isShared_5430_ == 0)
{
v___x_5432_ = v___x_5429_;
goto v_reusejp_5431_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5427_);
v___x_5432_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5431_;
}
v_reusejp_5431_:
{
lean_object* v___x_5433_; 
v___x_5433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5433_, 0, v___x_5432_);
return v___x_5433_;
}
}
}
else
{
lean_object* v_a_5436_; 
v_a_5436_ = lean_ctor_get(v_x_5425_, 0);
lean_inc(v_a_5436_);
lean_dec_ref_known(v_x_5425_, 1);
if (lean_obj_tag(v_a_5436_) == 0)
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5445_; 
lean_dec_ref(v___f_5424_);
v_a_5437_ = lean_ctor_get(v_a_5436_, 0);
v_isSharedCheck_5445_ = !lean_is_exclusive(v_a_5436_);
if (v_isSharedCheck_5445_ == 0)
{
v___x_5439_ = v_a_5436_;
v_isShared_5440_ = v_isSharedCheck_5445_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v_a_5436_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5445_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
lean_object* v___x_5443_; 
v___x_5443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5442_);
return v___x_5443_;
}
}
}
else
{
lean_object* v_a_5446_; lean_object* v___x_5447_; uint8_t v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; 
v_a_5446_ = lean_ctor_get(v_a_5436_, 0);
lean_inc(v_a_5446_);
lean_dec_ref_known(v_a_5436_, 1);
v___x_5447_ = lean_unsigned_to_nat(0u);
v___x_5448_ = 0;
v___x_5449_ = lean_task_map(v___f_5424_, v_a_5446_, v___x_5447_, v___x_5448_);
v___x_5450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5450_, 0, v___x_5449_);
return v___x_5450_;
}
}
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5424_ = stack[0].m_obj;
lean_object* v_x_5425_ = stack[1].m_obj;
lean_object* v_res_5451_;
v_res_5451_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1(v___f_5424_, v_x_5425_);
stack->m_obj
 = v_res_5451_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1___boxed(lean_object* v___f_5452_, lean_object* v_x_5453_, lean_object* v___y_5454_){
_start:
{
lean_object* v_res_5455_; 
v_res_5455_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__1(v___f_5452_, v_x_5453_);
return v_res_5455_;
}
}
lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2(lean_object* v___f_5456_, lean_object* v_receiver_5457_){
_start:
{
lean_object* v___x_5459_; uint8_t v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; 
v___x_5459_ = lean_unsigned_to_nat(0u);
v___x_5460_ = 0;
v___x_5461_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_receiver_5457_);
v___x_5462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5462_, 0, v___x_5461_);
v___x_5463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5463_, 0, v___x_5462_);
v___x_5464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5464_, 0, v___x_5463_);
v___x_5465_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5459_, v___x_5460_, v___x_5464_, v___f_5456_);
return v___x_5465_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5456_ = stack[0].m_obj;
lean_object* v_receiver_5457_ = stack[1].m_obj;
lean_object* v_res_5466_;
v_res_5466_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2(v___f_5456_, v_receiver_5457_);
stack->m_obj
 = v_res_5466_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5467_, lean_object* v_receiver_5468_, lean_object* v___y_5469_){
_start:
{
lean_object* v_res_5470_; 
v_res_5470_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___lam__2(v___f_5467_, v_receiver_5468_);
return v_res_5470_;
}
}
lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg(){
_start:
{
lean_object* v___f_5477_; 
v___f_5477_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___closed__2));
return v___f_5477_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5478_;
v_res_5478_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg();
stack->m_obj
 = v_res_5478_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg___boxed(lean_object* v___dummy_5479_){
_start:
{
lean_object* v_res_5480_; 
v_res_5480_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg();
return v_res_5480_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5481_; 
v___x_5481_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___redArg();
return v___x_5481_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(lean_object* v_00_u03b1_5482_, lean_object* v_inst_5483_){
_start:
{
lean_object* v___x_5484_; 
v___x_5484_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___closed__0);
return v___x_5484_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited___boxed(lean_object* v_00_u03b1_5485_, lean_object* v_inst_5486_){
_start:
{
lean_object* v_res_5487_; 
v_res_5487_ = l_Std_Broadcast_Receiver_instAsyncReadOptionOfInhabited(v_00_u03b1_5485_, v_inst_5486_);
lean_dec(v_inst_5486_);
return v_res_5487_;
}
}
lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0(lean_object* v_x_5492_){
_start:
{
if (lean_obj_tag(v_x_5492_) == 0)
{
lean_object* v_a_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5502_; 
v_a_5494_ = lean_ctor_get(v_x_5492_, 0);
v_isSharedCheck_5502_ = !lean_is_exclusive(v_x_5492_);
if (v_isSharedCheck_5502_ == 0)
{
v___x_5496_ = v_x_5492_;
v_isShared_5497_ = v_isSharedCheck_5502_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_a_5494_);
lean_dec(v_x_5492_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5502_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5499_; 
if (v_isShared_5497_ == 0)
{
v___x_5499_ = v___x_5496_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_a_5494_);
v___x_5499_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
lean_object* v___x_5500_; 
v___x_5500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5500_, 0, v___x_5499_);
return v___x_5500_;
}
}
}
else
{
lean_object* v_a_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; uint8_t v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; 
v_a_5503_ = lean_ctor_get(v_x_5492_, 0);
lean_inc(v_a_5503_);
lean_dec_ref_known(v_x_5492_, 1);
v___x_5504_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___closed__1));
v___x_5505_ = lean_unsigned_to_nat(0u);
v___x_5506_ = 0;
v___x_5507_ = lean_task_map(v___x_5504_, v_a_5503_, v___x_5505_, v___x_5506_);
v___x_5508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5508_, 0, v___x_5507_);
return v___x_5508_;
}
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5492_ = stack[0].m_obj;
lean_object* v_res_5509_;
v_res_5509_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0(v_x_5492_);
stack->m_obj
 = v_res_5509_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0___boxed(lean_object* v_x_5510_, lean_object* v___y_5511_){
_start:
{
lean_object* v_res_5512_; 
v_res_5512_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__0(v_x_5510_);
return v_res_5512_;
}
}
lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(lean_object* v___f_5513_, lean_object* v___f_5514_, lean_object* v_receiver_5515_, lean_object* v_x_5516_){
_start:
{
lean_object* v___x_5518_; uint8_t v___x_5519_; lean_object* v___x_5520_; uint8_t v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; 
v___x_5518_ = lean_unsigned_to_nat(0u);
v___x_5519_ = 0;
v___x_5520_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_receiver_5515_, v_x_5516_);
v___x_5521_ = 1;
v___x_5522_ = lean_io_bind_task(v___x_5520_, v___f_5513_, v___x_5518_, v___x_5521_);
v___x_5523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5523_, 0, v___x_5522_);
v___x_5524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5523_);
v___x_5525_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_5518_, v___x_5519_, v___x_5524_, v___f_5514_);
return v___x_5525_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5513_ = stack[0].m_obj;
lean_object* v___f_5514_ = stack[1].m_obj;
lean_object* v_receiver_5515_ = stack[2].m_obj;
lean_object* v_x_5516_ = stack[3].m_obj;
lean_object* v_res_5526_;
v_res_5526_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(v___f_5513_, v___f_5514_, v_receiver_5515_, v_x_5516_);
stack->m_obj
 = v_res_5526_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2___boxed(lean_object* v___f_5527_, lean_object* v___f_5528_, lean_object* v_receiver_5529_, lean_object* v_x_5530_, lean_object* v___y_5531_){
_start:
{
lean_object* v_res_5532_; 
v_res_5532_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__2(v___f_5527_, v___f_5528_, v_receiver_5529_, v_x_5530_);
return v_res_5532_;
}
}
lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(lean_object* v_x_5533_){
_start:
{
lean_object* v___x_5535_; 
v___x_5535_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5535_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5533_ = stack[0].m_obj;
lean_object* v_res_5536_;
v_res_5536_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(v_x_5533_);
stack->m_obj
 = v_res_5536_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1___boxed(lean_object* v_x_5537_, lean_object* v___y_5538_){
_start:
{
lean_object* v_res_5539_; 
v_res_5539_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__1(v_x_5537_);
lean_dec_ref(v_x_5537_);
return v_res_5539_;
}
}
lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(lean_object* v___f_5540_, lean_object* v_socket_5541_, lean_object* v_x_5542_, lean_object* v___y_5543_){
_start:
{
lean_object* v___x_5545_; 
v___x_5545_ = lean_apply_3(v___f_5540_, v_socket_5541_, v___y_5543_, lean_box(0));
return v___x_5545_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5540_ = stack[0].m_obj;
lean_object* v_socket_5541_ = stack[1].m_obj;
lean_object* v_x_5542_ = stack[2].m_obj;
lean_object* v___y_5543_ = stack[3].m_obj;
lean_object* v_res_5546_;
v_res_5546_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(v___f_5540_, v_socket_5541_, v_x_5542_, v___y_5543_);
stack->m_obj
 = v_res_5546_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3___boxed(lean_object* v___f_5547_, lean_object* v_socket_5548_, lean_object* v_x_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_){
_start:
{
lean_object* v_res_5552_; 
v_res_5552_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3(v___f_5547_, v_socket_5548_, v_x_5549_, v___y_5550_);
return v_res_5552_;
}
}
lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(lean_object* v___f_5553_, lean_object* v___x_5554_, lean_object* v_socket_5555_, lean_object* v_data_5556_){
_start:
{
lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; uint8_t v___x_5561_; 
v___x_5558_ = lean_unsigned_to_nat(0u);
v___x_5559_ = lean_array_get_size(v_data_5556_);
v___x_5560_ = lean_box(0);
v___x_5561_ = lean_nat_dec_lt(v___x_5558_, v___x_5559_);
if (v___x_5561_ == 0)
{
lean_object* v___x_5562_; 
lean_dec_ref(v_data_5556_);
lean_dec_ref(v_socket_5555_);
lean_dec_ref(v___x_5554_);
lean_dec_ref(v___f_5553_);
v___x_5562_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5562_;
}
else
{
lean_object* v___f_5563_; uint8_t v___x_5564_; 
v___f_5563_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__3___boxed), 5, 2);
lean_closure_set(v___f_5563_, 0, v___f_5553_);
lean_closure_set(v___f_5563_, 1, v_socket_5555_);
v___x_5564_ = lean_nat_dec_le(v___x_5559_, v___x_5559_);
if (v___x_5564_ == 0)
{
if (v___x_5561_ == 0)
{
lean_object* v___x_5565_; 
lean_dec_ref(v___f_5563_);
lean_dec_ref(v_data_5556_);
lean_dec_ref(v___x_5554_);
v___x_5565_ = ((lean_object*)(l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recvSelector___redArg___lam__0___closed__1));
return v___x_5565_;
}
else
{
size_t v___x_5566_; size_t v___x_5567_; lean_object* v___x_873__overap_5568_; lean_object* v___x_5569_; 
v___x_5566_ = ((size_t)0ULL);
v___x_5567_ = lean_usize_of_nat(v___x_5559_);
v___x_873__overap_5568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5554_, v___f_5563_, v_data_5556_, v___x_5566_, v___x_5567_, v___x_5560_);
v___x_5569_ = lean_apply_1(v___x_873__overap_5568_, lean_box(0));
return v___x_5569_;
}
}
else
{
size_t v___x_5570_; size_t v___x_5571_; lean_object* v___x_876__overap_5572_; lean_object* v___x_5573_; 
v___x_5570_ = ((size_t)0ULL);
v___x_5571_ = lean_usize_of_nat(v___x_5559_);
v___x_876__overap_5572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_5554_, v___f_5563_, v_data_5556_, v___x_5570_, v___x_5571_, v___x_5560_);
v___x_5573_ = lean_apply_1(v___x_876__overap_5572_, lean_box(0));
return v___x_5573_;
}
}
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_5553_ = stack[0].m_obj;
lean_object* v___x_5554_ = stack[1].m_obj;
lean_object* v_socket_5555_ = stack[2].m_obj;
lean_object* v_data_5556_ = stack[3].m_obj;
lean_object* v_res_5574_;
v_res_5574_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(v___f_5553_, v___x_5554_, v_socket_5555_, v_data_5556_);
stack->m_obj
 = v_res_5574_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4___boxed(lean_object* v___f_5575_, lean_object* v___x_5576_, lean_object* v_socket_5577_, lean_object* v_data_5578_, lean_object* v___y_5579_){
_start:
{
lean_object* v_res_5580_; 
v_res_5580_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4(v___f_5575_, v___x_5576_, v_socket_5577_, v_data_5578_);
return v_res_5580_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3(void){
_start:
{
lean_object* v___x_5586_; 
v___x_5586_ = l_Std_Async_EAsync_instMonad___redArg();
return v___x_5586_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4(void){
_start:
{
lean_object* v___x_5587_; lean_object* v___f_5588_; lean_object* v___f_5589_; 
v___x_5587_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__3);
v___f_5588_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1));
v___f_5589_ = lean_alloc_closure((void*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___lam__4___boxed), 5, 2);
lean_closure_set(v___f_5589_, 0, v___f_5588_);
lean_closure_set(v___f_5589_, 1, v___x_5587_);
return v___f_5589_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5(void){
_start:
{
lean_object* v___f_5590_; lean_object* v___f_5591_; lean_object* v___f_5592_; lean_object* v___x_5593_; 
v___f_5590_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__2));
v___f_5591_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__4);
v___f_5592_ = ((lean_object*)(l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__1));
v___x_5593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5593_, 0, v___f_5592_);
lean_ctor_set(v___x_5593_, 1, v___f_5591_);
lean_ctor_set(v___x_5593_, 2, v___f_5590_);
return v___x_5593_;
}
}
lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg(){
_start:
{
lean_object* v___x_5595_; 
v___x_5595_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___closed__5);
return v___x_5595_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_5596_;
v_res_5596_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg();
stack->m_obj
 = v_res_5596_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg___boxed(lean_object* v___dummy_5597_){
_start:
{
lean_object* v_res_5598_; 
v_res_5598_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg();
return v_res_5598_;
}
}
static lean_object* _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0(void){
_start:
{
lean_object* v___x_5599_; 
v___x_5599_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___redArg();
return v___x_5599_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(lean_object* v_00_u03b1_5600_, lean_object* v_inst_5601_){
_start:
{
lean_object* v___x_5602_; 
v___x_5602_ = lean_obj_once(&l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0, &l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0_once, _init_l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___closed__0);
return v___x_5602_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited___boxed(lean_object* v_00_u03b1_5603_, lean_object* v_inst_5604_){
_start:
{
lean_object* v_res_5605_; 
v_res_5605_ = l_Std_Broadcast_Receiver_instAsyncWriteOfInhabited(v_00_u03b1_5603_, v_inst_5604_);
lean_dec(v_inst_5604_);
return v_res_5605_;
}
}
static lean_object* _init_l_Std_Broadcast_Sync_new___auto__3(void){
_start:
{
lean_object* v___x_5606_; 
v___x_5606_ = lean_obj_once(&l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26, &l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26_once, _init_l___private_Std_Sync_Broadcast_0__Std_Bounded_new___auto__1___closed__26);
return v___x_5606_;
}
}
lean_object* l_Std_Broadcast_Sync_new___redArg(lean_object* v_capacity_5607_){
_start:
{
lean_object* v___x_5609_; 
v___x_5609_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5607_);
return v___x_5609_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Sync_new___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_5607_ = stack[0].m_obj;
lean_object* v_res_5610_;
v_res_5610_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5607_);
stack->m_obj
 = v_res_5610_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___redArg___boxed(lean_object* v_capacity_5611_, lean_object* v_a_5612_){
_start:
{
lean_object* v_res_5613_; 
v_res_5613_ = l_Std_Broadcast_Sync_new___redArg(v_capacity_5611_);
return v_res_5613_;
}
}
lean_object* l_Std_Broadcast_Sync_new(lean_object* v_00_u03b1_5614_, lean_object* v_capacity_5615_, lean_object* v_h_5616_){
_start:
{
lean_object* v___x_5618_; 
v___x_5618_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_new___redArg(v_capacity_5615_);
return v___x_5618_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Sync_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_capacity_5615_ = stack[1].m_obj;
lean_object* v_res_5619_;
v_res_5619_ = l_Std_Broadcast_Sync_new(lean_box(0), v_capacity_5615_, lean_box(0));
stack->m_obj
 = v_res_5619_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_new___boxed(lean_object* v_00_u03b1_5620_, lean_object* v_capacity_5621_, lean_object* v_h_5622_, lean_object* v_a_5623_){
_start:
{
lean_object* v_res_5624_; 
v_res_5624_ = l_Std_Broadcast_Sync_new(v_00_u03b1_5620_, v_capacity_5621_, v_h_5622_);
return v_res_5624_;
}
}
lean_object* l_Std_Broadcast_Sync_trySend___redArg(lean_object* v_ch_5625_, lean_object* v_v_5626_){
_start:
{
lean_object* v___x_5628_; 
v___x_5628_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5625_, v_v_5626_);
return v___x_5628_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Sync_trySend___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5625_ = stack[0].m_obj;
lean_object* v_v_5626_ = stack[1].m_obj;
lean_object* v_res_5629_;
v_res_5629_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5625_, v_v_5626_);
stack->m_obj
 = v_res_5629_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___redArg___boxed(lean_object* v_ch_5630_, lean_object* v_v_5631_, lean_object* v_a_5632_){
_start:
{
lean_object* v_res_5633_; 
v_res_5633_ = l_Std_Broadcast_Sync_trySend___redArg(v_ch_5630_, v_v_5631_);
return v_res_5633_;
}
}
lean_object* l_Std_Broadcast_Sync_trySend(lean_object* v_00_u03b1_5634_, lean_object* v_ch_5635_, lean_object* v_v_5636_){
_start:
{
lean_object* v___x_5638_; 
v___x_5638_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_trySend___redArg(v_ch_5635_, v_v_5636_);
return v___x_5638_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Sync_trySend_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5635_ = stack[1].m_obj;
lean_object* v_v_5636_ = stack[2].m_obj;
lean_object* v_res_5639_;
v_res_5639_ = l_Std_Broadcast_Sync_trySend(lean_box(0), v_ch_5635_, v_v_5636_);
stack->m_obj
 = v_res_5639_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_trySend___boxed(lean_object* v_00_u03b1_5640_, lean_object* v_ch_5641_, lean_object* v_v_5642_, lean_object* v_a_5643_){
_start:
{
lean_object* v_res_5644_; 
v_res_5644_ = l_Std_Broadcast_Sync_trySend(v_00_u03b1_5640_, v_ch_5641_, v_v_5642_);
return v_res_5644_;
}
}
lean_object* l_Std_Broadcast_Sync_send___redArg(lean_object* v_ch_5646_, lean_object* v_v_5647_){
_start:
{
lean_object* v___f_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; uint8_t v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5656_; 
v___f_5649_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5650_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5651_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5646_, v_v_5647_);
v___x_5652_ = lean_unsigned_to_nat(0u);
v___x_5653_ = 1;
v___x_5654_ = lean_io_bind_task(v___x_5651_, v___f_5649_, v___x_5652_, v___x_5653_);
v___x_5655_ = lean_io_wait(v___x_5654_);
v___x_5656_ = l_IO_ofExcept___redArg(v___x_5650_, v___x_5655_);
return v___x_5656_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Sync_send___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5646_ = stack[0].m_obj;
lean_object* v_v_5647_ = stack[1].m_obj;
lean_object* v_res_5657_;
v_res_5657_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5646_, v_v_5647_);
stack->m_obj
 = v_res_5657_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___redArg___boxed(lean_object* v_ch_5658_, lean_object* v_v_5659_, lean_object* v_a_5660_){
_start:
{
lean_object* v_res_5661_; 
v_res_5661_ = l_Std_Broadcast_Sync_send___redArg(v_ch_5658_, v_v_5659_);
return v_res_5661_;
}
}
lean_object* l_Std_Broadcast_Sync_send(lean_object* v_00_u03b1_5662_, lean_object* v_ch_5663_, lean_object* v_v_5664_){
_start:
{
lean_object* v___f_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; uint8_t v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; 
v___f_5666_ = ((lean_object*)(l_Std_Broadcast_send___redArg___closed__0));
v___x_5667_ = ((lean_object*)(l_Std_Broadcast_Sync_send___redArg___closed__0));
v___x_5668_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_send___redArg(v_ch_5663_, v_v_5664_);
v___x_5669_ = lean_unsigned_to_nat(0u);
v___x_5670_ = 1;
v___x_5671_ = lean_io_bind_task(v___x_5668_, v___f_5666_, v___x_5669_, v___x_5670_);
v___x_5672_ = lean_io_wait(v___x_5671_);
v___x_5673_ = l_IO_ofExcept___redArg(v___x_5667_, v___x_5672_);
return v___x_5673_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Sync_send_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5663_ = stack[1].m_obj;
lean_object* v_v_5664_ = stack[2].m_obj;
lean_object* v_res_5674_;
v_res_5674_ = l_Std_Broadcast_Sync_send(lean_box(0), v_ch_5663_, v_v_5664_);
stack->m_obj
 = v_res_5674_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_send___boxed(lean_object* v_00_u03b1_5675_, lean_object* v_ch_5676_, lean_object* v_v_5677_, lean_object* v_a_5678_){
_start:
{
lean_object* v_res_5679_; 
v_res_5679_ = l_Std_Broadcast_Sync_send(v_00_u03b1_5675_, v_ch_5676_, v_v_5677_);
return v_res_5679_;
}
}
lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(lean_object* v_ch_5680_){
_start:
{
lean_object* v___x_5682_; 
v___x_5682_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5680_);
return v___x_5682_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Sync_Receiver_tryRecv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5680_ = stack[0].m_obj;
lean_object* v_res_5683_;
v_res_5683_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5680_);
stack->m_obj
 = v_res_5683_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___redArg___boxed(lean_object* v_ch_5684_, lean_object* v_a_5685_){
_start:
{
lean_object* v_res_5686_; 
v_res_5686_ = l_Std_Broadcast_Sync_Receiver_tryRecv___redArg(v_ch_5684_);
return v_res_5686_;
}
}
lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv(lean_object* v_00_u03b1_5687_, lean_object* v_ch_5688_){
_start:
{
lean_object* v___x_5690_; 
v___x_5690_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_tryRecv___redArg(v_ch_5688_);
return v___x_5690_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Sync_Receiver_tryRecv_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5688_ = stack[1].m_obj;
lean_object* v_res_5691_;
v_res_5691_ = l_Std_Broadcast_Sync_Receiver_tryRecv(lean_box(0), v_ch_5688_);
stack->m_obj
 = v_res_5691_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_tryRecv___boxed(lean_object* v_00_u03b1_5692_, lean_object* v_ch_5693_, lean_object* v_a_5694_){
_start:
{
lean_object* v_res_5695_; 
v_res_5695_ = l_Std_Broadcast_Sync_Receiver_tryRecv(v_00_u03b1_5692_, v_ch_5693_);
return v_res_5695_;
}
}
lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg(lean_object* v_ch_5696_){
_start:
{
lean_object* v___x_5698_; lean_object* v___x_5699_; 
v___x_5698_ = l___private_Std_Sync_Broadcast_0__Std_Bounded_Receiver_recv___redArg(v_ch_5696_);
v___x_5699_ = lean_io_wait(v___x_5698_);
return v___x_5699_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Sync_Receiver_recv___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ch_5696_ = stack[0].m_obj;
lean_object* v_res_5700_;
v_res_5700_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5696_);
stack->m_obj
 = v_res_5700_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___redArg___boxed(lean_object* v_ch_5701_, lean_object* v_a_5702_){
_start:
{
lean_object* v_res_5703_; 
v_res_5703_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5701_);
return v_res_5703_;
}
}
lean_object* l_Std_Broadcast_Sync_Receiver_recv(lean_object* v_00_u03b1_5704_, lean_object* v_inst_5705_, lean_object* v_ch_5706_){
_start:
{
lean_object* v___x_5708_; 
v___x_5708_ = l_Std_Broadcast_Sync_Receiver_recv___redArg(v_ch_5706_);
return v___x_5708_;
}
}
LEAN_EXPORT void l_Std_Broadcast_Sync_Receiver_recv_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_5705_ = stack[1].m_obj;
lean_object* v_ch_5706_ = stack[2].m_obj;
lean_object* v_res_5709_;
v_res_5709_ = l_Std_Broadcast_Sync_Receiver_recv(lean_box(0), v_inst_5705_, v_ch_5706_);
stack->m_obj
 = v_res_5709_;
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_recv___boxed(lean_object* v_00_u03b1_5710_, lean_object* v_inst_5711_, lean_object* v_ch_5712_, lean_object* v_a_5713_){
_start:
{
lean_object* v_res_5714_; 
v_res_5714_ = l_Std_Broadcast_Sync_Receiver_recv(v_00_u03b1_5710_, v_inst_5711_, v_ch_5712_);
lean_dec(v_inst_5711_);
return v_res_5714_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1(lean_object* v_toPure_5715_, lean_object* v_b_5716_, lean_object* v_f_5717_, lean_object* v_toBind_5718_, lean_object* v___f_5719_, lean_object* v_a_5720_){
_start:
{
if (lean_obj_tag(v_a_5720_) == 0)
{
lean_object* v___x_5721_; 
lean_dec(v___f_5719_);
lean_dec(v_toBind_5718_);
lean_dec(v_f_5717_);
v___x_5721_ = lean_apply_2(v_toPure_5715_, lean_box(0), v_b_5716_);
return v___x_5721_;
}
else
{
lean_object* v_val_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; 
lean_dec(v_toPure_5715_);
v_val_5722_ = lean_ctor_get(v_a_5720_, 0);
lean_inc(v_val_5722_);
lean_dec_ref_known(v_a_5720_, 1);
v___x_5723_ = lean_apply_2(v_f_5717_, v_val_5722_, v_b_5716_);
v___x_5724_ = lean_apply_4(v_toBind_5718_, lean_box(0), lean_box(0), v___x_5723_, v___f_5719_);
return v___x_5724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg(lean_object* v_inst_5725_, lean_object* v_inst_5726_, lean_object* v_inst_5727_, lean_object* v_ch_5728_, lean_object* v_f_5729_, lean_object* v_b_5730_){
_start:
{
lean_object* v_toApplicative_5731_; lean_object* v_toBind_5732_; lean_object* v_toPure_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___f_5736_; lean_object* v___f_5737_; lean_object* v___x_5738_; 
v_toApplicative_5731_ = lean_ctor_get(v_inst_5726_, 0);
v_toBind_5732_ = lean_ctor_get(v_inst_5726_, 1);
lean_inc_n(v_toBind_5732_, 2);
v_toPure_5733_ = lean_ctor_get(v_toApplicative_5731_, 1);
lean_inc_n(v_toPure_5733_, 2);
lean_inc_ref(v_ch_5728_);
lean_inc(v_inst_5725_);
v___x_5734_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_recv___boxed), 4, 3);
lean_closure_set(v___x_5734_, 0, lean_box(0));
lean_closure_set(v___x_5734_, 1, v_inst_5725_);
lean_closure_set(v___x_5734_, 2, v_ch_5728_);
lean_inc(v_inst_5727_);
v___x_5735_ = lean_apply_2(v_inst_5727_, lean_box(0), v___x_5734_);
lean_inc(v_f_5729_);
v___f_5736_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_5736_, 0, v_toPure_5733_);
lean_closure_set(v___f_5736_, 1, v_inst_5725_);
lean_closure_set(v___f_5736_, 2, v_inst_5726_);
lean_closure_set(v___f_5736_, 3, v_inst_5727_);
lean_closure_set(v___f_5736_, 4, v_ch_5728_);
lean_closure_set(v___f_5736_, 5, v_f_5729_);
v___f_5737_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__1), 6, 5);
lean_closure_set(v___f_5737_, 0, v_toPure_5733_);
lean_closure_set(v___f_5737_, 1, v_b_5730_);
lean_closure_set(v___f_5737_, 2, v_f_5729_);
lean_closure_set(v___f_5737_, 3, v_toBind_5732_);
lean_closure_set(v___f_5737_, 4, v___f_5736_);
v___x_5738_ = lean_apply_4(v_toBind_5732_, lean_box(0), lean_box(0), v___x_5735_, v___f_5737_);
return v___x_5738_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn___redArg___lam__0(lean_object* v_toPure_5739_, lean_object* v_inst_5740_, lean_object* v_inst_5741_, lean_object* v_inst_5742_, lean_object* v_ch_5743_, lean_object* v_f_5744_, lean_object* v_____do__lift_5745_){
_start:
{
if (lean_obj_tag(v_____do__lift_5745_) == 0)
{
lean_object* v_a_5746_; lean_object* v___x_5747_; 
lean_dec(v_f_5744_);
lean_dec_ref(v_ch_5743_);
lean_dec(v_inst_5742_);
lean_dec_ref(v_inst_5741_);
lean_dec(v_inst_5740_);
v_a_5746_ = lean_ctor_get(v_____do__lift_5745_, 0);
lean_inc(v_a_5746_);
lean_dec_ref_known(v_____do__lift_5745_, 1);
v___x_5747_ = lean_apply_2(v_toPure_5739_, lean_box(0), v_a_5746_);
return v___x_5747_;
}
else
{
lean_object* v_a_5748_; lean_object* v___x_5749_; 
lean_dec(v_toPure_5739_);
v_a_5748_ = lean_ctor_get(v_____do__lift_5745_, 0);
lean_inc(v_a_5748_);
lean_dec_ref_known(v_____do__lift_5745_, 1);
v___x_5749_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5740_, v_inst_5741_, v_inst_5742_, v_ch_5743_, v_f_5744_, v_a_5748_);
return v___x_5749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_forIn(lean_object* v_00_u03b1_5750_, lean_object* v_m_5751_, lean_object* v_00_u03b2_5752_, lean_object* v_inst_5753_, lean_object* v_inst_5754_, lean_object* v_inst_5755_, lean_object* v_ch_5756_, lean_object* v_f_5757_, lean_object* v_b_5758_){
_start:
{
lean_object* v___x_5759_; 
v___x_5759_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5753_, v_inst_5754_, v_inst_5755_, v_ch_5756_, v_f_5757_, v_b_5758_);
return v___x_5759_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(lean_object* v_inst_5760_, lean_object* v_inst_5761_, lean_object* v_inst_5762_, lean_object* v_00_u03b2_5763_, lean_object* v_ch_5764_, lean_object* v_b_5765_, lean_object* v_f_5766_){
_start:
{
lean_object* v___x_5767_; 
v___x_5767_ = l_Std_Broadcast_Sync_Receiver_forIn___redArg(v_inst_5760_, v_inst_5761_, v_inst_5762_, v_ch_5764_, v_f_5766_, v_b_5765_);
return v___x_5767_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(lean_object* v_inst_5768_, lean_object* v_inst_5769_, lean_object* v_inst_5770_){
_start:
{
lean_object* v___f_5771_; 
v___f_5771_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5771_, 0, v_inst_5768_);
lean_closure_set(v___f_5771_, 1, v_inst_5769_);
lean_closure_set(v___f_5771_, 2, v_inst_5770_);
return v___f_5771_;
}
}
LEAN_EXPORT lean_object* l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(lean_object* v_00_u03b1_5772_, lean_object* v_m_5773_, lean_object* v_inst_5774_, lean_object* v_inst_5775_, lean_object* v_inst_5776_){
_start:
{
lean_object* v___f_5777_; 
v___f_5777_ = lean_alloc_closure((void*)(l_Std_Broadcast_Sync_Receiver_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0), 7, 3);
lean_closure_set(v___f_5777_, 0, v_inst_5774_);
lean_closure_set(v___f_5777_, 1, v_inst_5775_);
lean_closure_set(v___f_5777_, 2, v_inst_5776_);
return v___f_5777_;
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

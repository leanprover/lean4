// Lean compiler output
// Module: Std.Sync.CancellationToken
// Imports: public import Std.Data public import Init.Data.Queue public import Std.Sync.Mutex public import Std.Async.Select public import Init.Data.ToString.Macro
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Queue_empty___redArg();
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_promise_new();
lean_object* l_Std_Queue_enqueue___redArg(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_deadline_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_deadline_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_shutdown_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_shutdown_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_cancel_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_cancel_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_custom_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_custom_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_instReprCancellationReason_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.CancellationReason.cancel"};
static const lean_object* l_Std_instReprCancellationReason_repr___closed__0 = (const lean_object*)&l_Std_instReprCancellationReason_repr___closed__0_value;
static const lean_ctor_object l_Std_instReprCancellationReason_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_instReprCancellationReason_repr___closed__0_value)}};
static const lean_object* l_Std_instReprCancellationReason_repr___closed__1 = (const lean_object*)&l_Std_instReprCancellationReason_repr___closed__1_value;
static const lean_string_object l_Std_instReprCancellationReason_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.CancellationReason.shutdown"};
static const lean_object* l_Std_instReprCancellationReason_repr___closed__2 = (const lean_object*)&l_Std_instReprCancellationReason_repr___closed__2_value;
static const lean_ctor_object l_Std_instReprCancellationReason_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_instReprCancellationReason_repr___closed__2_value)}};
static const lean_object* l_Std_instReprCancellationReason_repr___closed__3 = (const lean_object*)&l_Std_instReprCancellationReason_repr___closed__3_value;
static const lean_string_object l_Std_instReprCancellationReason_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.CancellationReason.deadline"};
static const lean_object* l_Std_instReprCancellationReason_repr___closed__4 = (const lean_object*)&l_Std_instReprCancellationReason_repr___closed__4_value;
static const lean_ctor_object l_Std_instReprCancellationReason_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_instReprCancellationReason_repr___closed__4_value)}};
static const lean_object* l_Std_instReprCancellationReason_repr___closed__5 = (const lean_object*)&l_Std_instReprCancellationReason_repr___closed__5_value;
static lean_once_cell_t l_Std_instReprCancellationReason_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_instReprCancellationReason_repr___closed__6;
static lean_once_cell_t l_Std_instReprCancellationReason_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_instReprCancellationReason_repr___closed__7;
static const lean_string_object l_Std_instReprCancellationReason_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Std.CancellationReason.custom"};
static const lean_object* l_Std_instReprCancellationReason_repr___closed__8 = (const lean_object*)&l_Std_instReprCancellationReason_repr___closed__8_value;
static const lean_ctor_object l_Std_instReprCancellationReason_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_instReprCancellationReason_repr___closed__8_value)}};
static const lean_object* l_Std_instReprCancellationReason_repr___closed__9 = (const lean_object*)&l_Std_instReprCancellationReason_repr___closed__9_value;
static const lean_ctor_object l_Std_instReprCancellationReason_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_instReprCancellationReason_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_instReprCancellationReason_repr___closed__10 = (const lean_object*)&l_Std_instReprCancellationReason_repr___closed__10_value;
LEAN_EXPORT lean_object* l_Std_instReprCancellationReason_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instReprCancellationReason_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_instReprCancellationReason___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instReprCancellationReason_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instReprCancellationReason___closed__0 = (const lean_object*)&l_Std_instReprCancellationReason___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instReprCancellationReason = (const lean_object*)&l_Std_instReprCancellationReason___closed__0_value;
LEAN_EXPORT uint8_t l_Std_instBEqCancellationReason_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_instBEqCancellationReason_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_instBEqCancellationReason___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instBEqCancellationReason_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instBEqCancellationReason___closed__0 = (const lean_object*)&l_Std_instBEqCancellationReason___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instBEqCancellationReason = (const lean_object*)&l_Std_instBEqCancellationReason___closed__0_value;
static const lean_string_object l_Std_instToStringCancellationReason___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deadline"};
static const lean_object* l_Std_instToStringCancellationReason___lam__0___closed__0 = (const lean_object*)&l_Std_instToStringCancellationReason___lam__0___closed__0_value;
static const lean_string_object l_Std_instToStringCancellationReason___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "shutdown"};
static const lean_object* l_Std_instToStringCancellationReason___lam__0___closed__1 = (const lean_object*)&l_Std_instToStringCancellationReason___lam__0___closed__1_value;
static const lean_string_object l_Std_instToStringCancellationReason___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cancel"};
static const lean_object* l_Std_instToStringCancellationReason___lam__0___closed__2 = (const lean_object*)&l_Std_instToStringCancellationReason___lam__0___closed__2_value;
static const lean_string_object l_Std_instToStringCancellationReason___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "custom(\""};
static const lean_object* l_Std_instToStringCancellationReason___lam__0___closed__3 = (const lean_object*)&l_Std_instToStringCancellationReason___lam__0___closed__3_value;
static const lean_string_object l_Std_instToStringCancellationReason___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\")"};
static const lean_object* l_Std_instToStringCancellationReason___lam__0___closed__4 = (const lean_object*)&l_Std_instToStringCancellationReason___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Std_instToStringCancellationReason___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_instToStringCancellationReason___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_instToStringCancellationReason___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_instToStringCancellationReason___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_instToStringCancellationReason___closed__0 = (const lean_object*)&l_Std_instToStringCancellationReason___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_instToStringCancellationReason = (const lean_object*)&l_Std_instToStringCancellationReason___closed__0_value;
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_normal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_normal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_select_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_select_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CancellationToken_Consumer_resolve___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_resolve___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_CancellationToken_Consumer_resolve___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CancellationToken_Consumer_resolve___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_CancellationToken_Consumer_resolve___closed__0 = (const lean_object*)&l_Std_CancellationToken_Consumer_resolve___closed__0_value;
LEAN_EXPORT uint8_t l_Std_CancellationToken_Consumer_resolve(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_resolve___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_CancellationToken_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CancellationToken_new___closed__0;
static lean_once_cell_t l_Std_CancellationToken_new___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CancellationToken_new___closed__1;
LEAN_EXPORT lean_object* l_Std_CancellationToken_new();
LEAN_EXPORT lean_object* l_Std_CancellationToken_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_CancellationToken_isCancelled___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_isCancelled___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_CancellationToken_isCancelled___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CancellationToken_isCancelled___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CancellationToken_isCancelled___closed__0 = (const lean_object*)&l_Std_CancellationToken_isCancelled___closed__0_value;
LEAN_EXPORT uint8_t l_Std_CancellationToken_isCancelled(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_isCancelled___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_CancellationToken_getCancellationReason___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CancellationToken_getCancellationReason___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CancellationToken_getCancellationReason___closed__0 = (const lean_object*)&l_Std_CancellationToken_getCancellationReason___closed__0_value;
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_CancellationToken_wait___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "cancellation token dropped"};
static const lean_object* l_Std_CancellationToken_wait___lam__0___closed__0 = (const lean_object*)&l_Std_CancellationToken_wait___lam__0___closed__0_value;
static lean_once_cell_t l_Std_CancellationToken_wait___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CancellationToken_wait___lam__0___closed__1;
static lean_once_cell_t l_Std_CancellationToken_wait___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CancellationToken_wait___lam__0___closed__2;
static lean_once_cell_t l_Std_CancellationToken_wait___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CancellationToken_wait___lam__0___closed__3;
static lean_once_cell_t l_Std_CancellationToken_wait___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_CancellationToken_wait___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_CancellationToken_wait___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CancellationToken_wait___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CancellationToken_wait___closed__0 = (const lean_object*)&l_Std_CancellationToken_wait___closed__0_value;
static const lean_closure_object l_Std_CancellationToken_wait___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CancellationToken_wait___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_CancellationToken_wait___closed__0_value)} };
static const lean_object* l_Std_CancellationToken_wait___closed__1 = (const lean_object*)&l_Std_CancellationToken_wait___closed__1_value;
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__1(lean_object*, lean_object*);
static const lean_ctor_object l_Std_CancellationToken_selector___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0_value)}};
static const lean_object* l_Std_CancellationToken_selector___lam__2___closed__0 = (const lean_object*)&l_Std_CancellationToken_selector___lam__2___closed__0_value;
static const lean_closure_object l_Std_CancellationToken_selector___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CancellationToken_selector___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_CancellationToken_selector___lam__2___closed__1 = (const lean_object*)&l_Std_CancellationToken_selector___lam__2___closed__1_value;
static const lean_closure_object l_Std_CancellationToken_selector___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CancellationToken_selector___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_CancellationToken_selector___lam__2___closed__2 = (const lean_object*)&l_Std_CancellationToken_selector___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_CancellationToken_selector___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_CancellationToken_selector___lam__5___closed__0 = (const lean_object*)&l_Std_CancellationToken_selector___lam__5___closed__0_value;
static const lean_ctor_object l_Std_CancellationToken_selector___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_CancellationToken_selector___lam__5___closed__0_value)}};
static const lean_object* l_Std_CancellationToken_selector___lam__5___closed__1 = (const lean_object*)&l_Std_CancellationToken_selector___lam__5___closed__1_value;
static const lean_ctor_object l_Std_CancellationToken_selector___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_CancellationToken_selector___lam__5___closed__2 = (const lean_object*)&l_Std_CancellationToken_selector___lam__5___closed__2_value;
static const lean_ctor_object l_Std_CancellationToken_selector___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_CancellationToken_selector___lam__5___closed__2_value)}};
static const lean_object* l_Std_CancellationToken_selector___lam__5___closed__3 = (const lean_object*)&l_Std_CancellationToken_selector___lam__5___closed__3_value;
static const lean_ctor_object l_Std_CancellationToken_selector___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_CancellationToken_selector___lam__5___closed__3_value)}};
static const lean_object* l_Std_CancellationToken_selector___lam__5___closed__4 = (const lean_object*)&l_Std_CancellationToken_selector___lam__5___closed__4_value;
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0_value)}};
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1_value;
static const lean_closure_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0 = (const lean_object*)&l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__9(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__9___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_CancellationToken_selector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CancellationToken_selector___lam__5___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CancellationToken_selector___closed__0 = (const lean_object*)&l_Std_CancellationToken_selector___closed__0_value;
static const lean_closure_object l_Std_CancellationToken_selector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_CancellationToken_selector___lam__9___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_CancellationToken_selector___closed__1 = (const lean_object*)&l_Std_CancellationToken_selector___closed__1_value;
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_CancellationReason_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 3)
{
lean_object* v_msg_7_; lean_object* v___x_8_; 
v_msg_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_msg_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_msg_7_);
return v___x_8_;
}
else
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_CancellationReason_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_CancellationReason_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_deadline_elim___redArg(lean_object* v_t_21_, lean_object* v_deadline_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_CancellationReason_ctorElim___redArg(v_t_21_, v_deadline_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_deadline_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_deadline_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_CancellationReason_ctorElim___redArg(v_t_25_, v_deadline_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_shutdown_elim___redArg(lean_object* v_t_29_, lean_object* v_shutdown_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_CancellationReason_ctorElim___redArg(v_t_29_, v_shutdown_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_shutdown_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_shutdown_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_CancellationReason_ctorElim___redArg(v_t_33_, v_shutdown_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_cancel_elim___redArg(lean_object* v_t_37_, lean_object* v_cancel_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_CancellationReason_ctorElim___redArg(v_t_37_, v_cancel_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_cancel_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_cancel_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_CancellationReason_ctorElim___redArg(v_t_41_, v_cancel_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_custom_elim___redArg(lean_object* v_t_45_, lean_object* v_custom_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_CancellationReason_ctorElim___redArg(v_t_45_, v_custom_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_custom_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_custom_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Std_CancellationReason_ctorElim___redArg(v_t_49_, v_custom_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Std_instReprCancellationReason_repr___closed__6(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(2u);
v___x_63_ = lean_nat_to_int(v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l_Std_instReprCancellationReason_repr___closed__7(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_to_int(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_instReprCancellationReason_repr(lean_object* v_x_72_, lean_object* v_prec_73_){
_start:
{
lean_object* v___y_75_; lean_object* v___y_82_; lean_object* v___y_89_; 
switch(lean_obj_tag(v_x_72_))
{
case 0:
{
lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(1024u);
v___x_96_ = lean_nat_dec_le(v___x_95_, v_prec_73_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__6, &l_Std_instReprCancellationReason_repr___closed__6_once, _init_l_Std_instReprCancellationReason_repr___closed__6);
v___y_89_ = v___x_97_;
goto v___jp_88_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__7, &l_Std_instReprCancellationReason_repr___closed__7_once, _init_l_Std_instReprCancellationReason_repr___closed__7);
v___y_89_ = v___x_98_;
goto v___jp_88_;
}
}
case 1:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_unsigned_to_nat(1024u);
v___x_100_ = lean_nat_dec_le(v___x_99_, v_prec_73_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__6, &l_Std_instReprCancellationReason_repr___closed__6_once, _init_l_Std_instReprCancellationReason_repr___closed__6);
v___y_82_ = v___x_101_;
goto v___jp_81_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__7, &l_Std_instReprCancellationReason_repr___closed__7_once, _init_l_Std_instReprCancellationReason_repr___closed__7);
v___y_82_ = v___x_102_;
goto v___jp_81_;
}
}
case 2:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1024u);
v___x_104_ = lean_nat_dec_le(v___x_103_, v_prec_73_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__6, &l_Std_instReprCancellationReason_repr___closed__6_once, _init_l_Std_instReprCancellationReason_repr___closed__6);
v___y_75_ = v___x_105_;
goto v___jp_74_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__7, &l_Std_instReprCancellationReason_repr___closed__7_once, _init_l_Std_instReprCancellationReason_repr___closed__7);
v___y_75_ = v___x_106_;
goto v___jp_74_;
}
}
default: 
{
lean_object* v_msg_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_127_; 
v_msg_107_ = lean_ctor_get(v_x_72_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_x_72_);
if (v_isSharedCheck_127_ == 0)
{
v___x_109_ = v_x_72_;
v_isShared_110_ = v_isSharedCheck_127_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_msg_107_);
lean_dec(v_x_72_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_127_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___y_112_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1024u);
v___x_124_ = lean_nat_dec_le(v___x_123_, v_prec_73_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__6, &l_Std_instReprCancellationReason_repr___closed__6_once, _init_l_Std_instReprCancellationReason_repr___closed__6);
v___y_112_ = v___x_125_;
goto v___jp_111_;
}
else
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__7, &l_Std_instReprCancellationReason_repr___closed__7_once, _init_l_Std_instReprCancellationReason_repr___closed__7);
v___y_112_ = v___x_126_;
goto v___jp_111_;
}
v___jp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_113_ = ((lean_object*)(l_Std_instReprCancellationReason_repr___closed__10));
v___x_114_ = l_String_quote(v_msg_107_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_114_);
v___x_116_ = v___x_109_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_122_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_113_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
lean_inc(v___y_112_);
v___x_118_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_118_, 0, v___y_112_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = 0;
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_119_);
v___x_121_ = l_Repr_addAppParen(v___x_120_, v_prec_73_);
return v___x_121_;
}
}
}
}
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; uint8_t v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_76_ = ((lean_object*)(l_Std_instReprCancellationReason_repr___closed__1));
lean_inc(v___y_75_);
v___x_77_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_77_, 0, v___y_75_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = 0;
v___x_79_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*1, v___x_78_);
v___x_80_ = l_Repr_addAppParen(v___x_79_, v_prec_73_);
return v___x_80_;
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_83_ = ((lean_object*)(l_Std_instReprCancellationReason_repr___closed__3));
lean_inc(v___y_82_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___y_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
v___x_87_ = l_Repr_addAppParen(v___x_86_, v_prec_73_);
return v___x_87_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = ((lean_object*)(l_Std_instReprCancellationReason_repr___closed__5));
lean_inc(v___y_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___y_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_92_);
v___x_94_ = l_Repr_addAppParen(v___x_93_, v_prec_73_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Std_instReprCancellationReason_repr___boxed(lean_object* v_x_128_, lean_object* v_prec_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_instReprCancellationReason_repr(v_x_128_, v_prec_129_);
lean_dec(v_prec_129_);
return v_res_130_;
}
}
uint8_t l_Std_instBEqCancellationReason_beq(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
switch(lean_obj_tag(v_x_133_))
{
case 0:
{
if (lean_obj_tag(v_x_134_) == 0)
{
uint8_t v___x_135_; 
v___x_135_ = 1;
return v___x_135_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
}
case 1:
{
if (lean_obj_tag(v_x_134_) == 1)
{
uint8_t v___x_137_; 
v___x_137_ = 1;
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = 0;
return v___x_138_;
}
}
case 2:
{
if (lean_obj_tag(v_x_134_) == 2)
{
uint8_t v___x_139_; 
v___x_139_ = 1;
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = 0;
return v___x_140_;
}
}
default: 
{
if (lean_obj_tag(v_x_134_) == 3)
{
lean_object* v_msg_141_; lean_object* v_msg_142_; uint8_t v___x_143_; 
v_msg_141_ = lean_ctor_get(v_x_133_, 0);
v_msg_142_ = lean_ctor_get(v_x_134_, 0);
v___x_143_ = lean_string_dec_eq(v_msg_141_, v_msg_142_);
return v___x_143_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT void l_Std_instBEqCancellationReason_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_133_ = stack[0].m_obj;
lean_object* v_x_134_ = stack[1].m_obj;
uint8_t v_res_145_;
v_res_145_ = l_Std_instBEqCancellationReason_beq(v_x_133_, v_x_134_);
stack->m_num = v_res_145_;
}
LEAN_EXPORT lean_object* l_Std_instBEqCancellationReason_beq___boxed(lean_object* v_x_146_, lean_object* v_x_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Std_instBEqCancellationReason_beq(v_x_146_, v_x_147_);
lean_dec(v_x_147_);
lean_dec(v_x_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStringCancellationReason___lam__0(lean_object* v_x_157_){
_start:
{
switch(lean_obj_tag(v_x_157_))
{
case 0:
{
lean_object* v___x_158_; 
v___x_158_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__0));
return v___x_158_;
}
case 1:
{
lean_object* v___x_159_; 
v___x_159_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__1));
return v___x_159_;
}
case 2:
{
lean_object* v___x_160_; 
v___x_160_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__2));
return v___x_160_;
}
default: 
{
lean_object* v_msg_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_msg_161_ = lean_ctor_get(v_x_157_, 0);
v___x_162_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__3));
v___x_163_ = lean_string_append(v___x_162_, v_msg_161_);
v___x_164_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__4));
v___x_165_ = lean_string_append(v___x_163_, v___x_164_);
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instToStringCancellationReason___lam__0___boxed(lean_object* v_x_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Std_instToStringCancellationReason___lam__0(v_x_166_);
lean_dec(v_x_166_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorIdx___impl(lean_object* v_x_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_tag_nat(v_x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorIdx___impl___boxed(lean_object* v_x_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_CancellationToken_Consumer_ctorIdx___impl(v_x_172_);
lean_dec_ref(v_x_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim___redArg(lean_object* v_t_174_, lean_object* v_k_175_){
_start:
{
if (lean_obj_tag(v_t_174_) == 0)
{
lean_object* v_promise_176_; lean_object* v___x_177_; 
v_promise_176_ = lean_ctor_get(v_t_174_, 0);
lean_inc(v_promise_176_);
lean_dec_ref_known(v_t_174_, 1);
v___x_177_ = lean_apply_1(v_k_175_, v_promise_176_);
return v___x_177_;
}
else
{
lean_object* v_finished_178_; lean_object* v___x_179_; 
v_finished_178_ = lean_ctor_get(v_t_174_, 0);
lean_inc_ref(v_finished_178_);
lean_dec_ref_known(v_t_174_, 1);
v___x_179_ = lean_apply_1(v_k_175_, v_finished_178_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim(lean_object* v_motive_180_, lean_object* v_ctorIdx_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_k_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_182_, v_k_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim___boxed(lean_object* v_motive_186_, lean_object* v_ctorIdx_187_, lean_object* v_t_188_, lean_object* v_h_189_, lean_object* v_k_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_CancellationToken_Consumer_ctorElim(v_motive_186_, v_ctorIdx_187_, v_t_188_, v_h_189_, v_k_190_);
lean_dec(v_ctorIdx_187_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_normal_elim___redArg(lean_object* v_t_192_, lean_object* v_normal_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_192_, v_normal_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_normal_elim(lean_object* v_motive_195_, lean_object* v_t_196_, lean_object* v_h_197_, lean_object* v_normal_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_196_, v_normal_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_select_elim___redArg(lean_object* v_t_200_, lean_object* v_select_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_200_, v_select_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_select_elim(lean_object* v_motive_203_, lean_object* v_t_204_, lean_object* v_h_205_, lean_object* v_select_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_204_, v_select_206_);
return v___x_207_;
}
}
uint8_t l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(lean_object* v_w_210_, lean_object* v_lose_211_){
_start:
{
lean_object* v_finished_213_; lean_object* v_promise_214_; lean_object* v___x_215_; uint8_t v___y_217_; uint8_t v___x_225_; 
v_finished_213_ = lean_ctor_get(v_w_210_, 0);
v_promise_214_ = lean_ctor_get(v_w_210_, 1);
v___x_215_ = lean_st_ref_take(v_finished_213_);
v___x_225_ = lean_unbox(v___x_215_);
lean_dec(v___x_215_);
if (v___x_225_ == 0)
{
uint8_t v___x_226_; 
v___x_226_ = 1;
v___y_217_ = v___x_226_;
goto v___jp_216_;
}
else
{
uint8_t v___x_227_; 
v___x_227_ = 0;
v___y_217_ = v___x_227_;
goto v___jp_216_;
}
v___jp_216_:
{
uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = 1;
v___x_219_ = lean_box(v___x_218_);
v___x_220_ = lean_st_ref_put(v_finished_213_, v___x_219_);
if (v___y_217_ == 0)
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_apply_1(v_lose_211_, lean_box(0));
v___x_222_ = lean_unbox(v___x_221_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec_ref(v_lose_211_);
v___x_223_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_224_ = lean_io_promise_resolve(v___x_223_, v_promise_214_);
return v___y_217_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_210_ = stack[0].m_obj;
lean_object* v_lose_211_ = stack[1].m_obj;
uint8_t v_res_228_;
v_res_228_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(v_w_210_, v_lose_211_);
stack->m_num = v_res_228_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___boxed(lean_object* v_w_229_, lean_object* v_lose_230_, lean_object* v___y_231_){
_start:
{
uint8_t v_res_232_; lean_object* v_r_233_; 
v_res_232_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(v_w_229_, v_lose_230_);
lean_dec_ref(v_w_229_);
v_r_233_ = lean_box(v_res_232_);
return v_r_233_;
}
}
uint8_t l_Std_CancellationToken_Consumer_resolve___lam__0(uint8_t v___x_234_){
_start:
{
return v___x_234_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_Consumer_resolve___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_234_ = stack[0].m_num;
uint8_t v_res_236_;
v_res_236_ = l_Std_CancellationToken_Consumer_resolve___lam__0(v___x_234_);
stack->m_num = v_res_236_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_resolve___lam__0___boxed(lean_object* v___x_237_, lean_object* v___y_238_){
_start:
{
uint8_t v___x_397__boxed_239_; uint8_t v_res_240_; lean_object* v_r_241_; 
v___x_397__boxed_239_ = lean_unbox(v___x_237_);
v_res_240_ = l_Std_CancellationToken_Consumer_resolve___lam__0(v___x_397__boxed_239_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
uint8_t l_Std_CancellationToken_Consumer_resolve(lean_object* v_c_245_){
_start:
{
if (lean_obj_tag(v_c_245_) == 0)
{
lean_object* v_promise_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v_promise_247_ = lean_ctor_get(v_c_245_, 0);
v___x_248_ = lean_box(0);
v___x_249_ = lean_io_promise_resolve(v___x_248_, v_promise_247_);
v___x_250_ = 1;
return v___x_250_;
}
else
{
lean_object* v_finished_251_; lean_object* v_lose_252_; uint8_t v___x_253_; 
v_finished_251_ = lean_ctor_get(v_c_245_, 0);
v_lose_252_ = ((lean_object*)(l_Std_CancellationToken_Consumer_resolve___closed__0));
v___x_253_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(v_finished_251_, v_lose_252_);
return v___x_253_;
}
}
}
LEAN_EXPORT void l_Std_CancellationToken_Consumer_resolve_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_245_ = stack[0].m_obj;
uint8_t v_res_254_;
v_res_254_ = l_Std_CancellationToken_Consumer_resolve(v_c_245_);
stack->m_num = v_res_254_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_resolve___boxed(lean_object* v_c_255_, lean_object* v_a_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Std_CancellationToken_Consumer_resolve(v_c_255_);
lean_dec_ref(v_c_255_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
static lean_object* _init_l_Std_CancellationToken_new___closed__0(void){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Std_Queue_empty___redArg();
return v___x_259_;
}
}
static lean_object* _init_l_Std_CancellationToken_new___closed__1(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_obj_once(&l_Std_CancellationToken_new___closed__0, &l_Std_CancellationToken_new___closed__0_once, _init_l_Std_CancellationToken_new___closed__0);
v___x_261_ = lean_box(0);
v___x_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v___x_260_);
return v___x_262_;
}
}
lean_object* l_Std_CancellationToken_new(){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_obj_once(&l_Std_CancellationToken_new___closed__1, &l_Std_CancellationToken_new___closed__1_once, _init_l_Std_CancellationToken_new___closed__1);
v___x_265_ = l_Std_Mutex_new___redArg(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_266_;
v_res_266_ = l_Std_CancellationToken_new();
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_new___boxed(lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Std_CancellationToken_new();
return v_res_268_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(lean_object* v_mutex_269_, lean_object* v_k_270_){
_start:
{
lean_object* v_ref_272_; lean_object* v_mutex_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_ref_272_ = lean_ctor_get(v_mutex_269_, 0);
lean_inc(v_ref_272_);
v_mutex_273_ = lean_ctor_get(v_mutex_269_, 1);
lean_inc(v_mutex_273_);
lean_dec_ref(v_mutex_269_);
v___x_274_ = lean_io_basemutex_lock(v_mutex_273_);
v___x_275_ = lean_apply_2(v_k_270_, v_ref_272_, lean_box(0));
v___x_276_ = lean_io_basemutex_unlock(v_mutex_273_);
lean_dec(v_mutex_273_);
return v___x_275_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_269_ = stack[0].m_obj;
lean_object* v_k_270_ = stack[1].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_mutex_269_, v_k_270_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg___boxed(lean_object* v_mutex_278_, lean_object* v_k_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_mutex_278_, v_k_279_);
return v_res_281_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_, lean_object* v_mutex_284_, lean_object* v_k_285_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_mutex_284_, v_k_285_);
return v___x_287_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_284_ = stack[2].m_obj;
lean_object* v_k_285_ = stack[3].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(lean_box(0), lean_box(0), v_mutex_284_, v_k_285_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___boxed(lean_object* v_00_u03b1_289_, lean_object* v_00_u03b2_290_, lean_object* v_mutex_291_, lean_object* v_k_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(v_00_u03b1_289_, v_00_u03b2_290_, v_mutex_291_, v_k_292_);
return v_res_294_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; 
lean_inc_ref(v_a_295_);
v___x_297_ = l_Std_Queue_dequeue_x3f___redArg(v_a_295_);
if (lean_obj_tag(v___x_297_) == 1)
{
lean_object* v_val_298_; lean_object* v_fst_299_; lean_object* v_snd_300_; uint8_t v___x_301_; 
lean_dec_ref(v_a_295_);
v_val_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_val_298_);
lean_dec_ref_known(v___x_297_, 1);
v_fst_299_ = lean_ctor_get(v_val_298_, 0);
lean_inc(v_fst_299_);
v_snd_300_ = lean_ctor_get(v_val_298_, 1);
lean_inc(v_snd_300_);
lean_dec(v_val_298_);
v___x_301_ = l_Std_CancellationToken_Consumer_resolve(v_fst_299_);
lean_dec(v_fst_299_);
v_a_295_ = v_snd_300_;
goto _start;
}
else
{
lean_dec(v___x_297_);
return v_a_295_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_295_ = stack[0].m_obj;
lean_object* v_res_303_;
v_res_303_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_295_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg___boxed(lean_object* v_a_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_304_);
return v_res_306_;
}
}
lean_object* l_Std_CancellationToken_cancel___lam__0(lean_object* v_reason_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; lean_object* v_reason_311_; 
v___x_310_ = lean_st_ref_get(v___y_308_);
v_reason_311_ = lean_ctor_get(v___x_310_, 0);
if (lean_obj_tag(v_reason_311_) == 0)
{
lean_object* v_consumers_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_324_; 
v_consumers_312_ = lean_ctor_get(v___x_310_, 1);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v___x_310_, 0);
lean_dec(v_unused_325_);
v___x_314_ = v___x_310_;
v_isShared_315_ = v_isSharedCheck_324_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_consumers_312_);
lean_dec(v___x_310_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_324_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_st_319_; 
v___x_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_316_, 0, v_reason_307_);
v___x_317_ = lean_obj_once(&l_Std_CancellationToken_new___closed__0, &l_Std_CancellationToken_new___closed__0_once, _init_l_Std_CancellationToken_new___closed__0);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_317_);
lean_ctor_set(v___x_314_, 0, v___x_316_);
v_st_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_317_);
v_st_319_ = v_reuseFailAlloc_323_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_consumers_312_);
lean_dec_ref(v___x_320_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_st_ref_swap(v___y_308_, v_st_319_);
lean_dec(v___x_322_);
return v___x_321_;
}
}
}
else
{
lean_object* v___x_326_; 
lean_dec(v___x_310_);
lean_dec(v_reason_307_);
v___x_326_ = lean_box(0);
return v___x_326_;
}
}
}
LEAN_EXPORT void l_Std_CancellationToken_cancel___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_reason_307_ = stack[0].m_obj;
lean_object* v___y_308_ = stack[1].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Std_CancellationToken_cancel___lam__0(v_reason_307_, v___y_308_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___lam__0___boxed(lean_object* v_reason_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_CancellationToken_cancel___lam__0(v_reason_328_, v___y_329_);
lean_dec(v___y_329_);
return v_res_331_;
}
}
lean_object* l_Std_CancellationToken_cancel(lean_object* v_x_332_, lean_object* v_reason_333_){
_start:
{
lean_object* v___f_335_; lean_object* v___x_336_; 
v___f_335_ = lean_alloc_closure((void*)(l_Std_CancellationToken_cancel___lam__0___boxed), 3, 1);
lean_closure_set(v___f_335_, 0, v_reason_333_);
v___x_336_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_332_, v___f_335_);
return v___x_336_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_cancel_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_332_ = stack[0].m_obj;
lean_object* v_reason_333_ = stack[1].m_obj;
lean_object* v_res_337_;
v_res_337_ = l_Std_CancellationToken_cancel(v_x_332_, v_reason_333_);
stack->m_obj
 = v_res_337_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___boxed(lean_object* v_x_338_, lean_object* v_reason_339_, lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_CancellationToken_cancel(v_x_338_, v_reason_339_);
return v_res_341_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0(lean_object* v_inst_342_, lean_object* v_a_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_343_);
return v___x_346_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_343_ = stack[1].m_obj;
lean_object* v___y_344_ = stack[2].m_obj;
lean_object* v_res_347_;
v_res_347_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0(lean_box(0), v_a_343_, v___y_344_);
stack->m_obj
 = v_res_347_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___boxed(lean_object* v_inst_348_, lean_object* v_a_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0(v_inst_348_, v_a_349_, v___y_350_);
lean_dec(v___y_350_);
return v_res_352_;
}
}
uint8_t l_Std_CancellationToken_isCancelled___lam__0(lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v_reason_356_; 
v___x_355_ = lean_st_ref_get(v___y_353_);
v_reason_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_reason_356_);
lean_dec(v___x_355_);
if (lean_obj_tag(v_reason_356_) == 0)
{
uint8_t v___x_357_; 
v___x_357_ = 0;
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
lean_dec_ref_known(v_reason_356_, 1);
v___x_358_ = 1;
return v___x_358_;
}
}
}
LEAN_EXPORT void l_Std_CancellationToken_isCancelled___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_353_ = stack[0].m_obj;
uint8_t v_res_359_;
v_res_359_ = l_Std_CancellationToken_isCancelled___lam__0(v___y_353_);
stack->m_num = v_res_359_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_isCancelled___lam__0___boxed(lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Std_CancellationToken_isCancelled___lam__0(v___y_360_);
lean_dec(v___y_360_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
uint8_t l_Std_CancellationToken_isCancelled(lean_object* v_x_365_){
_start:
{
lean_object* v___f_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v___f_367_ = ((lean_object*)(l_Std_CancellationToken_isCancelled___closed__0));
v___x_368_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_365_, v___f_367_);
v___x_369_ = lean_unbox(v___x_368_);
lean_dec(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_isCancelled_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_365_ = stack[0].m_obj;
uint8_t v_res_370_;
v_res_370_ = l_Std_CancellationToken_isCancelled(v_x_365_);
stack->m_num = v_res_370_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_isCancelled___boxed(lean_object* v_x_371_, lean_object* v_a_372_){
_start:
{
uint8_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Std_CancellationToken_isCancelled(v_x_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
lean_object* l_Std_CancellationToken_getCancellationReason___lam__0(lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; lean_object* v_reason_378_; 
v___x_377_ = lean_st_ref_get(v___y_375_);
v_reason_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_reason_378_);
lean_dec(v___x_377_);
return v_reason_378_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_getCancellationReason___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_375_ = stack[0].m_obj;
lean_object* v_res_379_;
v_res_379_ = l_Std_CancellationToken_getCancellationReason___lam__0(v___y_375_);
stack->m_obj
 = v_res_379_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___lam__0___boxed(lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_CancellationToken_getCancellationReason___lam__0(v___y_380_);
lean_dec(v___y_380_);
return v_res_382_;
}
}
lean_object* l_Std_CancellationToken_getCancellationReason(lean_object* v_x_384_){
_start:
{
lean_object* v___f_386_; lean_object* v___x_387_; 
v___f_386_ = ((lean_object*)(l_Std_CancellationToken_getCancellationReason___closed__0));
v___x_387_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_384_, v___f_386_);
return v___x_387_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_getCancellationReason_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_384_ = stack[0].m_obj;
lean_object* v_res_388_;
v_res_388_ = l_Std_CancellationToken_getCancellationReason(v_x_384_);
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___boxed(lean_object* v_x_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_CancellationToken_getCancellationReason(v_x_389_);
return v_res_391_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(lean_object* v_mutex_392_, lean_object* v_k_393_){
_start:
{
lean_object* v_ref_395_; lean_object* v_mutex_396_; lean_object* v___x_397_; lean_object* v_r_398_; 
v_ref_395_ = lean_ctor_get(v_mutex_392_, 0);
lean_inc(v_ref_395_);
v_mutex_396_ = lean_ctor_get(v_mutex_392_, 1);
lean_inc(v_mutex_396_);
lean_dec_ref(v_mutex_392_);
v___x_397_ = lean_io_basemutex_lock(v_mutex_396_);
v_r_398_ = lean_apply_2(v_k_393_, v_ref_395_, lean_box(0));
if (lean_obj_tag(v_r_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_407_; 
v_a_399_ = lean_ctor_get(v_r_398_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_r_398_);
if (v_isSharedCheck_407_ == 0)
{
v___x_401_ = v_r_398_;
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v_r_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_io_basemutex_unlock(v_mutex_396_);
lean_dec(v_mutex_396_);
if (v_isShared_402_ == 0)
{
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_399_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_416_; 
v_a_408_ = lean_ctor_get(v_r_398_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v_r_398_);
if (v_isSharedCheck_416_ == 0)
{
v___x_410_ = v_r_398_;
v_isShared_411_ = v_isSharedCheck_416_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v_r_398_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_416_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_412_ = lean_io_basemutex_unlock(v_mutex_396_);
lean_dec(v_mutex_396_);
if (v_isShared_411_ == 0)
{
v___x_414_ = v___x_410_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_408_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_392_ = stack[0].m_obj;
lean_object* v_k_393_ = stack[1].m_obj;
lean_object* v_res_417_;
v_res_417_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_mutex_392_, v_k_393_);
stack->m_obj
 = v_res_417_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg___boxed(lean_object* v_mutex_418_, lean_object* v_k_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_mutex_418_, v_k_419_);
return v_res_421_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(lean_object* v_00_u03b1_422_, lean_object* v_00_u03b2_423_, lean_object* v_mutex_424_, lean_object* v_k_425_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_mutex_424_, v_k_425_);
return v___x_427_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_424_ = stack[2].m_obj;
lean_object* v_k_425_ = stack[3].m_obj;
lean_object* v_res_428_;
v_res_428_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(lean_box(0), lean_box(0), v_mutex_424_, v_k_425_);
stack->m_obj
 = v_res_428_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___boxed(lean_object* v_00_u03b1_429_, lean_object* v_00_u03b2_430_, lean_object* v_mutex_431_, lean_object* v_k_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(v_00_u03b1_429_, v_00_u03b2_430_, v_mutex_431_, v_k_432_);
return v_res_434_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__1(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l_Std_CancellationToken_wait___lam__0___closed__0));
v___x_437_ = lean_mk_io_user_error(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__2(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__1, &l_Std_CancellationToken_wait___lam__0___closed__1_once, _init_l_Std_CancellationToken_wait___lam__0___closed__1);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__3(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__2, &l_Std_CancellationToken_wait___lam__0___closed__2_once, _init_l_Std_CancellationToken_wait___lam__0___closed__2);
v___x_441_ = lean_task_pure(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__4(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_443_ = lean_task_pure(v___x_442_);
return v___x_443_;
}
}
lean_object* l_Std_CancellationToken_wait___lam__0(lean_object* v_a_444_){
_start:
{
if (lean_obj_tag(v_a_444_) == 0)
{
lean_object* v___x_446_; 
v___x_446_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__3, &l_Std_CancellationToken_wait___lam__0___closed__3_once, _init_l_Std_CancellationToken_wait___lam__0___closed__3);
return v___x_446_;
}
else
{
lean_object* v___x_447_; 
v___x_447_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__4, &l_Std_CancellationToken_wait___lam__0___closed__4_once, _init_l_Std_CancellationToken_wait___lam__0___closed__4);
return v___x_447_;
}
}
}
LEAN_EXPORT void l_Std_CancellationToken_wait___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_444_ = stack[0].m_obj;
lean_object* v_res_448_;
v_res_448_ = l_Std_CancellationToken_wait___lam__0(v_a_444_);
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__0___boxed(lean_object* v_a_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_CancellationToken_wait___lam__0(v_a_449_);
lean_dec(v_a_449_);
return v_res_451_;
}
}
lean_object* l_Std_CancellationToken_wait___lam__1(lean_object* v___f_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; lean_object* v_reason_456_; 
v___x_455_ = lean_st_ref_get(v___y_453_);
v_reason_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_reason_456_);
lean_dec(v___x_455_);
if (lean_obj_tag(v_reason_456_) == 0)
{
uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v_reason_460_; lean_object* v_consumers_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_475_; 
v___x_457_ = 0;
v___x_458_ = lean_io_promise_new();
v___x_459_ = lean_st_ref_take(v___y_453_);
v_reason_460_ = lean_ctor_get(v___x_459_, 0);
v_consumers_461_ = lean_ctor_get(v___x_459_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_475_ == 0)
{
v___x_463_ = v___x_459_;
v_isShared_464_ = v_isSharedCheck_475_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_consumers_461_);
lean_inc(v_reason_460_);
lean_dec(v___x_459_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_475_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
lean_inc(v___x_458_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_458_);
v___x_466_ = l_Std_Queue_enqueue___redArg(v___x_465_, v_consumers_461_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_466_);
v___x_468_ = v___x_463_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_reason_460_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_466_);
v___x_468_ = v_reuseFailAlloc_474_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_469_ = lean_st_ref_put(v___y_453_, v___x_468_);
v___x_470_ = lean_io_promise_result_opt(v___x_458_);
lean_dec(v___x_458_);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_io_bind_task(v___x_470_, v___f_452_, v___x_471_, v___x_457_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
else
{
lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_483_; 
lean_dec_ref(v___f_452_);
v_isSharedCheck_483_ = !lean_is_exclusive(v_reason_456_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_reason_456_, 0);
lean_dec(v_unused_484_);
v___x_477_ = v_reason_456_;
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
else
{
lean_dec(v_reason_456_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_483_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_479_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__4, &l_Std_CancellationToken_wait___lam__0___closed__4_once, _init_l_Std_CancellationToken_wait___lam__0___closed__4);
if (v_isShared_478_ == 0)
{
lean_ctor_set_tag(v___x_477_, 0);
lean_ctor_set(v___x_477_, 0, v___x_479_);
v___x_481_ = v___x_477_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
LEAN_EXPORT void l_Std_CancellationToken_wait___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_452_ = stack[0].m_obj;
lean_object* v___y_453_ = stack[1].m_obj;
lean_object* v_res_485_;
v_res_485_ = l_Std_CancellationToken_wait___lam__1(v___f_452_, v___y_453_);
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__1___boxed(lean_object* v___f_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_CancellationToken_wait___lam__1(v___f_486_, v___y_487_);
lean_dec(v___y_487_);
return v_res_489_;
}
}
lean_object* l_Std_CancellationToken_wait(lean_object* v_x_493_){
_start:
{
lean_object* v___f_495_; lean_object* v___x_496_; 
v___f_495_ = ((lean_object*)(l_Std_CancellationToken_wait___closed__1));
v___x_496_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_x_493_, v___f_495_);
return v___x_496_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_493_ = stack[0].m_obj;
lean_object* v_res_497_;
v_res_497_ = l_Std_CancellationToken_wait(v_x_493_);
stack->m_obj
 = v_res_497_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___boxed(lean_object* v_x_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_CancellationToken_wait(v_x_498_);
return v_res_500_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(uint8_t v___x_501_, lean_object* v_x_502_){
_start:
{
if (lean_obj_tag(v_x_502_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_512_; 
v_a_504_ = lean_ctor_get(v_x_502_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_512_ == 0)
{
v___x_506_ = v_x_502_;
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v_x_502_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_512_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_511_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; 
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
}
else
{
lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_521_; 
v_isSharedCheck_521_ = !lean_is_exclusive(v_x_502_);
if (v_isSharedCheck_521_ == 0)
{
lean_object* v_unused_522_; 
v_unused_522_ = lean_ctor_get(v_x_502_, 0);
lean_dec(v_unused_522_);
v___x_514_ = v_x_502_;
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
else
{
lean_dec(v_x_502_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_521_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_518_; 
v___x_516_ = lean_box(v___x_501_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_516_);
v___x_518_ = v___x_514_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_520_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
lean_object* v___x_519_; 
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_501_ = stack[0].m_num;
lean_object* v_x_502_ = stack[1].m_obj;
lean_object* v_res_523_;
v_res_523_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(v___x_501_, v_x_502_);
stack->m_obj
 = v_res_523_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0___boxed(lean_object* v___x_524_, lean_object* v_x_525_, lean_object* v___y_526_){
_start:
{
uint8_t v___x_6594__boxed_527_; lean_object* v_res_528_; 
v___x_6594__boxed_527_ = lean_unbox(v___x_524_);
v_res_528_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(v___x_6594__boxed_527_, v_x_525_);
return v_res_528_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(lean_object* v_lose_529_, lean_object* v___y_530_, lean_object* v_promise_531_, lean_object* v___f_532_, lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_533_) == 0)
{
lean_object* v___x_535_; 
lean_dec_ref(v___f_532_);
lean_dec_ref(v_lose_529_);
v___x_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_535_, 0, v_x_533_);
return v___x_535_;
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_551_; 
v_a_536_ = lean_ctor_get(v_x_533_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_533_);
if (v_isSharedCheck_551_ == 0)
{
v___x_538_ = v_x_533_;
v_isShared_539_ = v_isSharedCheck_551_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v_x_533_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_551_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
uint8_t v___x_540_; 
v___x_540_ = lean_unbox(v_a_536_);
lean_dec(v_a_536_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
lean_del_object(v___x_538_);
lean_dec_ref(v___f_532_);
lean_inc(v___y_530_);
v___x_541_ = lean_apply_2(v_lose_529_, v___y_530_, lean_box(0));
return v___x_541_;
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
lean_dec_ref(v_lose_529_);
v___x_542_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = 0;
v___x_545_ = lean_io_promise_resolve(v___x_542_, v_promise_531_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_545_);
v___x_547_ = v___x_538_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_550_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
v___x_549_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_543_, v___x_544_, v___x_548_, v___f_532_);
return v___x_549_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_lose_529_ = stack[0].m_obj;
lean_object* v___y_530_ = stack[1].m_obj;
lean_object* v_promise_531_ = stack[2].m_obj;
lean_object* v___f_532_ = stack[3].m_obj;
lean_object* v_x_533_ = stack[4].m_obj;
lean_object* v_res_552_;
v_res_552_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(v_lose_529_, v___y_530_, v_promise_531_, v___f_532_, v_x_533_);
stack->m_obj
 = v_res_552_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed(lean_object* v_lose_553_, lean_object* v___y_554_, lean_object* v_promise_555_, lean_object* v___f_556_, lean_object* v_x_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(v_lose_553_, v___y_554_, v_promise_555_, v___f_556_, v_x_557_);
lean_dec(v_promise_555_);
lean_dec(v___y_554_);
return v_res_559_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(lean_object* v_w_563_, lean_object* v_lose_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_finished_567_; lean_object* v_promise_568_; uint8_t v___x_569_; lean_object* v___f_570_; lean_object* v___f_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; uint8_t v___y_576_; uint8_t v___x_583_; 
v_finished_567_ = lean_ctor_get(v_w_563_, 0);
lean_inc(v_finished_567_);
v_promise_568_ = lean_ctor_get(v_w_563_, 1);
lean_inc(v_promise_568_);
lean_dec_ref(v_w_563_);
v___x_569_ = 1;
v___f_570_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0));
lean_inc(v___y_565_);
v___f_571_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed), 6, 4);
lean_closure_set(v___f_571_, 0, v_lose_564_);
lean_closure_set(v___f_571_, 1, v___y_565_);
lean_closure_set(v___f_571_, 2, v_promise_568_);
lean_closure_set(v___f_571_, 3, v___f_570_);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = 0;
v___x_574_ = lean_st_ref_take(v_finished_567_);
v___x_583_ = lean_unbox(v___x_574_);
lean_dec(v___x_574_);
if (v___x_583_ == 0)
{
v___y_576_ = v___x_569_;
goto v___jp_575_;
}
else
{
v___y_576_ = v___x_573_;
goto v___jp_575_;
}
v___jp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_577_ = lean_box(v___x_569_);
v___x_578_ = lean_st_ref_put(v_finished_567_, v___x_577_);
lean_dec(v_finished_567_);
v___x_579_ = lean_box(v___y_576_);
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___x_582_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_572_, v___x_573_, v___x_581_, v___f_571_);
return v___x_582_;
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_563_ = stack[0].m_obj;
lean_object* v_lose_564_ = stack[1].m_obj;
lean_object* v___y_565_ = stack[2].m_obj;
lean_object* v_res_584_;
v_res_584_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(v_w_563_, v_lose_564_, v___y_565_);
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___boxed(lean_object* v_w_585_, lean_object* v_lose_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(v_w_585_, v_lose_586_, v___y_587_);
lean_dec(v___y_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(lean_object* v___y_590_){
_start:
{
if (lean_obj_tag(v___y_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
v_a_591_ = lean_ctor_get(v___y_590_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___y_590_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___y_590_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___y_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
v_a_599_ = lean_ctor_get(v___y_590_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___y_590_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v___y_590_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___y_590_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v_fst_603_; lean_object* v___x_605_; 
v_fst_603_ = lean_ctor_get(v_a_599_, 0);
lean_inc(v_fst_603_);
lean_dec(v_a_599_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v_fst_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_fst_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(lean_object* v_mutex_608_, lean_object* v_x_609_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_io_basemutex_unlock(v_mutex_608_);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_608_ = stack[0].m_obj;
lean_object* v_x_609_ = stack[1].m_obj;
lean_object* v_res_614_;
v_res_614_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(v_mutex_608_, v_x_609_);
stack->m_obj
 = v_res_614_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed(lean_object* v_mutex_615_, lean_object* v_x_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(v_mutex_615_, v_x_616_);
lean_dec(v_x_616_);
lean_dec(v_mutex_615_);
return v_res_618_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(lean_object* v_k_619_, lean_object* v_ref_620_, lean_object* v_x_621_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_ref_620_);
lean_dec_ref(v_k_619_);
v_a_623_ = lean_ctor_get(v_x_621_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_631_ == 0)
{
v___x_625_ = v_x_621_;
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v_x_621_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_631_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_630_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; 
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
}
else
{
lean_object* v___x_632_; 
lean_dec_ref_known(v_x_621_, 1);
v___x_632_ = lean_apply_2(v_k_619_, v_ref_620_, lean_box(0));
return v___x_632_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_619_ = stack[0].m_obj;
lean_object* v_ref_620_ = stack[1].m_obj;
lean_object* v_x_621_ = stack[2].m_obj;
lean_object* v_res_633_;
v_res_633_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(v_k_619_, v_ref_620_, v_x_621_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed(lean_object* v_k_634_, lean_object* v_ref_635_, lean_object* v_x_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(v_k_634_, v_ref_635_, v_x_636_);
return v_res_638_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(lean_object* v_mutex_639_, lean_object* v___f_640_){
_start:
{
lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = 0;
v___x_644_ = lean_io_basemutex_lock(v_mutex_639_);
v___x_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
v___x_647_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_642_, v___x_643_, v___x_646_, v___f_640_);
return v___x_647_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_639_ = stack[0].m_obj;
lean_object* v___f_640_ = stack[1].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(v_mutex_639_, v___f_640_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3___boxed(lean_object* v_mutex_649_, lean_object* v___f_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(v_mutex_649_, v___f_650_);
lean_dec(v_mutex_649_);
return v_res_652_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(lean_object* v_mutex_654_, lean_object* v_k_655_){
_start:
{
lean_object* v_ref_657_; lean_object* v_mutex_658_; lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___f_661_; lean_object* v___f_662_; lean_object* v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___y_667_; 
v_ref_657_ = lean_ctor_get(v_mutex_654_, 0);
lean_inc(v_ref_657_);
v_mutex_658_ = lean_ctor_get(v_mutex_654_, 1);
lean_inc_n(v_mutex_658_, 2);
lean_dec_ref(v_mutex_654_);
v___f_659_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0));
v___f_660_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_660_, 0, v_mutex_658_);
v___f_661_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_661_, 0, v_k_655_);
lean_closure_set(v___f_661_, 1, v_ref_657_);
v___f_662_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_662_, 0, v_mutex_658_);
lean_closure_set(v___f_662_, 1, v___f_661_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = 0;
v___x_665_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_662_, v___f_660_, v___x_663_, v___x_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_669_; 
v_a_669_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_665_, 1);
if (lean_obj_tag(v_a_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v_a_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v_a_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v_a_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v_a_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
v___y_667_ = v___x_675_;
goto v___jp_666_;
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_686_; 
v_a_678_ = lean_ctor_get(v_a_669_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v_a_669_);
if (v_isSharedCheck_686_ == 0)
{
v___x_680_ = v_a_669_;
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v_a_669_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_fst_682_; lean_object* v___x_684_; 
v_fst_682_ = lean_ctor_get(v_a_678_, 0);
lean_inc(v_fst_682_);
lean_dec(v_a_678_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v_fst_682_);
v___x_684_ = v___x_680_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_fst_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
v___y_667_ = v___x_684_;
goto v___jp_666_;
}
}
}
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_695_; 
v_a_687_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_695_ == 0)
{
v___x_689_ = v___x_665_;
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_665_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_695_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_task_map(v___f_659_, v_a_687_, v___x_663_, v___x_664_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_691_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
v___jp_666_:
{
lean_object* v___x_668_; 
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___y_667_);
return v___x_668_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_654_ = stack[0].m_obj;
lean_object* v_k_655_ = stack[1].m_obj;
lean_object* v_res_696_;
v_res_696_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_mutex_654_, v_k_655_);
stack->m_obj
 = v_res_696_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___boxed(lean_object* v_mutex_697_, lean_object* v_k_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_mutex_697_, v_k_698_);
return v_res_700_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(lean_object* v_00_u03b1_701_, lean_object* v_00_u03b2_702_, lean_object* v_mutex_703_, lean_object* v_k_704_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_mutex_703_, v_k_704_);
return v___x_706_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_703_ = stack[2].m_obj;
lean_object* v_k_704_ = stack[3].m_obj;
lean_object* v_res_707_;
v_res_707_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(lean_box(0), lean_box(0), v_mutex_703_, v_k_704_);
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed(lean_object* v_00_u03b1_708_, lean_object* v_00_u03b2_709_, lean_object* v_mutex_710_, lean_object* v_k_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(v_00_u03b1_708_, v_00_u03b2_709_, v_mutex_710_, v_k_711_);
return v_res_713_;
}
}
lean_object* l_Std_CancellationToken_selector___lam__0(uint8_t v___x_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_box(v___x_714_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_selector___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_714_ = stack[0].m_num;
lean_object* v___y_715_ = stack[1].m_obj;
lean_object* v_res_720_;
v_res_720_ = l_Std_CancellationToken_selector___lam__0(v___x_714_, v___y_715_);
stack->m_obj
 = v_res_720_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__0___boxed(lean_object* v___x_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint8_t v___x_7072__boxed_724_; lean_object* v_res_725_; 
v___x_7072__boxed_724_ = lean_unbox(v___x_721_);
v_res_725_ = l_Std_CancellationToken_selector___lam__0(v___x_7072__boxed_724_, v___y_722_);
lean_dec(v___y_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__1(lean_object* v___x_726_, lean_object* v___y_727_){
_start:
{
if (lean_obj_tag(v___y_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___y_727_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___y_727_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___y_727_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___y_727_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
v_isSharedCheck_742_ = !lean_is_exclusive(v___y_727_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___y_727_, 0);
lean_dec(v_unused_743_);
v___x_737_ = v___y_727_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_dec(v___y_727_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_726_);
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_726_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
lean_object* l_Std_CancellationToken_selector___lam__2(lean_object* v___y_751_, lean_object* v_waiter_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v_waiter_752_);
v_a_755_ = lean_ctor_get(v_x_753_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v_x_753_);
if (v_isSharedCheck_763_ == 0)
{
v___x_757_ = v_x_753_;
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v_x_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_763_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_762_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; 
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
else
{
lean_object* v_a_764_; lean_object* v_reason_765_; 
v_a_764_ = lean_ctor_get(v_x_753_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v_x_753_, 1);
v_reason_765_ = lean_ctor_get(v_a_764_, 0);
lean_inc(v_reason_765_);
lean_dec(v_a_764_);
if (lean_obj_tag(v_reason_765_) == 0)
{
lean_object* v___x_766_; lean_object* v_reason_767_; lean_object* v_consumers_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_779_; 
v___x_766_ = lean_st_ref_take(v___y_751_);
v_reason_767_ = lean_ctor_get(v___x_766_, 0);
v_consumers_768_ = lean_ctor_get(v___x_766_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_779_ == 0)
{
v___x_770_ = v___x_766_;
v_isShared_771_ = v_isSharedCheck_779_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_consumers_768_);
lean_inc(v_reason_767_);
lean_dec(v___x_766_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_779_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_772_, 0, v_waiter_752_);
v___x_773_ = l_Std_Queue_enqueue___redArg(v___x_772_, v_consumers_768_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 1, v___x_773_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_reason_767_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_778_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_st_ref_put(v___y_751_, v___x_775_);
v___x_777_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__0));
return v___x_777_;
}
}
}
else
{
lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_812_; 
v_isSharedCheck_812_ = !lean_is_exclusive(v_reason_765_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_reason_765_, 0);
lean_dec(v_unused_813_);
v___x_781_ = v_reason_765_;
v_isShared_782_ = v_isSharedCheck_812_;
goto v_resetjp_780_;
}
else
{
lean_dec(v_reason_765_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_812_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
uint8_t v___x_783_; lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___y_789_; 
v___x_783_ = 0;
v___f_784_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__1));
v___f_785_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__2));
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(v_waiter_752_, v___f_784_, v___y_751_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_793_; 
v_a_793_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_787_, 1);
if (lean_obj_tag(v_a_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_a_794_ = lean_ctor_get(v_a_793_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v_a_793_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v_a_793_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v_a_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
v___y_789_ = v___x_799_;
goto v___jp_788_;
}
}
}
else
{
lean_object* v___x_802_; 
lean_dec_ref_known(v_a_793_, 1);
v___x_802_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___y_789_ = v___x_802_;
goto v___jp_788_;
}
}
else
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_811_; 
lean_del_object(v___x_781_);
v_a_803_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_811_ == 0)
{
v___x_805_ = v___x_787_;
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_787_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_811_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_807_ = lean_task_map(v___f_785_, v_a_803_, v___x_786_, v___x_783_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_807_);
v___x_809_ = v___x_805_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
v___jp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 0);
lean_ctor_set(v___x_781_, 0, v___y_789_);
v___x_791_ = v___x_781_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___y_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_CancellationToken_selector___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_751_ = stack[0].m_obj;
lean_object* v_waiter_752_ = stack[1].m_obj;
lean_object* v_x_753_ = stack[2].m_obj;
lean_object* v_res_814_;
v_res_814_ = l_Std_CancellationToken_selector___lam__2(v___y_751_, v_waiter_752_, v_x_753_);
stack->m_obj
 = v_res_814_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__2___boxed(lean_object* v___y_815_, lean_object* v_waiter_816_, lean_object* v_x_817_, lean_object* v___y_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_CancellationToken_selector___lam__2(v___y_815_, v_waiter_816_, v_x_817_);
lean_dec(v___y_815_);
return v_res_819_;
}
}
lean_object* l_Std_CancellationToken_selector___lam__3(lean_object* v_waiter_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___f_823_; lean_object* v___x_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_inc(v___y_821_);
v___f_823_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__2___boxed), 4, 2);
lean_closure_set(v___f_823_, 0, v___y_821_);
lean_closure_set(v___f_823_, 1, v_waiter_820_);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = 0;
v___x_826_ = lean_st_ref_get(v___y_821_);
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
v___x_829_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_824_, v___x_825_, v___x_828_, v___f_823_);
return v___x_829_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_selector___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_820_ = stack[0].m_obj;
lean_object* v___y_821_ = stack[1].m_obj;
lean_object* v_res_830_;
v_res_830_ = l_Std_CancellationToken_selector___lam__3(v_waiter_820_, v___y_821_);
stack->m_obj
 = v_res_830_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__3___boxed(lean_object* v_waiter_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_CancellationToken_selector___lam__3(v_waiter_831_, v___y_832_);
lean_dec(v___y_832_);
return v_res_834_;
}
}
lean_object* l_Std_CancellationToken_selector___lam__4(lean_object* v_token_835_, lean_object* v_waiter_836_){
_start:
{
lean_object* v___f_838_; lean_object* v___x_839_; 
v___f_838_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_838_, 0, v_waiter_836_);
v___x_839_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_token_835_, v___f_838_);
return v___x_839_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_selector___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_token_835_ = stack[0].m_obj;
lean_object* v_waiter_836_ = stack[1].m_obj;
lean_object* v_res_840_;
v_res_840_ = l_Std_CancellationToken_selector___lam__4(v_token_835_, v_waiter_836_);
stack->m_obj
 = v_res_840_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__4___boxed(lean_object* v_token_841_, lean_object* v_waiter_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_CancellationToken_selector___lam__4(v_token_841_, v_waiter_842_);
return v_res_844_;
}
}
lean_object* l_Std_CancellationToken_selector___lam__5(lean_object* v_x_855_){
_start:
{
if (lean_obj_tag(v_x_855_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_865_; 
v_a_857_ = lean_ctor_get(v_x_855_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v_x_855_);
if (v_isSharedCheck_865_ == 0)
{
v___x_859_ = v_x_855_;
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v_x_855_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_865_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_864_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_863_; 
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
}
else
{
lean_object* v_a_866_; uint8_t v___x_867_; 
v_a_866_ = lean_ctor_get(v_x_855_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v_x_855_, 1);
v___x_867_ = lean_unbox(v_a_866_);
lean_dec(v_a_866_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
v___x_868_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__5___closed__1));
return v___x_868_;
}
else
{
lean_object* v___x_869_; 
v___x_869_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__5___closed__4));
return v___x_869_;
}
}
}
}
LEAN_EXPORT void l_Std_CancellationToken_selector___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_855_ = stack[0].m_obj;
lean_object* v_res_870_;
v_res_870_ = l_Std_CancellationToken_selector___lam__5(v_x_855_);
stack->m_obj
 = v_res_870_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__5___boxed(lean_object* v_x_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_CancellationToken_selector___lam__5(v_x_871_);
return v_res_873_;
}
}
lean_object* l_Std_CancellationToken_selector___lam__6(lean_object* v_token_874_, lean_object* v___f_875_){
_start:
{
lean_object* v___x_877_; uint8_t v___x_878_; uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = 0;
v___x_879_ = l_Std_CancellationToken_isCancelled(v_token_874_);
v___x_880_ = lean_box(v___x_879_);
v___x_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
v___x_883_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_877_, v___x_878_, v___x_882_, v___f_875_);
return v___x_883_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_selector___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_token_874_ = stack[0].m_obj;
lean_object* v___f_875_ = stack[1].m_obj;
lean_object* v_res_884_;
v_res_884_ = l_Std_CancellationToken_selector___lam__6(v_token_874_, v___f_875_);
stack->m_obj
 = v_res_884_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__6___boxed(lean_object* v_token_885_, lean_object* v___f_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Std_CancellationToken_selector___lam__6(v_token_885_, v___f_886_);
return v_res_888_;
}
}
lean_object* l_Std_CancellationToken_selector___lam__7(lean_object* v_reason_889_, lean_object* v___y_890_, lean_object* v_x_891_){
_start:
{
if (lean_obj_tag(v_x_891_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_901_; 
lean_dec(v_reason_889_);
v_a_893_ = lean_ctor_get(v_x_891_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_891_);
if (v_isSharedCheck_901_ == 0)
{
v___x_895_ = v_x_891_;
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v_x_891_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_901_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_900_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_899_; 
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_a_902_ = lean_ctor_get(v_x_891_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v_x_891_, 1);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v_reason_889_);
lean_ctor_set(v___x_903_, 1, v_a_902_);
v___x_904_ = lean_st_ref_swap(v___y_890_, v___x_903_);
lean_dec(v___x_904_);
v___x_905_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__0));
return v___x_905_;
}
}
}
LEAN_EXPORT void l_Std_CancellationToken_selector___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_reason_889_ = stack[0].m_obj;
lean_object* v___y_890_ = stack[1].m_obj;
lean_object* v_x_891_ = stack[2].m_obj;
lean_object* v_res_906_;
v_res_906_ = l_Std_CancellationToken_selector___lam__7(v_reason_889_, v___y_890_, v_x_891_);
stack->m_obj
 = v_res_906_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__7___boxed(lean_object* v_reason_907_, lean_object* v___y_908_, lean_object* v_x_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Std_CancellationToken_selector___lam__7(v_reason_907_, v___y_908_, v_x_909_);
lean_dec(v___y_908_);
return v_res_911_;
}
}
lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_912_) == 0)
{
lean_object* v___x_914_; 
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v_x_912_);
return v___x_914_;
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_924_; 
v_a_915_ = lean_ctor_get(v_x_912_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v_x_912_);
if (v_isSharedCheck_924_ == 0)
{
v___x_917_ = v_x_912_;
v_isShared_918_ = v_isSharedCheck_924_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v_x_912_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_924_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = l_List_reverse___redArg(v_a_915_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_923_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_912_ = stack[0].m_obj;
lean_object* v_res_925_;
v_res_925_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(v_x_912_);
stack->m_obj
 = v_res_925_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0___boxed(lean_object* v_x_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(v_x_926_);
return v_res_928_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(lean_object* v_x_929_){
_start:
{
uint8_t v___y_932_; 
if (lean_obj_tag(v_x_929_) == 0)
{
lean_object* v___x_936_; 
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v_x_929_);
return v___x_936_;
}
else
{
lean_object* v_a_937_; uint8_t v___x_938_; 
v_a_937_ = lean_ctor_get(v_x_929_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v_x_929_, 1);
v___x_938_ = lean_unbox(v_a_937_);
lean_dec(v_a_937_);
if (v___x_938_ == 0)
{
uint8_t v___x_939_; 
v___x_939_ = 1;
v___y_932_ = v___x_939_;
goto v___jp_931_;
}
else
{
uint8_t v___x_940_; 
v___x_940_ = 0;
v___y_932_ = v___x_940_;
goto v___jp_931_;
}
}
v___jp_931_:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_box(v___y_932_);
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_929_ = stack[0].m_obj;
lean_object* v_res_941_;
v_res_941_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(v_x_929_);
stack->m_obj
 = v_res_941_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1___boxed(lean_object* v_x_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(v_x_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_945_, lean_object* v_x_946_, lean_object* v_head_947_, lean_object* v_x_948_, lean_object* v___y_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(v_tail_945_, v_x_946_, v_head_947_, v_x_948_);
return v_res_950_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(lean_object* v_x_957_, lean_object* v_x_958_){
_start:
{
if (lean_obj_tag(v_x_957_) == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v_x_958_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
else
{
lean_object* v_head_962_; lean_object* v_tail_963_; lean_object* v___f_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_head_962_ = lean_ctor_get(v_x_957_, 0);
lean_inc_n(v_head_962_, 2);
v_tail_963_ = lean_ctor_get(v_x_957_, 1);
lean_inc(v_tail_963_);
lean_dec_ref_known(v_x_957_, 2);
v___f_964_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_964_, 0, v_tail_963_);
lean_closure_set(v___f_964_, 1, v_x_958_);
lean_closure_set(v___f_964_, 2, v_head_962_);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = 0;
if (lean_obj_tag(v_head_962_) == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec_ref_known(v_head_962_, 1);
v___x_967_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1));
v___x_968_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_965_, v___x_966_, v___x_967_, v___f_964_);
return v___x_968_;
}
else
{
lean_object* v_finished_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_982_; 
v_finished_969_ = lean_ctor_get(v_head_962_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v_head_962_);
if (v_isSharedCheck_982_ == 0)
{
v___x_971_ = v_head_962_;
v_isShared_972_ = v_isSharedCheck_982_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_finished_969_);
lean_dec(v_head_962_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_982_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v_finished_973_; lean_object* v___f_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v_finished_973_ = lean_ctor_get(v_finished_969_, 0);
lean_inc(v_finished_973_);
lean_dec_ref(v_finished_969_);
v___f_974_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2));
v___x_975_ = lean_st_ref_get(v_finished_973_);
lean_dec(v_finished_973_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_975_);
v___x_977_ = v___x_971_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_981_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
v___x_979_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_965_, v___x_966_, v___x_978_, v___f_974_);
v___x_980_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_965_, v___x_966_, v___x_979_, v___f_964_);
return v___x_980_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_957_ = stack[0].m_obj;
lean_object* v_x_958_ = stack[1].m_obj;
lean_object* v_res_983_;
v_res_983_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_957_, v_x_958_);
stack->m_obj
 = v_res_983_;
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_984_, lean_object* v_x_985_, lean_object* v_head_986_, lean_object* v_x_987_){
_start:
{
if (lean_obj_tag(v_x_987_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v_head_986_);
lean_dec(v_x_985_);
lean_dec(v_tail_984_);
v_a_989_ = lean_ctor_get(v_x_987_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_x_987_);
if (v_isSharedCheck_997_ == 0)
{
v___x_991_ = v_x_987_;
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v_x_987_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_996_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; 
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
}
else
{
lean_object* v_a_998_; uint8_t v___x_999_; 
v_a_998_ = lean_ctor_get(v_x_987_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v_x_987_, 1);
v___x_999_ = lean_unbox(v_a_998_);
lean_dec(v_a_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec_ref(v_head_986_);
v___x_1000_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_984_, v_x_985_);
return v___x_1000_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_head_986_);
lean_ctor_set(v___x_1001_, 1, v_x_985_);
v___x_1002_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_984_, v___x_1001_);
return v___x_1002_;
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_984_ = stack[0].m_obj;
lean_object* v_x_985_ = stack[1].m_obj;
lean_object* v_head_986_ = stack[2].m_obj;
lean_object* v_x_987_ = stack[3].m_obj;
lean_object* v_res_1003_;
v_res_1003_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(v_tail_984_, v_x_985_, v_head_986_, v_x_987_);
stack->m_obj
 = v_res_1003_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___boxed(lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_1004_, v_x_1005_);
return v_res_1007_;
}
}
lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(lean_object* v_a_1008_, lean_object* v___x_1009_, lean_object* v_x_1010_){
_start:
{
if (lean_obj_tag(v_x_1010_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
lean_dec(v___x_1009_);
lean_dec(v_a_1008_);
v_a_1012_ = lean_ctor_get(v_x_1010_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_x_1010_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1014_ = v_x_1010_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v_x_1010_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1037_; 
v_a_1021_ = lean_ctor_get(v_x_1010_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_x_1010_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1023_ = v_x_1010_;
v_isShared_1024_ = v_isSharedCheck_1037_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v_x_1010_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1037_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
uint8_t v___x_1025_; 
v___x_1025_ = l_List_isEmpty___redArg(v_a_1008_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_dec(v___x_1009_);
v___x_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_a_1021_);
lean_ctor_set(v___x_1026_, 1, v_a_1008_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1026_);
v___x_1028_ = v___x_1023_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
lean_dec(v_a_1008_);
v___x_1031_ = l_List_reverse___redArg(v_a_1021_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1009_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1032_);
v___x_1034_ = v___x_1023_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1008_ = stack[0].m_obj;
lean_object* v___x_1009_ = stack[1].m_obj;
lean_object* v_x_1010_ = stack[2].m_obj;
lean_object* v_res_1038_;
v_res_1038_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(v_a_1008_, v___x_1009_, v_x_1010_);
stack->m_obj
 = v_res_1038_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed(lean_object* v_a_1039_, lean_object* v___x_1040_, lean_object* v_x_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(v_a_1039_, v___x_1040_, v_x_1041_);
return v_res_1043_;
}
}
lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(lean_object* v___x_1044_, lean_object* v_eList_1045_, lean_object* v___f_1046_, lean_object* v_x_1047_){
_start:
{
if (lean_obj_tag(v_x_1047_) == 0)
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v___f_1046_);
lean_dec(v_eList_1045_);
lean_dec(v___x_1044_);
v_a_1049_ = lean_ctor_get(v_x_1047_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_x_1047_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1051_ = v_x_1047_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v_x_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_a_1058_ = lean_ctor_get(v_x_1047_, 0);
lean_inc(v_a_1058_);
lean_dec_ref_known(v_x_1047_, 1);
lean_inc(v___x_1044_);
v___f_1059_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1059_, 0, v_a_1058_);
lean_closure_set(v___f_1059_, 1, v___x_1044_);
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = 0;
v___x_1062_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_eList_1045_, v___x_1044_);
v___x_1063_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1060_, v___x_1061_, v___x_1062_, v___f_1046_);
v___x_1064_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1060_, v___x_1061_, v___x_1063_, v___f_1059_);
return v___x_1064_;
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1044_ = stack[0].m_obj;
lean_object* v_eList_1045_ = stack[1].m_obj;
lean_object* v___f_1046_ = stack[2].m_obj;
lean_object* v_x_1047_ = stack[3].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(v___x_1044_, v_eList_1045_, v___f_1046_, v_x_1047_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed(lean_object* v___x_1066_, lean_object* v_eList_1067_, lean_object* v___f_1068_, lean_object* v_x_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(v___x_1066_, v_eList_1067_, v___f_1068_, v_x_1069_);
return v_res_1071_;
}
}
lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(lean_object* v_q_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_eList_1076_; lean_object* v_dList_1077_; lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_eList_1076_ = lean_ctor_get(v_q_1073_, 0);
lean_inc(v_eList_1076_);
v_dList_1077_ = lean_ctor_get(v_q_1073_, 1);
lean_inc(v_dList_1077_);
lean_dec_ref(v_q_1073_);
v___f_1078_ = ((lean_object*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0));
v___x_1079_ = lean_box(0);
v___f_1080_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1080_, 0, v___x_1079_);
lean_closure_set(v___f_1080_, 1, v_eList_1076_);
lean_closure_set(v___f_1080_, 2, v___f_1078_);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = 0;
v___x_1083_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_dList_1077_, v___x_1079_);
v___x_1084_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1081_, v___x_1082_, v___x_1083_, v___f_1078_);
v___x_1085_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1081_, v___x_1082_, v___x_1084_, v___f_1080_);
return v___x_1085_;
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_1073_ = stack[0].m_obj;
lean_object* v___y_1074_ = stack[1].m_obj;
lean_object* v_res_1086_;
v_res_1086_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_q_1073_, v___y_1074_);
stack->m_obj
 = v_res_1086_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___boxed(lean_object* v_q_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_q_1087_, v___y_1088_);
lean_dec(v___y_1088_);
return v_res_1090_;
}
}
lean_object* l_Std_CancellationToken_selector___lam__8(lean_object* v___y_1091_, lean_object* v_x_1092_){
_start:
{
if (lean_obj_tag(v_x_1092_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1102_; 
v_a_1094_ = lean_ctor_get(v_x_1092_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1092_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1096_ = v_x_1092_;
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v_x_1092_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1102_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
return v___x_1100_;
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v_reason_1104_; lean_object* v_consumers_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v_a_1103_ = lean_ctor_get(v_x_1092_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v_x_1092_, 1);
v_reason_1104_ = lean_ctor_get(v_a_1103_, 0);
lean_inc(v_reason_1104_);
v_consumers_1105_ = lean_ctor_get(v_a_1103_, 1);
lean_inc_ref(v_consumers_1105_);
lean_dec(v_a_1103_);
lean_inc(v___y_1091_);
v___f_1106_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1106_, 0, v_reason_1104_);
lean_closure_set(v___f_1106_, 1, v___y_1091_);
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = 0;
v___x_1109_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_consumers_1105_, v___y_1091_);
v___x_1110_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1107_, v___x_1108_, v___x_1109_, v___f_1106_);
return v___x_1110_;
}
}
}
LEAN_EXPORT void l_Std_CancellationToken_selector___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1091_ = stack[0].m_obj;
lean_object* v_x_1092_ = stack[1].m_obj;
lean_object* v_res_1111_;
v_res_1111_ = l_Std_CancellationToken_selector___lam__8(v___y_1091_, v_x_1092_);
stack->m_obj
 = v_res_1111_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__8___boxed(lean_object* v___y_1112_, lean_object* v_x_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Std_CancellationToken_selector___lam__8(v___y_1112_, v_x_1113_);
lean_dec(v___y_1112_);
return v_res_1115_;
}
}
lean_object* l_Std_CancellationToken_selector___lam__9(lean_object* v___y_1116_){
_start:
{
lean_object* v___f_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
lean_inc(v___y_1116_);
v___f_1118_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1118_, 0, v___y_1116_);
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = 0;
v___x_1121_ = lean_st_ref_get(v___y_1116_);
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
v___x_1124_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1119_, v___x_1120_, v___x_1123_, v___f_1118_);
return v___x_1124_;
}
}
LEAN_EXPORT void l_Std_CancellationToken_selector___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_1116_ = stack[0].m_obj;
lean_object* v_res_1125_;
v_res_1125_ = l_Std_CancellationToken_selector___lam__9(v___y_1116_);
stack->m_obj
 = v_res_1125_;
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__9___boxed(lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Std_CancellationToken_selector___lam__9(v___y_1126_);
lean_dec(v___y_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector(lean_object* v_token_1131_){
_start:
{
lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___f_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_inc_ref_n(v_token_1131_, 2);
v___f_1132_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1132_, 0, v_token_1131_);
v___f_1133_ = ((lean_object*)(l_Std_CancellationToken_selector___closed__0));
v___f_1134_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__6___boxed), 3, 2);
lean_closure_set(v___f_1134_, 0, v_token_1131_);
lean_closure_set(v___f_1134_, 1, v___f_1133_);
v___f_1135_ = ((lean_object*)(l_Std_CancellationToken_selector___closed__1));
v___x_1136_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed), 5, 4);
lean_closure_set(v___x_1136_, 0, lean_box(0));
lean_closure_set(v___x_1136_, 1, lean_box(0));
lean_closure_set(v___x_1136_, 2, v_token_1131_);
lean_closure_set(v___x_1136_, 3, v___f_1135_);
v___x_1137_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1137_, 0, v___f_1134_);
lean_ctor_set(v___x_1137_, 1, v___f_1132_);
lean_ctor_set(v___x_1137_, 2, v___x_1136_);
return v___x_1137_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(lean_object* v_x_1138_, lean_object* v_x_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_1138_, v_x_1139_);
return v___x_1142_;
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1138_ = stack[0].m_obj;
lean_object* v_x_1139_ = stack[1].m_obj;
lean_object* v___y_1140_ = stack[2].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(v_x_1138_, v_x_1139_, v___y_1140_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___boxed(lean_object* v_x_1144_, lean_object* v_x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(v_x_1144_, v_x_1145_, v___y_1146_);
lean_dec(v___y_1146_);
return v_res_1148_;
}
}
lean_object* runtime_initialize_Std_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_CancellationToken(uint8_t builtin) {
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
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_CancellationToken(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data(uint8_t builtin);
lean_object* initialize_Init_Data_Queue(uint8_t builtin);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* initialize_Std_Async_Select(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_CancellationToken(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_CancellationToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_CancellationToken(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_CancellationToken(builtin);
}
#ifdef __cplusplus
}
#endif

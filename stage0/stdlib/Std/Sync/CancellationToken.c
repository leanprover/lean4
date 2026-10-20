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
LEAN_EXPORT uint8_t l_Std_instBEqCancellationReason_beq(lean_object* v_x_133_, lean_object* v_x_134_){
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
LEAN_EXPORT lean_object* l_Std_instBEqCancellationReason_beq___boxed(lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Std_instBEqCancellationReason_beq(v_x_145_, v_x_146_);
lean_dec(v_x_146_);
lean_dec(v_x_145_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStringCancellationReason___lam__0(lean_object* v_x_156_){
_start:
{
switch(lean_obj_tag(v_x_156_))
{
case 0:
{
lean_object* v___x_157_; 
v___x_157_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__0));
return v___x_157_;
}
case 1:
{
lean_object* v___x_158_; 
v___x_158_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__1));
return v___x_158_;
}
case 2:
{
lean_object* v___x_159_; 
v___x_159_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__2));
return v___x_159_;
}
default: 
{
lean_object* v_msg_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_msg_160_ = lean_ctor_get(v_x_156_, 0);
v___x_161_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__3));
v___x_162_ = lean_string_append(v___x_161_, v_msg_160_);
v___x_163_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__4));
v___x_164_ = lean_string_append(v___x_162_, v___x_163_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instToStringCancellationReason___lam__0___boxed(lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_instToStringCancellationReason___lam__0(v_x_165_);
lean_dec(v_x_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorIdx___impl(lean_object* v_x_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_tag_nat(v_x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorIdx___impl___boxed(lean_object* v_x_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_CancellationToken_Consumer_ctorIdx___impl(v_x_171_);
lean_dec_ref(v_x_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim___redArg(lean_object* v_t_173_, lean_object* v_k_174_){
_start:
{
if (lean_obj_tag(v_t_173_) == 0)
{
lean_object* v_promise_175_; lean_object* v___x_176_; 
v_promise_175_ = lean_ctor_get(v_t_173_, 0);
lean_inc(v_promise_175_);
lean_dec_ref_known(v_t_173_, 1);
v___x_176_ = lean_apply_1(v_k_174_, v_promise_175_);
return v___x_176_;
}
else
{
lean_object* v_finished_177_; lean_object* v___x_178_; 
v_finished_177_ = lean_ctor_get(v_t_173_, 0);
lean_inc_ref(v_finished_177_);
lean_dec_ref_known(v_t_173_, 1);
v___x_178_ = lean_apply_1(v_k_174_, v_finished_177_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim(lean_object* v_motive_179_, lean_object* v_ctorIdx_180_, lean_object* v_t_181_, lean_object* v_h_182_, lean_object* v_k_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_181_, v_k_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim___boxed(lean_object* v_motive_185_, lean_object* v_ctorIdx_186_, lean_object* v_t_187_, lean_object* v_h_188_, lean_object* v_k_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_CancellationToken_Consumer_ctorElim(v_motive_185_, v_ctorIdx_186_, v_t_187_, v_h_188_, v_k_189_);
lean_dec(v_ctorIdx_186_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_normal_elim___redArg(lean_object* v_t_191_, lean_object* v_normal_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_191_, v_normal_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_normal_elim(lean_object* v_motive_194_, lean_object* v_t_195_, lean_object* v_h_196_, lean_object* v_normal_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_195_, v_normal_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_select_elim___redArg(lean_object* v_t_199_, lean_object* v_select_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_199_, v_select_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_select_elim(lean_object* v_motive_202_, lean_object* v_t_203_, lean_object* v_h_204_, lean_object* v_select_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_203_, v_select_205_);
return v___x_206_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(lean_object* v_w_209_, lean_object* v_lose_210_){
_start:
{
lean_object* v_finished_212_; lean_object* v_promise_213_; lean_object* v___x_214_; uint8_t v___y_216_; uint8_t v___x_224_; 
v_finished_212_ = lean_ctor_get(v_w_209_, 0);
v_promise_213_ = lean_ctor_get(v_w_209_, 1);
v___x_214_ = lean_st_ref_take(v_finished_212_);
v___x_224_ = lean_unbox(v___x_214_);
lean_dec(v___x_214_);
if (v___x_224_ == 0)
{
uint8_t v___x_225_; 
v___x_225_ = 1;
v___y_216_ = v___x_225_;
goto v___jp_215_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = 0;
v___y_216_ = v___x_226_;
goto v___jp_215_;
}
v___jp_215_:
{
uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_217_ = 1;
v___x_218_ = lean_box(v___x_217_);
v___x_219_ = lean_st_ref_put(v_finished_212_, v___x_218_);
if (v___y_216_ == 0)
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = lean_apply_1(v_lose_210_, lean_box(0));
v___x_221_ = lean_unbox(v___x_220_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec_ref(v_lose_210_);
v___x_222_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_223_ = lean_io_promise_resolve(v___x_222_, v_promise_213_);
return v___y_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___boxed(lean_object* v_w_227_, lean_object* v_lose_228_, lean_object* v___y_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(v_w_227_, v_lose_228_);
lean_dec_ref(v_w_227_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationToken_Consumer_resolve___lam__0(uint8_t v___x_232_){
_start:
{
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_resolve___lam__0___boxed(lean_object* v___x_234_, lean_object* v___y_235_){
_start:
{
uint8_t v___x_380__boxed_236_; uint8_t v_res_237_; lean_object* v_r_238_; 
v___x_380__boxed_236_ = lean_unbox(v___x_234_);
v_res_237_ = l_Std_CancellationToken_Consumer_resolve___lam__0(v___x_380__boxed_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationToken_Consumer_resolve(lean_object* v_c_242_){
_start:
{
if (lean_obj_tag(v_c_242_) == 0)
{
lean_object* v_promise_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_promise_244_ = lean_ctor_get(v_c_242_, 0);
v___x_245_ = lean_box(0);
v___x_246_ = lean_io_promise_resolve(v___x_245_, v_promise_244_);
v___x_247_ = 1;
return v___x_247_;
}
else
{
lean_object* v_finished_248_; lean_object* v_lose_249_; uint8_t v___x_250_; 
v_finished_248_ = lean_ctor_get(v_c_242_, 0);
v_lose_249_ = ((lean_object*)(l_Std_CancellationToken_Consumer_resolve___closed__0));
v___x_250_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(v_finished_248_, v_lose_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_resolve___boxed(lean_object* v_c_251_, lean_object* v_a_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Std_CancellationToken_Consumer_resolve(v_c_251_);
lean_dec_ref(v_c_251_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
static lean_object* _init_l_Std_CancellationToken_new___closed__0(void){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Std_Queue_empty___redArg();
return v___x_255_;
}
}
static lean_object* _init_l_Std_CancellationToken_new___closed__1(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_obj_once(&l_Std_CancellationToken_new___closed__0, &l_Std_CancellationToken_new___closed__0_once, _init_l_Std_CancellationToken_new___closed__0);
v___x_257_ = lean_box(0);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___x_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_new(){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_obj_once(&l_Std_CancellationToken_new___closed__1, &l_Std_CancellationToken_new___closed__1_once, _init_l_Std_CancellationToken_new___closed__1);
v___x_261_ = l_Std_Mutex_new___redArg(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_new___boxed(lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_CancellationToken_new();
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(lean_object* v_mutex_264_, lean_object* v_k_265_){
_start:
{
lean_object* v_ref_267_; lean_object* v_mutex_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_ref_267_ = lean_ctor_get(v_mutex_264_, 0);
lean_inc(v_ref_267_);
v_mutex_268_ = lean_ctor_get(v_mutex_264_, 1);
lean_inc(v_mutex_268_);
lean_dec_ref(v_mutex_264_);
v___x_269_ = lean_io_basemutex_lock(v_mutex_268_);
v___x_270_ = lean_apply_2(v_k_265_, v_ref_267_, lean_box(0));
v___x_271_ = lean_io_basemutex_unlock(v_mutex_268_);
lean_dec(v_mutex_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg___boxed(lean_object* v_mutex_272_, lean_object* v_k_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_mutex_272_, v_k_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_, lean_object* v_mutex_278_, lean_object* v_k_279_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_mutex_278_, v_k_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___boxed(lean_object* v_00_u03b1_282_, lean_object* v_00_u03b2_283_, lean_object* v_mutex_284_, lean_object* v_k_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(v_00_u03b1_282_, v_00_u03b2_283_, v_mutex_284_, v_k_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(lean_object* v_a_288_){
_start:
{
lean_object* v___x_290_; 
lean_inc_ref(v_a_288_);
v___x_290_ = l_Std_Queue_dequeue_x3f___redArg(v_a_288_);
if (lean_obj_tag(v___x_290_) == 1)
{
lean_object* v_val_291_; lean_object* v_fst_292_; lean_object* v_snd_293_; uint8_t v___x_294_; 
lean_dec_ref(v_a_288_);
v_val_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v___x_290_, 1);
v_fst_292_ = lean_ctor_get(v_val_291_, 0);
lean_inc(v_fst_292_);
v_snd_293_ = lean_ctor_get(v_val_291_, 1);
lean_inc(v_snd_293_);
lean_dec(v_val_291_);
v___x_294_ = l_Std_CancellationToken_Consumer_resolve(v_fst_292_);
lean_dec(v_fst_292_);
v_a_288_ = v_snd_293_;
goto _start;
}
else
{
lean_dec(v___x_290_);
return v_a_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg___boxed(lean_object* v_a_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___lam__0(lean_object* v_reason_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; lean_object* v_reason_303_; 
v___x_302_ = lean_st_ref_get(v___y_300_);
v_reason_303_ = lean_ctor_get(v___x_302_, 0);
if (lean_obj_tag(v_reason_303_) == 0)
{
lean_object* v_consumers_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_316_; 
v_consumers_304_ = lean_ctor_get(v___x_302_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; 
v_unused_317_ = lean_ctor_get(v___x_302_, 0);
lean_dec(v_unused_317_);
v___x_306_ = v___x_302_;
v_isShared_307_ = v_isSharedCheck_316_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_consumers_304_);
lean_dec(v___x_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_316_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_st_311_; 
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v_reason_299_);
v___x_309_ = lean_obj_once(&l_Std_CancellationToken_new___closed__0, &l_Std_CancellationToken_new___closed__0_once, _init_l_Std_CancellationToken_new___closed__0);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v___x_309_);
lean_ctor_set(v___x_306_, 0, v___x_308_);
v_st_311_ = v___x_306_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_309_);
v_st_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_consumers_304_);
lean_dec_ref(v___x_312_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_st_ref_swap(v___y_300_, v_st_311_);
lean_dec(v___x_314_);
return v___x_313_;
}
}
}
else
{
lean_object* v___x_318_; 
lean_dec(v___x_302_);
lean_dec(v_reason_299_);
v___x_318_ = lean_box(0);
return v___x_318_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___lam__0___boxed(lean_object* v_reason_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_CancellationToken_cancel___lam__0(v_reason_319_, v___y_320_);
lean_dec(v___y_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel(lean_object* v_x_323_, lean_object* v_reason_324_){
_start:
{
lean_object* v___f_326_; lean_object* v___x_327_; 
v___f_326_ = lean_alloc_closure((void*)(l_Std_CancellationToken_cancel___lam__0___boxed), 3, 1);
lean_closure_set(v___f_326_, 0, v_reason_324_);
v___x_327_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_323_, v___f_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___boxed(lean_object* v_x_328_, lean_object* v_reason_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_CancellationToken_cancel(v_x_328_, v_reason_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0(lean_object* v_inst_332_, lean_object* v_a_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_333_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___boxed(lean_object* v_inst_337_, lean_object* v_a_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0(v_inst_337_, v_a_338_, v___y_339_);
lean_dec(v___y_339_);
return v_res_341_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationToken_isCancelled___lam__0(lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; lean_object* v_reason_345_; 
v___x_344_ = lean_st_ref_get(v___y_342_);
v_reason_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_reason_345_);
lean_dec(v___x_344_);
if (lean_obj_tag(v_reason_345_) == 0)
{
uint8_t v___x_346_; 
v___x_346_ = 0;
return v___x_346_;
}
else
{
uint8_t v___x_347_; 
lean_dec_ref_known(v_reason_345_, 1);
v___x_347_ = 1;
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_isCancelled___lam__0___boxed(lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
uint8_t v_res_350_; lean_object* v_r_351_; 
v_res_350_ = l_Std_CancellationToken_isCancelled___lam__0(v___y_348_);
lean_dec(v___y_348_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationToken_isCancelled(lean_object* v_x_353_){
_start:
{
lean_object* v___f_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___f_355_ = ((lean_object*)(l_Std_CancellationToken_isCancelled___closed__0));
v___x_356_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_353_, v___f_355_);
v___x_357_ = lean_unbox(v___x_356_);
lean_dec(v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_isCancelled___boxed(lean_object* v_x_358_, lean_object* v_a_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Std_CancellationToken_isCancelled(v_x_358_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___lam__0(lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; lean_object* v_reason_365_; 
v___x_364_ = lean_st_ref_get(v___y_362_);
v_reason_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_reason_365_);
lean_dec(v___x_364_);
return v_reason_365_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___lam__0___boxed(lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_CancellationToken_getCancellationReason___lam__0(v___y_366_);
lean_dec(v___y_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason(lean_object* v_x_370_){
_start:
{
lean_object* v___f_372_; lean_object* v___x_373_; 
v___f_372_ = ((lean_object*)(l_Std_CancellationToken_getCancellationReason___closed__0));
v___x_373_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_370_, v___f_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___boxed(lean_object* v_x_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_CancellationToken_getCancellationReason(v_x_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(lean_object* v_mutex_377_, lean_object* v_k_378_){
_start:
{
lean_object* v_ref_380_; lean_object* v_mutex_381_; lean_object* v___x_382_; lean_object* v_r_383_; 
v_ref_380_ = lean_ctor_get(v_mutex_377_, 0);
lean_inc(v_ref_380_);
v_mutex_381_ = lean_ctor_get(v_mutex_377_, 1);
lean_inc(v_mutex_381_);
lean_dec_ref(v_mutex_377_);
v___x_382_ = lean_io_basemutex_lock(v_mutex_381_);
v_r_383_ = lean_apply_2(v_k_378_, v_ref_380_, lean_box(0));
if (lean_obj_tag(v_r_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_392_; 
v_a_384_ = lean_ctor_get(v_r_383_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v_r_383_);
if (v_isSharedCheck_392_ == 0)
{
v___x_386_ = v_r_383_;
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v_r_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_392_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_io_basemutex_unlock(v_mutex_381_);
lean_dec(v_mutex_381_);
if (v_isShared_387_ == 0)
{
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_384_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_a_393_ = lean_ctor_get(v_r_383_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_r_383_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v_r_383_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v_r_383_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = lean_io_basemutex_unlock(v_mutex_381_);
lean_dec(v_mutex_381_);
if (v_isShared_396_ == 0)
{
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_393_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg___boxed(lean_object* v_mutex_402_, lean_object* v_k_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_mutex_402_, v_k_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(lean_object* v_00_u03b1_406_, lean_object* v_00_u03b2_407_, lean_object* v_mutex_408_, lean_object* v_k_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_mutex_408_, v_k_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___boxed(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_mutex_414_, lean_object* v_k_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(v_00_u03b1_412_, v_00_u03b2_413_, v_mutex_414_, v_k_415_);
return v_res_417_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__1(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l_Std_CancellationToken_wait___lam__0___closed__0));
v___x_420_ = lean_mk_io_user_error(v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__2(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__1, &l_Std_CancellationToken_wait___lam__0___closed__1_once, _init_l_Std_CancellationToken_wait___lam__0___closed__1);
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
return v___x_422_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__3(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__2, &l_Std_CancellationToken_wait___lam__0___closed__2_once, _init_l_Std_CancellationToken_wait___lam__0___closed__2);
v___x_424_ = lean_task_pure(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__4(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_426_ = lean_task_pure(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__0(lean_object* v_a_427_){
_start:
{
if (lean_obj_tag(v_a_427_) == 0)
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__3, &l_Std_CancellationToken_wait___lam__0___closed__3_once, _init_l_Std_CancellationToken_wait___lam__0___closed__3);
return v___x_429_;
}
else
{
lean_object* v___x_430_; 
v___x_430_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__4, &l_Std_CancellationToken_wait___lam__0___closed__4_once, _init_l_Std_CancellationToken_wait___lam__0___closed__4);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__0___boxed(lean_object* v_a_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_CancellationToken_wait___lam__0(v_a_431_);
lean_dec(v_a_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__1(lean_object* v___f_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; lean_object* v_reason_438_; 
v___x_437_ = lean_st_ref_get(v___y_435_);
v_reason_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_reason_438_);
lean_dec(v___x_437_);
if (lean_obj_tag(v_reason_438_) == 0)
{
uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_reason_442_; lean_object* v_consumers_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_457_; 
v___x_439_ = 0;
v___x_440_ = lean_io_promise_new();
v___x_441_ = lean_st_ref_take(v___y_435_);
v_reason_442_ = lean_ctor_get(v___x_441_, 0);
v_consumers_443_ = lean_ctor_get(v___x_441_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_457_ == 0)
{
v___x_445_ = v___x_441_;
v_isShared_446_ = v_isSharedCheck_457_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_consumers_443_);
lean_inc(v_reason_442_);
lean_dec(v___x_441_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_457_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
lean_inc(v___x_440_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_440_);
v___x_448_ = l_Std_Queue_enqueue___redArg(v___x_447_, v_consumers_443_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_448_);
v___x_450_ = v___x_445_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_reason_442_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_456_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_451_ = lean_st_ref_put(v___y_435_, v___x_450_);
v___x_452_ = lean_io_promise_result_opt(v___x_440_);
lean_dec(v___x_440_);
v___x_453_ = lean_unsigned_to_nat(0u);
v___x_454_ = lean_io_bind_task(v___x_452_, v___f_434_, v___x_453_, v___x_439_);
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
}
else
{
lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_465_; 
lean_dec_ref(v___f_434_);
v_isSharedCheck_465_ = !lean_is_exclusive(v_reason_438_);
if (v_isSharedCheck_465_ == 0)
{
lean_object* v_unused_466_; 
v_unused_466_ = lean_ctor_get(v_reason_438_, 0);
lean_dec(v_unused_466_);
v___x_459_ = v_reason_438_;
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
else
{
lean_dec(v_reason_438_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_465_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_461_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__4, &l_Std_CancellationToken_wait___lam__0___closed__4_once, _init_l_Std_CancellationToken_wait___lam__0___closed__4);
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 0);
lean_ctor_set(v___x_459_, 0, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__1___boxed(lean_object* v___f_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Std_CancellationToken_wait___lam__1(v___f_467_, v___y_468_);
lean_dec(v___y_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait(lean_object* v_x_474_){
_start:
{
lean_object* v___f_476_; lean_object* v___x_477_; 
v___f_476_ = ((lean_object*)(l_Std_CancellationToken_wait___closed__1));
v___x_477_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_x_474_, v___f_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___boxed(lean_object* v_x_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_CancellationToken_wait(v_x_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(uint8_t v___x_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_492_; 
v_a_484_ = lean_ctor_get(v_x_482_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_492_ == 0)
{
v___x_486_ = v_x_482_;
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v_x_482_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_492_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_491_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
}
else
{
lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_501_; 
v_isSharedCheck_501_ = !lean_is_exclusive(v_x_482_);
if (v_isSharedCheck_501_ == 0)
{
lean_object* v_unused_502_; 
v_unused_502_ = lean_ctor_get(v_x_482_, 0);
lean_dec(v_unused_502_);
v___x_494_ = v_x_482_;
v_isShared_495_ = v_isSharedCheck_501_;
goto v_resetjp_493_;
}
else
{
lean_dec(v_x_482_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_501_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = lean_box(v___x_481_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_496_);
v___x_498_ = v_reuseFailAlloc_500_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0___boxed(lean_object* v___x_503_, lean_object* v_x_504_, lean_object* v___y_505_){
_start:
{
uint8_t v___x_6594__boxed_506_; lean_object* v_res_507_; 
v___x_6594__boxed_506_ = lean_unbox(v___x_503_);
v_res_507_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(v___x_6594__boxed_506_, v_x_504_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(lean_object* v_lose_508_, lean_object* v___y_509_, lean_object* v_promise_510_, lean_object* v___f_511_, lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v___x_514_; 
lean_dec_ref(v___f_511_);
lean_dec_ref(v_lose_508_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v_x_512_);
return v___x_514_;
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_530_; 
v_a_515_ = lean_ctor_get(v_x_512_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_512_);
if (v_isSharedCheck_530_ == 0)
{
v___x_517_ = v_x_512_;
v_isShared_518_ = v_isSharedCheck_530_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v_x_512_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_530_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
uint8_t v___x_519_; 
v___x_519_ = lean_unbox(v_a_515_);
lean_dec(v_a_515_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
lean_del_object(v___x_517_);
lean_dec_ref(v___f_511_);
lean_inc(v___y_509_);
v___x_520_ = lean_apply_2(v_lose_508_, v___y_509_, lean_box(0));
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec_ref(v_lose_508_);
v___x_521_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = 0;
v___x_524_ = lean_io_promise_resolve(v___x_521_, v_promise_510_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_524_);
v___x_526_ = v___x_517_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_529_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___x_528_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_522_, v___x_523_, v___x_527_, v___f_511_);
return v___x_528_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed(lean_object* v_lose_531_, lean_object* v___y_532_, lean_object* v_promise_533_, lean_object* v___f_534_, lean_object* v_x_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(v_lose_531_, v___y_532_, v_promise_533_, v___f_534_, v_x_535_);
lean_dec(v_promise_533_);
lean_dec(v___y_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(lean_object* v_w_541_, lean_object* v_lose_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_finished_545_; lean_object* v_promise_546_; uint8_t v___x_547_; lean_object* v___f_548_; lean_object* v___f_549_; lean_object* v___x_550_; uint8_t v___x_551_; lean_object* v___x_552_; uint8_t v___y_554_; uint8_t v___x_561_; 
v_finished_545_ = lean_ctor_get(v_w_541_, 0);
lean_inc(v_finished_545_);
v_promise_546_ = lean_ctor_get(v_w_541_, 1);
lean_inc(v_promise_546_);
lean_dec_ref(v_w_541_);
v___x_547_ = 1;
v___f_548_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0));
lean_inc(v___y_543_);
v___f_549_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed), 6, 4);
lean_closure_set(v___f_549_, 0, v_lose_542_);
lean_closure_set(v___f_549_, 1, v___y_543_);
lean_closure_set(v___f_549_, 2, v_promise_546_);
lean_closure_set(v___f_549_, 3, v___f_548_);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = 0;
v___x_552_ = lean_st_ref_take(v_finished_545_);
v___x_561_ = lean_unbox(v___x_552_);
lean_dec(v___x_552_);
if (v___x_561_ == 0)
{
v___y_554_ = v___x_547_;
goto v___jp_553_;
}
else
{
v___y_554_ = v___x_551_;
goto v___jp_553_;
}
v___jp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_555_ = lean_box(v___x_547_);
v___x_556_ = lean_st_ref_put(v_finished_545_, v___x_555_);
lean_dec(v_finished_545_);
v___x_557_ = lean_box(v___y_554_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_550_, v___x_551_, v___x_559_, v___f_549_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___boxed(lean_object* v_w_562_, lean_object* v_lose_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(v_w_562_, v_lose_563_, v___y_564_);
lean_dec(v___y_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(lean_object* v___y_567_){
_start:
{
if (lean_obj_tag(v___y_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
v_a_568_ = lean_ctor_get(v___y_567_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___y_567_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___y_567_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___y_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_584_; 
v_a_576_ = lean_ctor_get(v___y_567_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___y_567_);
if (v_isSharedCheck_584_ == 0)
{
v___x_578_ = v___y_567_;
v_isShared_579_ = v_isSharedCheck_584_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___y_567_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_584_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_fst_580_; lean_object* v___x_582_; 
v_fst_580_ = lean_ctor_get(v_a_576_, 0);
lean_inc(v_fst_580_);
lean_dec(v_a_576_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_fst_580_);
v___x_582_ = v___x_578_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_fst_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(lean_object* v_mutex_585_, lean_object* v_x_586_){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_io_basemutex_unlock(v_mutex_585_);
v___x_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed(lean_object* v_mutex_591_, lean_object* v_x_592_, lean_object* v___y_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(v_mutex_591_, v_x_592_);
lean_dec(v_x_592_);
lean_dec(v_mutex_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(lean_object* v_k_595_, lean_object* v_ref_596_, lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
lean_dec(v_ref_596_);
lean_dec_ref(v_k_595_);
v_a_599_ = lean_ctor_get(v_x_597_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v_x_597_);
if (v_isSharedCheck_607_ == 0)
{
v___x_601_ = v_x_597_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v_x_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
return v___x_605_;
}
}
}
else
{
lean_object* v___x_608_; 
lean_dec_ref_known(v_x_597_, 1);
v___x_608_ = lean_apply_2(v_k_595_, v_ref_596_, lean_box(0));
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed(lean_object* v_k_609_, lean_object* v_ref_610_, lean_object* v_x_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(v_k_609_, v_ref_610_, v_x_611_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(lean_object* v_mutex_614_, lean_object* v___f_615_){
_start:
{
lean_object* v___x_617_; uint8_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = 0;
v___x_619_ = lean_io_basemutex_lock(v_mutex_614_);
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
v___x_622_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_617_, v___x_618_, v___x_621_, v___f_615_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3___boxed(lean_object* v_mutex_623_, lean_object* v___f_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(v_mutex_623_, v___f_624_);
lean_dec(v_mutex_623_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(lean_object* v_mutex_628_, lean_object* v_k_629_){
_start:
{
lean_object* v_ref_631_; lean_object* v_mutex_632_; lean_object* v___f_633_; lean_object* v___f_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; lean_object* v___y_641_; 
v_ref_631_ = lean_ctor_get(v_mutex_628_, 0);
lean_inc(v_ref_631_);
v_mutex_632_ = lean_ctor_get(v_mutex_628_, 1);
lean_inc_n(v_mutex_632_, 2);
lean_dec_ref(v_mutex_628_);
v___f_633_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0));
v___f_634_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_634_, 0, v_mutex_632_);
v___f_635_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_635_, 0, v_k_629_);
lean_closure_set(v___f_635_, 1, v_ref_631_);
v___f_636_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_636_, 0, v_mutex_632_);
lean_closure_set(v___f_636_, 1, v___f_635_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = 0;
v___x_639_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_636_, v___f_634_, v___x_637_, v___x_638_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_643_; 
v_a_643_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_639_, 1);
if (lean_obj_tag(v_a_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_a_644_ = lean_ctor_get(v_a_643_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_a_643_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v_a_643_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v_a_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
v___y_641_ = v___x_649_;
goto v___jp_640_;
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_a_652_ = lean_ctor_get(v_a_643_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_a_643_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v_a_643_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v_a_643_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v_fst_656_; lean_object* v___x_658_; 
v_fst_656_ = lean_ctor_get(v_a_652_, 0);
lean_inc(v_fst_656_);
lean_dec(v_a_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v_fst_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_fst_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
v___y_641_ = v___x_658_;
goto v___jp_640_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_669_; 
v_a_661_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_669_ == 0)
{
v___x_663_ = v___x_639_;
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_639_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_665_ = lean_task_map(v___f_633_, v_a_661_, v___x_637_, v___x_638_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
v___jp_640_:
{
lean_object* v___x_642_; 
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___y_641_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___boxed(lean_object* v_mutex_670_, lean_object* v_k_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_mutex_670_, v_k_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_mutex_676_, lean_object* v_k_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_mutex_676_, v_k_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b2_681_, lean_object* v_mutex_682_, lean_object* v_k_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(v_00_u03b1_680_, v_00_u03b2_681_, v_mutex_682_, v_k_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__0(uint8_t v___x_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = lean_box(v___x_686_);
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__0___boxed(lean_object* v___x_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v___x_6910__boxed_695_; lean_object* v_res_696_; 
v___x_6910__boxed_695_ = lean_unbox(v___x_692_);
v_res_696_ = l_Std_CancellationToken_selector___lam__0(v___x_6910__boxed_695_, v___y_693_);
lean_dec(v___y_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__1(lean_object* v___x_697_, lean_object* v___y_698_){
_start:
{
if (lean_obj_tag(v___y_698_) == 0)
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_a_699_ = lean_ctor_get(v___y_698_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___y_698_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___y_698_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___y_698_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
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
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_isSharedCheck_713_ = !lean_is_exclusive(v___y_698_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; 
v_unused_714_ = lean_ctor_get(v___y_698_, 0);
lean_dec(v_unused_714_);
v___x_708_ = v___y_698_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_dec(v___y_698_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_697_);
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_697_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__2(lean_object* v___y_722_, lean_object* v_waiter_723_, lean_object* v_x_724_){
_start:
{
if (lean_obj_tag(v_x_724_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v_waiter_723_);
v_a_726_ = lean_ctor_get(v_x_724_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_x_724_);
if (v_isSharedCheck_734_ == 0)
{
v___x_728_ = v_x_724_;
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v_x_724_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_733_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; 
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
else
{
lean_object* v_a_735_; lean_object* v_reason_736_; 
v_a_735_ = lean_ctor_get(v_x_724_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v_x_724_, 1);
v_reason_736_ = lean_ctor_get(v_a_735_, 0);
lean_inc(v_reason_736_);
lean_dec(v_a_735_);
if (lean_obj_tag(v_reason_736_) == 0)
{
lean_object* v___x_737_; lean_object* v_reason_738_; lean_object* v_consumers_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_750_; 
v___x_737_ = lean_st_ref_take(v___y_722_);
v_reason_738_ = lean_ctor_get(v___x_737_, 0);
v_consumers_739_ = lean_ctor_get(v___x_737_, 1);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_750_ == 0)
{
v___x_741_ = v___x_737_;
v_isShared_742_ = v_isSharedCheck_750_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_consumers_739_);
lean_inc(v_reason_738_);
lean_dec(v___x_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_750_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_746_; 
v___x_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_743_, 0, v_waiter_723_);
v___x_744_ = l_Std_Queue_enqueue___redArg(v___x_743_, v_consumers_739_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 1, v___x_744_);
v___x_746_ = v___x_741_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_reason_738_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_749_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_st_ref_put(v___y_722_, v___x_746_);
v___x_748_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__0));
return v___x_748_;
}
}
}
else
{
lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_783_; 
v_isSharedCheck_783_ = !lean_is_exclusive(v_reason_736_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_reason_736_, 0);
lean_dec(v_unused_784_);
v___x_752_ = v_reason_736_;
v_isShared_753_ = v_isSharedCheck_783_;
goto v_resetjp_751_;
}
else
{
lean_dec(v_reason_736_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_783_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
uint8_t v___x_754_; lean_object* v___f_755_; lean_object* v___f_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___y_760_; 
v___x_754_ = 0;
v___f_755_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__1));
v___f_756_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__2));
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(v_waiter_723_, v___f_755_, v___y_722_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_758_, 1);
if (lean_obj_tag(v_a_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
v_a_765_ = lean_ctor_get(v_a_764_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v_a_764_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v_a_764_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v_a_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
v___y_760_ = v___x_770_;
goto v___jp_759_;
}
}
}
else
{
lean_object* v___x_773_; 
lean_dec_ref_known(v_a_764_, 1);
v___x_773_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___y_760_ = v___x_773_;
goto v___jp_759_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
lean_del_object(v___x_752_);
v_a_774_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_782_ == 0)
{
v___x_776_ = v___x_758_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_758_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_task_map(v___f_756_, v_a_774_, v___x_757_, v___x_754_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
v___jp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 0);
lean_ctor_set(v___x_752_, 0, v___y_760_);
v___x_762_ = v___x_752_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___y_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__2___boxed(lean_object* v___y_785_, lean_object* v_waiter_786_, lean_object* v_x_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_CancellationToken_selector___lam__2(v___y_785_, v_waiter_786_, v_x_787_);
lean_dec(v___y_785_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__3(lean_object* v_waiter_790_, lean_object* v___y_791_){
_start:
{
lean_object* v___f_793_; lean_object* v___x_794_; uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_inc(v___y_791_);
v___f_793_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__2___boxed), 4, 2);
lean_closure_set(v___f_793_, 0, v___y_791_);
lean_closure_set(v___f_793_, 1, v_waiter_790_);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = 0;
v___x_796_ = lean_st_ref_get(v___y_791_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___x_799_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_794_, v___x_795_, v___x_798_, v___f_793_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__3___boxed(lean_object* v_waiter_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_CancellationToken_selector___lam__3(v_waiter_800_, v___y_801_);
lean_dec(v___y_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__4(lean_object* v_token_804_, lean_object* v_waiter_805_){
_start:
{
lean_object* v___f_807_; lean_object* v___x_808_; 
v___f_807_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_807_, 0, v_waiter_805_);
v___x_808_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_token_804_, v___f_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__4___boxed(lean_object* v_token_809_, lean_object* v_waiter_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_CancellationToken_selector___lam__4(v_token_809_, v_waiter_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__5(lean_object* v_x_823_){
_start:
{
if (lean_obj_tag(v_x_823_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_833_; 
v_a_825_ = lean_ctor_get(v_x_823_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_x_823_);
if (v_isSharedCheck_833_ == 0)
{
v___x_827_ = v_x_823_;
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v_x_823_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_832_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
else
{
lean_object* v_a_834_; uint8_t v___x_835_; 
v_a_834_ = lean_ctor_get(v_x_823_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v_x_823_, 1);
v___x_835_ = lean_unbox(v_a_834_);
lean_dec(v_a_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
v___x_836_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__5___closed__1));
return v___x_836_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__5___closed__4));
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__5___boxed(lean_object* v_x_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_CancellationToken_selector___lam__5(v_x_838_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__6(lean_object* v_token_841_, lean_object* v___f_842_){
_start:
{
lean_object* v___x_844_; uint8_t v___x_845_; uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_844_ = lean_unsigned_to_nat(0u);
v___x_845_ = 0;
v___x_846_ = l_Std_CancellationToken_isCancelled(v_token_841_);
v___x_847_ = lean_box(v___x_846_);
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
v___x_850_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_844_, v___x_845_, v___x_849_, v___f_842_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__6___boxed(lean_object* v_token_851_, lean_object* v___f_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_CancellationToken_selector___lam__6(v_token_851_, v___f_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__7(lean_object* v_reason_855_, lean_object* v___y_856_, lean_object* v_x_857_){
_start:
{
if (lean_obj_tag(v_x_857_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_reason_855_);
v_a_859_ = lean_ctor_get(v_x_857_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v_x_857_);
if (v_isSharedCheck_867_ == 0)
{
v___x_861_ = v_x_857_;
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v_x_857_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_866_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; 
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_a_868_ = lean_ctor_get(v_x_857_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v_x_857_, 1);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_reason_855_);
lean_ctor_set(v___x_869_, 1, v_a_868_);
v___x_870_ = lean_st_ref_swap(v___y_856_, v___x_869_);
lean_dec(v___x_870_);
v___x_871_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__0));
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__7___boxed(lean_object* v_reason_872_, lean_object* v___y_873_, lean_object* v_x_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_CancellationToken_selector___lam__7(v_reason_872_, v___y_873_, v_x_874_);
lean_dec(v___y_873_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_877_) == 0)
{
lean_object* v___x_879_; 
v___x_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_879_, 0, v_x_877_);
return v___x_879_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_889_; 
v_a_880_ = lean_ctor_get(v_x_877_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v_x_877_);
if (v_isSharedCheck_889_ == 0)
{
v___x_882_ = v_x_877_;
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v_x_877_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = l_List_reverse___redArg(v_a_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_888_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; 
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0___boxed(lean_object* v_x_890_, lean_object* v___y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(v_x_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(lean_object* v_x_893_){
_start:
{
uint8_t v___y_896_; 
if (lean_obj_tag(v_x_893_) == 0)
{
lean_object* v___x_900_; 
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v_x_893_);
return v___x_900_;
}
else
{
lean_object* v_a_901_; uint8_t v___x_902_; 
v_a_901_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v_x_893_, 1);
v___x_902_ = lean_unbox(v_a_901_);
lean_dec(v_a_901_);
if (v___x_902_ == 0)
{
uint8_t v___x_903_; 
v___x_903_ = 1;
v___y_896_ = v___x_903_;
goto v___jp_895_;
}
else
{
uint8_t v___x_904_; 
v___x_904_ = 0;
v___y_896_ = v___x_904_;
goto v___jp_895_;
}
}
v___jp_895_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_box(v___y_896_);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1___boxed(lean_object* v_x_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(v_x_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_908_, lean_object* v_x_909_, lean_object* v_head_910_, lean_object* v_x_911_, lean_object* v___y_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(v_tail_908_, v_x_909_, v_head_910_, v_x_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_920_) == 0)
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_923_, 0, v_x_921_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
else
{
lean_object* v_head_925_; lean_object* v_tail_926_; lean_object* v___f_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v_head_925_ = lean_ctor_get(v_x_920_, 0);
lean_inc_n(v_head_925_, 2);
v_tail_926_ = lean_ctor_get(v_x_920_, 1);
lean_inc(v_tail_926_);
lean_dec_ref_known(v_x_920_, 2);
v___f_927_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_927_, 0, v_tail_926_);
lean_closure_set(v___f_927_, 1, v_x_921_);
lean_closure_set(v___f_927_, 2, v_head_925_);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = 0;
if (lean_obj_tag(v_head_925_) == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec_ref_known(v_head_925_, 1);
v___x_930_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1));
v___x_931_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_928_, v___x_929_, v___x_930_, v___f_927_);
return v___x_931_;
}
else
{
lean_object* v_finished_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_945_; 
v_finished_932_ = lean_ctor_get(v_head_925_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v_head_925_);
if (v_isSharedCheck_945_ == 0)
{
v___x_934_ = v_head_925_;
v_isShared_935_ = v_isSharedCheck_945_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_finished_932_);
lean_dec(v_head_925_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_945_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v_finished_936_; lean_object* v___f_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v_finished_936_ = lean_ctor_get(v_finished_932_, 0);
lean_inc(v_finished_936_);
lean_dec_ref(v_finished_932_);
v___f_937_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2));
v___x_938_ = lean_st_ref_get(v_finished_936_);
lean_dec(v_finished_936_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_938_);
v___x_940_ = v___x_934_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_944_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
v___x_942_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_928_, v___x_929_, v___x_941_, v___f_937_);
v___x_943_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_928_, v___x_929_, v___x_942_, v___f_927_);
return v___x_943_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_946_, lean_object* v_x_947_, lean_object* v_head_948_, lean_object* v_x_949_){
_start:
{
if (lean_obj_tag(v_x_949_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_959_; 
lean_dec_ref(v_head_948_);
lean_dec(v_x_947_);
lean_dec(v_tail_946_);
v_a_951_ = lean_ctor_get(v_x_949_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v_x_949_);
if (v_isSharedCheck_959_ == 0)
{
v___x_953_ = v_x_949_;
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v_x_949_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_959_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_958_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
return v___x_957_;
}
}
}
else
{
lean_object* v_a_960_; uint8_t v___x_961_; 
v_a_960_ = lean_ctor_get(v_x_949_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v_x_949_, 1);
v___x_961_ = lean_unbox(v_a_960_);
lean_dec(v_a_960_);
if (v___x_961_ == 0)
{
lean_object* v___x_962_; 
lean_dec_ref(v_head_948_);
v___x_962_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_946_, v_x_947_);
return v___x_962_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_963_, 0, v_head_948_);
lean_ctor_set(v___x_963_, 1, v_x_947_);
v___x_964_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_946_, v___x_963_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___boxed(lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_965_, v_x_966_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(lean_object* v_a_969_, lean_object* v___x_970_, lean_object* v_x_971_){
_start:
{
if (lean_obj_tag(v_x_971_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
lean_dec(v___x_970_);
lean_dec(v_a_969_);
v_a_973_ = lean_ctor_get(v_x_971_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v_x_971_);
if (v_isSharedCheck_981_ == 0)
{
v___x_975_ = v_x_971_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v_x_971_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_980_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; 
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
}
}
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_998_; 
v_a_982_ = lean_ctor_get(v_x_971_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v_x_971_);
if (v_isSharedCheck_998_ == 0)
{
v___x_984_ = v_x_971_;
v_isShared_985_ = v_isSharedCheck_998_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v_x_971_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_998_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
uint8_t v___x_986_; 
v___x_986_ = l_List_isEmpty___redArg(v_a_969_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_989_; 
lean_dec(v___x_970_);
v___x_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_987_, 0, v_a_982_);
lean_ctor_set(v___x_987_, 1, v_a_969_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_987_);
v___x_989_ = v___x_984_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_987_);
v___x_989_ = v_reuseFailAlloc_991_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; 
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
lean_dec(v_a_969_);
v___x_992_ = l_List_reverse___redArg(v_a_982_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_970_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_993_);
v___x_995_ = v___x_984_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_997_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_996_; 
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed(lean_object* v_a_999_, lean_object* v___x_1000_, lean_object* v_x_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(v_a_999_, v___x_1000_, v_x_1001_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(lean_object* v___x_1004_, lean_object* v_eList_1005_, lean_object* v___f_1006_, lean_object* v_x_1007_){
_start:
{
if (lean_obj_tag(v_x_1007_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v___f_1006_);
lean_dec(v_eList_1005_);
lean_dec(v___x_1004_);
v_a_1009_ = lean_ctor_get(v_x_1007_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_x_1007_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1011_ = v_x_1007_;
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v_x_1007_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
else
{
lean_object* v_a_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_a_1018_ = lean_ctor_get(v_x_1007_, 0);
lean_inc(v_a_1018_);
lean_dec_ref_known(v_x_1007_, 1);
lean_inc(v___x_1004_);
v___f_1019_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1019_, 0, v_a_1018_);
lean_closure_set(v___f_1019_, 1, v___x_1004_);
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = 0;
v___x_1022_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_eList_1005_, v___x_1004_);
v___x_1023_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1020_, v___x_1021_, v___x_1022_, v___f_1006_);
v___x_1024_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1020_, v___x_1021_, v___x_1023_, v___f_1019_);
return v___x_1024_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed(lean_object* v___x_1025_, lean_object* v_eList_1026_, lean_object* v___f_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(v___x_1025_, v_eList_1026_, v___f_1027_, v_x_1028_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(lean_object* v_q_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_eList_1035_; lean_object* v_dList_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___f_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v_eList_1035_ = lean_ctor_get(v_q_1032_, 0);
lean_inc(v_eList_1035_);
v_dList_1036_ = lean_ctor_get(v_q_1032_, 1);
lean_inc(v_dList_1036_);
lean_dec_ref(v_q_1032_);
v___f_1037_ = ((lean_object*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0));
v___x_1038_ = lean_box(0);
v___f_1039_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1039_, 0, v___x_1038_);
lean_closure_set(v___f_1039_, 1, v_eList_1035_);
lean_closure_set(v___f_1039_, 2, v___f_1037_);
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = 0;
v___x_1042_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_dList_1036_, v___x_1038_);
v___x_1043_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1040_, v___x_1041_, v___x_1042_, v___f_1037_);
v___x_1044_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1040_, v___x_1041_, v___x_1043_, v___f_1039_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___boxed(lean_object* v_q_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_q_1045_, v___y_1046_);
lean_dec(v___y_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__8(lean_object* v___y_1049_, lean_object* v_x_1050_){
_start:
{
if (lean_obj_tag(v_x_1050_) == 0)
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1060_; 
v_a_1052_ = lean_ctor_get(v_x_1050_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_x_1050_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1054_ = v_x_1050_;
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v_x_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v_reason_1062_; lean_object* v_consumers_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_a_1061_ = lean_ctor_get(v_x_1050_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v_x_1050_, 1);
v_reason_1062_ = lean_ctor_get(v_a_1061_, 0);
lean_inc(v_reason_1062_);
v_consumers_1063_ = lean_ctor_get(v_a_1061_, 1);
lean_inc_ref(v_consumers_1063_);
lean_dec(v_a_1061_);
lean_inc(v___y_1049_);
v___f_1064_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1064_, 0, v_reason_1062_);
lean_closure_set(v___f_1064_, 1, v___y_1049_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = 0;
v___x_1067_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_consumers_1063_, v___y_1049_);
v___x_1068_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1065_, v___x_1066_, v___x_1067_, v___f_1064_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__8___boxed(lean_object* v___y_1069_, lean_object* v_x_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Std_CancellationToken_selector___lam__8(v___y_1069_, v_x_1070_);
lean_dec(v___y_1069_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__9(lean_object* v___y_1073_){
_start:
{
lean_object* v___f_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_inc(v___y_1073_);
v___f_1075_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1075_, 0, v___y_1073_);
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = 0;
v___x_1078_ = lean_st_ref_get(v___y_1073_);
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
v___x_1081_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1076_, v___x_1077_, v___x_1080_, v___f_1075_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__9___boxed(lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Std_CancellationToken_selector___lam__9(v___y_1082_);
lean_dec(v___y_1082_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector(lean_object* v_token_1087_){
_start:
{
lean_object* v___f_1088_; lean_object* v___f_1089_; lean_object* v___f_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_inc_ref_n(v_token_1087_, 2);
v___f_1088_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1088_, 0, v_token_1087_);
v___f_1089_ = ((lean_object*)(l_Std_CancellationToken_selector___closed__0));
v___f_1090_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__6___boxed), 3, 2);
lean_closure_set(v___f_1090_, 0, v_token_1087_);
lean_closure_set(v___f_1090_, 1, v___f_1089_);
v___f_1091_ = ((lean_object*)(l_Std_CancellationToken_selector___closed__1));
v___x_1092_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed), 5, 4);
lean_closure_set(v___x_1092_, 0, lean_box(0));
lean_closure_set(v___x_1092_, 1, lean_box(0));
lean_closure_set(v___x_1092_, 2, v_token_1087_);
lean_closure_set(v___x_1092_, 3, v___f_1091_);
v___x_1093_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1093_, 0, v___f_1090_);
lean_ctor_set(v___x_1093_, 1, v___f_1088_);
lean_ctor_set(v___x_1093_, 2, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(lean_object* v_x_1094_, lean_object* v_x_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_1094_, v_x_1095_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___boxed(lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(v_x_1099_, v_x_1100_, v___y_1101_);
lean_dec(v___y_1101_);
return v_res_1103_;
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

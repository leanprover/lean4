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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
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
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Std_CancellationReason_ctorIdx(v_x_6_);
lean_dec(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
if (lean_obj_tag(v_t_8_) == 3)
{
lean_object* v_msg_10_; lean_object* v___x_11_; 
v_msg_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_msg_10_);
lean_dec_ref_known(v_t_8_, 1);
v___x_11_ = lean_apply_1(v_k_9_, v_msg_10_);
return v___x_11_;
}
else
{
lean_dec(v_t_8_);
return v_k_9_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Std_CancellationReason_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_CancellationReason_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_deadline_elim___redArg(lean_object* v_t_24_, lean_object* v_deadline_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Std_CancellationReason_ctorElim___redArg(v_t_24_, v_deadline_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_deadline_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_deadline_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_CancellationReason_ctorElim___redArg(v_t_28_, v_deadline_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_shutdown_elim___redArg(lean_object* v_t_32_, lean_object* v_shutdown_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_CancellationReason_ctorElim___redArg(v_t_32_, v_shutdown_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_shutdown_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_shutdown_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_CancellationReason_ctorElim___redArg(v_t_36_, v_shutdown_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_cancel_elim___redArg(lean_object* v_t_40_, lean_object* v_cancel_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Std_CancellationReason_ctorElim___redArg(v_t_40_, v_cancel_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_cancel_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_cancel_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_CancellationReason_ctorElim___redArg(v_t_44_, v_cancel_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_custom_elim___redArg(lean_object* v_t_48_, lean_object* v_custom_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_CancellationReason_ctorElim___redArg(v_t_48_, v_custom_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationReason_custom_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_custom_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_CancellationReason_ctorElim___redArg(v_t_52_, v_custom_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Std_instReprCancellationReason_repr___closed__6(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_unsigned_to_nat(2u);
v___x_66_ = lean_nat_to_int(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Std_instReprCancellationReason_repr___closed__7(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(1u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_instReprCancellationReason_repr(lean_object* v_x_75_, lean_object* v_prec_76_){
_start:
{
lean_object* v___y_78_; lean_object* v___y_85_; lean_object* v___y_92_; 
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(1024u);
v___x_99_ = lean_nat_dec_le(v___x_98_, v_prec_76_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__6, &l_Std_instReprCancellationReason_repr___closed__6_once, _init_l_Std_instReprCancellationReason_repr___closed__6);
v___y_92_ = v___x_100_;
goto v___jp_91_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__7, &l_Std_instReprCancellationReason_repr___closed__7_once, _init_l_Std_instReprCancellationReason_repr___closed__7);
v___y_92_ = v___x_101_;
goto v___jp_91_;
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
v___x_104_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__6, &l_Std_instReprCancellationReason_repr___closed__6_once, _init_l_Std_instReprCancellationReason_repr___closed__6);
v___y_85_ = v___x_104_;
goto v___jp_84_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__7, &l_Std_instReprCancellationReason_repr___closed__7_once, _init_l_Std_instReprCancellationReason_repr___closed__7);
v___y_85_ = v___x_105_;
goto v___jp_84_;
}
}
case 2:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1024u);
v___x_107_ = lean_nat_dec_le(v___x_106_, v_prec_76_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__6, &l_Std_instReprCancellationReason_repr___closed__6_once, _init_l_Std_instReprCancellationReason_repr___closed__6);
v___y_78_ = v___x_108_;
goto v___jp_77_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__7, &l_Std_instReprCancellationReason_repr___closed__7_once, _init_l_Std_instReprCancellationReason_repr___closed__7);
v___y_78_ = v___x_109_;
goto v___jp_77_;
}
}
default: 
{
lean_object* v_msg_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_130_; 
v_msg_110_ = lean_ctor_get(v_x_75_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v_x_75_);
if (v_isSharedCheck_130_ == 0)
{
v___x_112_ = v_x_75_;
v_isShared_113_ = v_isSharedCheck_130_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_msg_110_);
lean_dec(v_x_75_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_130_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___y_115_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_unsigned_to_nat(1024u);
v___x_127_ = lean_nat_dec_le(v___x_126_, v_prec_76_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__6, &l_Std_instReprCancellationReason_repr___closed__6_once, _init_l_Std_instReprCancellationReason_repr___closed__6);
v___y_115_ = v___x_128_;
goto v___jp_114_;
}
else
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Std_instReprCancellationReason_repr___closed__7, &l_Std_instReprCancellationReason_repr___closed__7_once, _init_l_Std_instReprCancellationReason_repr___closed__7);
v___y_115_ = v___x_129_;
goto v___jp_114_;
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_116_ = ((lean_object*)(l_Std_instReprCancellationReason_repr___closed__10));
v___x_117_ = l_String_quote(v_msg_110_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_117_);
v___x_119_ = v___x_112_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_125_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_116_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
lean_inc(v___y_115_);
v___x_121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_121_, 0, v___y_115_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = 0;
v___x_123_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_123_, sizeof(void*)*1, v___x_122_);
v___x_124_ = l_Repr_addAppParen(v___x_123_, v_prec_76_);
return v___x_124_;
}
}
}
}
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = ((lean_object*)(l_Std_instReprCancellationReason_repr___closed__1));
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
v___x_86_ = ((lean_object*)(l_Std_instReprCancellationReason_repr___closed__3));
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
v___x_93_ = ((lean_object*)(l_Std_instReprCancellationReason_repr___closed__5));
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
LEAN_EXPORT lean_object* l_Std_instReprCancellationReason_repr___boxed(lean_object* v_x_131_, lean_object* v_prec_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_instReprCancellationReason_repr(v_x_131_, v_prec_132_);
lean_dec(v_prec_132_);
return v_res_133_;
}
}
LEAN_EXPORT uint8_t l_Std_instBEqCancellationReason_beq(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
switch(lean_obj_tag(v_x_136_))
{
case 0:
{
if (lean_obj_tag(v_x_137_) == 0)
{
uint8_t v___x_138_; 
v___x_138_ = 1;
return v___x_138_;
}
else
{
uint8_t v___x_139_; 
v___x_139_ = 0;
return v___x_139_;
}
}
case 1:
{
if (lean_obj_tag(v_x_137_) == 1)
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
}
case 2:
{
if (lean_obj_tag(v_x_137_) == 2)
{
uint8_t v___x_142_; 
v___x_142_ = 1;
return v___x_142_;
}
else
{
uint8_t v___x_143_; 
v___x_143_ = 0;
return v___x_143_;
}
}
default: 
{
if (lean_obj_tag(v_x_137_) == 3)
{
lean_object* v_msg_144_; lean_object* v_msg_145_; uint8_t v___x_146_; 
v_msg_144_ = lean_ctor_get(v_x_136_, 0);
v_msg_145_ = lean_ctor_get(v_x_137_, 0);
v___x_146_ = lean_string_dec_eq(v_msg_144_, v_msg_145_);
return v___x_146_;
}
else
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instBEqCancellationReason_beq___boxed(lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
uint8_t v_res_150_; lean_object* v_r_151_; 
v_res_150_ = l_Std_instBEqCancellationReason_beq(v_x_148_, v_x_149_);
lean_dec(v_x_149_);
lean_dec(v_x_148_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
LEAN_EXPORT lean_object* l_Std_instToStringCancellationReason___lam__0(lean_object* v_x_159_){
_start:
{
switch(lean_obj_tag(v_x_159_))
{
case 0:
{
lean_object* v___x_160_; 
v___x_160_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__0));
return v___x_160_;
}
case 1:
{
lean_object* v___x_161_; 
v___x_161_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__1));
return v___x_161_;
}
case 2:
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__2));
return v___x_162_;
}
default: 
{
lean_object* v_msg_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_msg_163_ = lean_ctor_get(v_x_159_, 0);
v___x_164_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__3));
v___x_165_ = lean_string_append(v___x_164_, v_msg_163_);
v___x_166_ = ((lean_object*)(l_Std_instToStringCancellationReason___lam__0___closed__4));
v___x_167_ = lean_string_append(v___x_165_, v___x_166_);
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_instToStringCancellationReason___lam__0___boxed(lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_instToStringCancellationReason___lam__0(v_x_168_);
lean_dec(v_x_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorIdx(lean_object* v_x_172_){
_start:
{
if (lean_obj_tag(v_x_172_) == 0)
{
lean_object* v___x_173_; 
v___x_173_ = lean_unsigned_to_nat(0u);
return v___x_173_;
}
else
{
lean_object* v___x_174_; 
v___x_174_ = lean_unsigned_to_nat(1u);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorIdx___boxed(lean_object* v_x_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_CancellationToken_Consumer_ctorIdx(v_x_175_);
lean_dec_ref(v_x_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim___redArg(lean_object* v_t_177_, lean_object* v_k_178_){
_start:
{
if (lean_obj_tag(v_t_177_) == 0)
{
lean_object* v_promise_179_; lean_object* v___x_180_; 
v_promise_179_ = lean_ctor_get(v_t_177_, 0);
lean_inc(v_promise_179_);
lean_dec_ref_known(v_t_177_, 1);
v___x_180_ = lean_apply_1(v_k_178_, v_promise_179_);
return v___x_180_;
}
else
{
lean_object* v_finished_181_; lean_object* v___x_182_; 
v_finished_181_ = lean_ctor_get(v_t_177_, 0);
lean_inc_ref(v_finished_181_);
lean_dec_ref_known(v_t_177_, 1);
v___x_182_ = lean_apply_1(v_k_178_, v_finished_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim(lean_object* v_motive_183_, lean_object* v_ctorIdx_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_k_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_185_, v_k_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_ctorElim___boxed(lean_object* v_motive_189_, lean_object* v_ctorIdx_190_, lean_object* v_t_191_, lean_object* v_h_192_, lean_object* v_k_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_CancellationToken_Consumer_ctorElim(v_motive_189_, v_ctorIdx_190_, v_t_191_, v_h_192_, v_k_193_);
lean_dec(v_ctorIdx_190_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_normal_elim___redArg(lean_object* v_t_195_, lean_object* v_normal_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_195_, v_normal_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_normal_elim(lean_object* v_motive_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_normal_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_199_, v_normal_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_select_elim___redArg(lean_object* v_t_203_, lean_object* v_select_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_203_, v_select_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_select_elim(lean_object* v_motive_206_, lean_object* v_t_207_, lean_object* v_h_208_, lean_object* v_select_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_207_, v_select_209_);
return v___x_210_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(lean_object* v_w_213_, lean_object* v_lose_214_){
_start:
{
lean_object* v_finished_216_; lean_object* v_promise_217_; lean_object* v___x_218_; uint8_t v___y_220_; uint8_t v___x_228_; 
v_finished_216_ = lean_ctor_get(v_w_213_, 0);
v_promise_217_ = lean_ctor_get(v_w_213_, 1);
v___x_218_ = lean_st_ref_take(v_finished_216_);
v___x_228_ = lean_unbox(v___x_218_);
lean_dec(v___x_218_);
if (v___x_228_ == 0)
{
uint8_t v___x_229_; 
v___x_229_ = 1;
v___y_220_ = v___x_229_;
goto v___jp_219_;
}
else
{
uint8_t v___x_230_; 
v___x_230_ = 0;
v___y_220_ = v___x_230_;
goto v___jp_219_;
}
v___jp_219_:
{
uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = 1;
v___x_222_ = lean_box(v___x_221_);
v___x_223_ = lean_st_ref_put(v_finished_216_, v___x_222_);
if (v___y_220_ == 0)
{
lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_224_ = lean_apply_1(v_lose_214_, lean_box(0));
v___x_225_ = lean_unbox(v___x_224_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; 
lean_dec_ref(v_lose_214_);
v___x_226_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_227_ = lean_io_promise_resolve(v___x_226_, v_promise_217_);
return v___y_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___boxed(lean_object* v_w_231_, lean_object* v_lose_232_, lean_object* v___y_233_){
_start:
{
uint8_t v_res_234_; lean_object* v_r_235_; 
v_res_234_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(v_w_231_, v_lose_232_);
lean_dec_ref(v_w_231_);
v_r_235_ = lean_box(v_res_234_);
return v_r_235_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationToken_Consumer_resolve___lam__0(uint8_t v___x_236_){
_start:
{
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_Consumer_resolve___lam__0___boxed(lean_object* v___x_238_, lean_object* v___y_239_){
_start:
{
uint8_t v___x_414__boxed_240_; uint8_t v_res_241_; lean_object* v_r_242_; 
v___x_414__boxed_240_ = lean_unbox(v___x_238_);
v_res_241_ = l_Std_CancellationToken_Consumer_resolve___lam__0(v___x_414__boxed_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationToken_Consumer_resolve(lean_object* v_c_246_){
_start:
{
if (lean_obj_tag(v_c_246_) == 0)
{
lean_object* v_promise_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_promise_248_ = lean_ctor_get(v_c_246_, 0);
v___x_249_ = lean_box(0);
v___x_250_ = lean_io_promise_resolve(v___x_249_, v_promise_248_);
v___x_251_ = 1;
return v___x_251_;
}
else
{
lean_object* v_finished_252_; lean_object* v_lose_253_; uint8_t v___x_254_; 
v_finished_252_ = lean_ctor_get(v_c_246_, 0);
v_lose_253_ = ((lean_object*)(l_Std_CancellationToken_Consumer_resolve___closed__0));
v___x_254_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(v_finished_252_, v_lose_253_);
return v___x_254_;
}
}
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
LEAN_EXPORT lean_object* l_Std_CancellationToken_new(){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_obj_once(&l_Std_CancellationToken_new___closed__1, &l_Std_CancellationToken_new___closed__1_once, _init_l_Std_CancellationToken_new___closed__1);
v___x_265_ = l_Std_Mutex_new___redArg(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_new___boxed(lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Std_CancellationToken_new();
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(lean_object* v_mutex_268_, lean_object* v_k_269_){
_start:
{
lean_object* v_ref_271_; lean_object* v_mutex_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_ref_271_ = lean_ctor_get(v_mutex_268_, 0);
lean_inc(v_ref_271_);
v_mutex_272_ = lean_ctor_get(v_mutex_268_, 1);
lean_inc(v_mutex_272_);
lean_dec_ref(v_mutex_268_);
v___x_273_ = lean_io_basemutex_lock(v_mutex_272_);
v___x_274_ = lean_apply_2(v_k_269_, v_ref_271_, lean_box(0));
v___x_275_ = lean_io_basemutex_unlock(v_mutex_272_);
lean_dec(v_mutex_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg___boxed(lean_object* v_mutex_276_, lean_object* v_k_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_mutex_276_, v_k_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_mutex_282_, lean_object* v_k_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_mutex_282_, v_k_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___boxed(lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_, lean_object* v_mutex_288_, lean_object* v_k_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(v_00_u03b1_286_, v_00_u03b2_287_, v_mutex_288_, v_k_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(lean_object* v_a_292_){
_start:
{
lean_object* v___x_294_; 
lean_inc_ref(v_a_292_);
v___x_294_ = l_Std_Queue_dequeue_x3f___redArg(v_a_292_);
if (lean_obj_tag(v___x_294_) == 1)
{
lean_object* v_val_295_; lean_object* v_fst_296_; lean_object* v_snd_297_; uint8_t v___x_298_; 
lean_dec_ref(v_a_292_);
v_val_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_val_295_);
lean_dec_ref_known(v___x_294_, 1);
v_fst_296_ = lean_ctor_get(v_val_295_, 0);
lean_inc(v_fst_296_);
v_snd_297_ = lean_ctor_get(v_val_295_, 1);
lean_inc(v_snd_297_);
lean_dec(v_val_295_);
v___x_298_ = l_Std_CancellationToken_Consumer_resolve(v_fst_296_);
lean_dec(v_fst_296_);
v_a_292_ = v_snd_297_;
goto _start;
}
else
{
lean_dec(v___x_294_);
return v_a_292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg___boxed(lean_object* v_a_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___lam__0(lean_object* v_reason_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; lean_object* v_reason_307_; 
v___x_306_ = lean_st_ref_get(v___y_304_);
v_reason_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_reason_307_);
if (lean_obj_tag(v_reason_307_) == 0)
{
lean_object* v_consumers_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_320_; 
v_consumers_308_ = lean_ctor_get(v___x_306_, 1);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_306_, 0);
lean_dec(v_unused_321_);
v___x_310_ = v___x_306_;
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_consumers_308_);
lean_dec(v___x_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_320_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_st_315_; 
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v_reason_303_);
v___x_313_ = lean_obj_once(&l_Std_CancellationToken_new___closed__0, &l_Std_CancellationToken_new___closed__0_once, _init_l_Std_CancellationToken_new___closed__0);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v___x_313_);
lean_ctor_set(v___x_310_, 0, v___x_312_);
v_st_315_ = v___x_310_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_313_);
v_st_315_ = v_reuseFailAlloc_319_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_consumers_308_);
lean_dec_ref(v___x_316_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_st_ref_swap(v___y_304_, v_st_315_);
lean_dec(v___x_318_);
return v___x_317_;
}
}
}
else
{
lean_object* v___x_322_; 
lean_dec_ref_known(v_reason_307_, 1);
lean_dec(v___x_306_);
lean_dec(v_reason_303_);
v___x_322_ = lean_box(0);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___lam__0___boxed(lean_object* v_reason_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_CancellationToken_cancel___lam__0(v_reason_323_, v___y_324_);
lean_dec(v___y_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel(lean_object* v_x_327_, lean_object* v_reason_328_){
_start:
{
lean_object* v___f_330_; lean_object* v___x_331_; 
v___f_330_ = lean_alloc_closure((void*)(l_Std_CancellationToken_cancel___lam__0___boxed), 3, 1);
lean_closure_set(v___f_330_, 0, v_reason_328_);
v___x_331_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_327_, v___f_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___boxed(lean_object* v_x_332_, lean_object* v_reason_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_CancellationToken_cancel(v_x_332_, v_reason_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0(lean_object* v_inst_336_, lean_object* v_a_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_337_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0___boxed(lean_object* v_inst_341_, lean_object* v_a_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Init_While_0__repeatM_erased___at___00Std_CancellationToken_cancel_spec__0(v_inst_341_, v_a_342_, v___y_343_);
lean_dec(v___y_343_);
return v_res_345_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationToken_isCancelled___lam__0(lean_object* v___y_346_){
_start:
{
lean_object* v___x_348_; lean_object* v_reason_349_; 
v___x_348_ = lean_st_ref_get(v___y_346_);
v_reason_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_reason_349_);
lean_dec(v___x_348_);
if (lean_obj_tag(v_reason_349_) == 0)
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
else
{
uint8_t v___x_351_; 
lean_dec_ref_known(v_reason_349_, 1);
v___x_351_ = 1;
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_isCancelled___lam__0___boxed(lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
uint8_t v_res_354_; lean_object* v_r_355_; 
v_res_354_ = l_Std_CancellationToken_isCancelled___lam__0(v___y_352_);
lean_dec(v___y_352_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationToken_isCancelled(lean_object* v_x_357_){
_start:
{
lean_object* v___f_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___f_359_ = ((lean_object*)(l_Std_CancellationToken_isCancelled___closed__0));
v___x_360_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_357_, v___f_359_);
v___x_361_ = lean_unbox(v___x_360_);
lean_dec(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_isCancelled___boxed(lean_object* v_x_362_, lean_object* v_a_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Std_CancellationToken_isCancelled(v_x_362_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___lam__0(lean_object* v___y_366_){
_start:
{
lean_object* v___x_368_; lean_object* v_reason_369_; 
v___x_368_ = lean_st_ref_get(v___y_366_);
v_reason_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_reason_369_);
lean_dec(v___x_368_);
return v_reason_369_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___lam__0___boxed(lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_CancellationToken_getCancellationReason___lam__0(v___y_370_);
lean_dec(v___y_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason(lean_object* v_x_374_){
_start:
{
lean_object* v___f_376_; lean_object* v___x_377_; 
v___f_376_ = ((lean_object*)(l_Std_CancellationToken_getCancellationReason___closed__0));
v___x_377_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_374_, v___f_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___boxed(lean_object* v_x_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_CancellationToken_getCancellationReason(v_x_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(lean_object* v_mutex_381_, lean_object* v_k_382_){
_start:
{
lean_object* v_ref_384_; lean_object* v_mutex_385_; lean_object* v___x_386_; lean_object* v_r_387_; 
v_ref_384_ = lean_ctor_get(v_mutex_381_, 0);
lean_inc(v_ref_384_);
v_mutex_385_ = lean_ctor_get(v_mutex_381_, 1);
lean_inc(v_mutex_385_);
lean_dec_ref(v_mutex_381_);
v___x_386_ = lean_io_basemutex_lock(v_mutex_385_);
v_r_387_ = lean_apply_2(v_k_382_, v_ref_384_, lean_box(0));
if (lean_obj_tag(v_r_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_396_; 
v_a_388_ = lean_ctor_get(v_r_387_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v_r_387_);
if (v_isSharedCheck_396_ == 0)
{
v___x_390_ = v_r_387_;
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v_r_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_396_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = lean_io_basemutex_unlock(v_mutex_385_);
lean_dec(v_mutex_385_);
if (v_isShared_391_ == 0)
{
v___x_394_ = v___x_390_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_388_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v_a_397_ = lean_ctor_get(v_r_387_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_r_387_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v_r_387_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v_r_387_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_io_basemutex_unlock(v_mutex_385_);
lean_dec(v_mutex_385_);
if (v_isShared_400_ == 0)
{
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_397_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg___boxed(lean_object* v_mutex_406_, lean_object* v_k_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_mutex_406_, v_k_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v_mutex_412_, lean_object* v_k_413_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_mutex_412_, v_k_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___boxed(lean_object* v_00_u03b1_416_, lean_object* v_00_u03b2_417_, lean_object* v_mutex_418_, lean_object* v_k_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(v_00_u03b1_416_, v_00_u03b2_417_, v_mutex_418_, v_k_419_);
return v_res_421_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__1(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Std_CancellationToken_wait___lam__0___closed__0));
v___x_424_ = lean_mk_io_user_error(v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__2(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__1, &l_Std_CancellationToken_wait___lam__0___closed__1_once, _init_l_Std_CancellationToken_wait___lam__0___closed__1);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__3(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__2, &l_Std_CancellationToken_wait___lam__0___closed__2_once, _init_l_Std_CancellationToken_wait___lam__0___closed__2);
v___x_428_ = lean_task_pure(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__4(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_430_ = lean_task_pure(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__0(lean_object* v_a_431_){
_start:
{
if (lean_obj_tag(v_a_431_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__3, &l_Std_CancellationToken_wait___lam__0___closed__3_once, _init_l_Std_CancellationToken_wait___lam__0___closed__3);
return v___x_433_;
}
else
{
lean_object* v___x_434_; 
v___x_434_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__4, &l_Std_CancellationToken_wait___lam__0___closed__4_once, _init_l_Std_CancellationToken_wait___lam__0___closed__4);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__0___boxed(lean_object* v_a_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_CancellationToken_wait___lam__0(v_a_435_);
lean_dec(v_a_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__1(lean_object* v___f_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; lean_object* v_reason_442_; 
v___x_441_ = lean_st_ref_get(v___y_439_);
v_reason_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_reason_442_);
lean_dec(v___x_441_);
if (lean_obj_tag(v_reason_442_) == 0)
{
uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v_reason_446_; lean_object* v_consumers_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_461_; 
v___x_443_ = 0;
v___x_444_ = lean_io_promise_new();
v___x_445_ = lean_st_ref_take(v___y_439_);
v_reason_446_ = lean_ctor_get(v___x_445_, 0);
v_consumers_447_ = lean_ctor_get(v___x_445_, 1);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_461_ == 0)
{
v___x_449_ = v___x_445_;
v_isShared_450_ = v_isSharedCheck_461_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_consumers_447_);
lean_inc(v_reason_446_);
lean_dec(v___x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_461_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
lean_inc(v___x_444_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_444_);
v___x_452_ = l_Std_Queue_enqueue___redArg(v___x_451_, v_consumers_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_reason_446_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_452_);
v___x_454_ = v_reuseFailAlloc_460_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = lean_st_ref_put(v___y_439_, v___x_454_);
v___x_456_ = lean_io_promise_result_opt(v___x_444_);
lean_dec(v___x_444_);
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_io_bind_task(v___x_456_, v___f_438_, v___x_457_, v___x_443_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
}
else
{
lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_469_; 
lean_dec_ref(v___f_438_);
v_isSharedCheck_469_ = !lean_is_exclusive(v_reason_442_);
if (v_isSharedCheck_469_ == 0)
{
lean_object* v_unused_470_; 
v_unused_470_ = lean_ctor_get(v_reason_442_, 0);
lean_dec(v_unused_470_);
v___x_463_ = v_reason_442_;
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
else
{
lean_dec(v_reason_442_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_469_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_465_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__4, &l_Std_CancellationToken_wait___lam__0___closed__4_once, _init_l_Std_CancellationToken_wait___lam__0___closed__4);
if (v_isShared_464_ == 0)
{
lean_ctor_set_tag(v___x_463_, 0);
lean_ctor_set(v___x_463_, 0, v___x_465_);
v___x_467_ = v___x_463_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__1___boxed(lean_object* v___f_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_CancellationToken_wait___lam__1(v___f_471_, v___y_472_);
lean_dec(v___y_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait(lean_object* v_x_478_){
_start:
{
lean_object* v___f_480_; lean_object* v___x_481_; 
v___f_480_ = ((lean_object*)(l_Std_CancellationToken_wait___closed__1));
v___x_481_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_x_478_, v___f_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___boxed(lean_object* v_x_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_CancellationToken_wait(v_x_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(uint8_t v___x_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_496_; 
v_a_488_ = lean_ctor_get(v_x_486_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_x_486_);
if (v_isSharedCheck_496_ == 0)
{
v___x_490_ = v_x_486_;
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v_x_486_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_495_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; 
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
}
else
{
lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_505_; 
v_isSharedCheck_505_ = !lean_is_exclusive(v_x_486_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_x_486_, 0);
lean_dec(v_unused_506_);
v___x_498_ = v_x_486_;
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
else
{
lean_dec(v_x_486_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_box(v___x_485_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_504_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; 
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0___boxed(lean_object* v___x_507_, lean_object* v_x_508_, lean_object* v___y_509_){
_start:
{
uint8_t v___x_6594__boxed_510_; lean_object* v_res_511_; 
v___x_6594__boxed_510_ = lean_unbox(v___x_507_);
v_res_511_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(v___x_6594__boxed_510_, v_x_508_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(lean_object* v_lose_512_, lean_object* v___y_513_, lean_object* v_promise_514_, lean_object* v___f_515_, lean_object* v_x_516_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v___x_518_; 
lean_dec_ref(v___f_515_);
lean_dec_ref(v_lose_512_);
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v_x_516_);
return v___x_518_;
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_534_; 
v_a_519_ = lean_ctor_get(v_x_516_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_534_ == 0)
{
v___x_521_ = v_x_516_;
v_isShared_522_ = v_isSharedCheck_534_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v_x_516_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_534_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint8_t v___x_523_; 
v___x_523_ = lean_unbox(v_a_519_);
lean_dec(v_a_519_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_del_object(v___x_521_);
lean_dec_ref(v___f_515_);
lean_inc(v___y_513_);
v___x_524_ = lean_apply_2(v_lose_512_, v___y_513_, lean_box(0));
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
lean_dec_ref(v_lose_512_);
v___x_525_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = 0;
v___x_528_ = lean_io_promise_resolve(v___x_525_, v_promise_514_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_528_);
v___x_530_ = v___x_521_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_533_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_526_, v___x_527_, v___x_531_, v___f_515_);
return v___x_532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed(lean_object* v_lose_535_, lean_object* v___y_536_, lean_object* v_promise_537_, lean_object* v___f_538_, lean_object* v_x_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(v_lose_535_, v___y_536_, v_promise_537_, v___f_538_, v_x_539_);
lean_dec(v_promise_537_);
lean_dec(v___y_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(lean_object* v_w_545_, lean_object* v_lose_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_finished_549_; lean_object* v_promise_550_; uint8_t v___x_551_; lean_object* v___f_552_; lean_object* v___f_553_; lean_object* v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; uint8_t v___y_558_; uint8_t v___x_565_; 
v_finished_549_ = lean_ctor_get(v_w_545_, 0);
lean_inc(v_finished_549_);
v_promise_550_ = lean_ctor_get(v_w_545_, 1);
lean_inc(v_promise_550_);
lean_dec_ref(v_w_545_);
v___x_551_ = 1;
v___f_552_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0));
lean_inc(v___y_547_);
v___f_553_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed), 6, 4);
lean_closure_set(v___f_553_, 0, v_lose_546_);
lean_closure_set(v___f_553_, 1, v___y_547_);
lean_closure_set(v___f_553_, 2, v_promise_550_);
lean_closure_set(v___f_553_, 3, v___f_552_);
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = 0;
v___x_556_ = lean_st_ref_take(v_finished_549_);
v___x_565_ = lean_unbox(v___x_556_);
lean_dec(v___x_556_);
if (v___x_565_ == 0)
{
v___y_558_ = v___x_551_;
goto v___jp_557_;
}
else
{
v___y_558_ = v___x_555_;
goto v___jp_557_;
}
v___jp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_559_ = lean_box(v___x_551_);
v___x_560_ = lean_st_ref_put(v_finished_549_, v___x_559_);
lean_dec(v_finished_549_);
v___x_561_ = lean_box(v___y_558_);
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
v___x_564_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_554_, v___x_555_, v___x_563_, v___f_553_);
return v___x_564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___boxed(lean_object* v_w_566_, lean_object* v_lose_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(v_w_566_, v_lose_567_, v___y_568_);
lean_dec(v___y_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(lean_object* v___y_571_){
_start:
{
if (lean_obj_tag(v___y_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_a_572_ = lean_ctor_get(v___y_571_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___y_571_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___y_571_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___y_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_588_; 
v_a_580_ = lean_ctor_get(v___y_571_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___y_571_);
if (v_isSharedCheck_588_ == 0)
{
v___x_582_ = v___y_571_;
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___y_571_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v_fst_584_; lean_object* v___x_586_; 
v_fst_584_ = lean_ctor_get(v_a_580_, 0);
lean_inc(v_fst_584_);
lean_dec(v_a_580_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v_fst_584_);
v___x_586_ = v___x_582_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_fst_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(lean_object* v_mutex_589_, lean_object* v_x_590_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_io_basemutex_unlock(v_mutex_589_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed(lean_object* v_mutex_595_, lean_object* v_x_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(v_mutex_595_, v_x_596_);
lean_dec(v_x_596_);
lean_dec(v_mutex_595_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(lean_object* v_k_599_, lean_object* v_ref_600_, lean_object* v_x_601_){
_start:
{
if (lean_obj_tag(v_x_601_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_ref_600_);
lean_dec_ref(v_k_599_);
v_a_603_ = lean_ctor_get(v_x_601_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_611_ == 0)
{
v___x_605_ = v_x_601_;
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v_x_601_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_611_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_610_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
}
else
{
lean_object* v___x_612_; 
lean_dec_ref_known(v_x_601_, 1);
v___x_612_ = lean_apply_2(v_k_599_, v_ref_600_, lean_box(0));
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed(lean_object* v_k_613_, lean_object* v_ref_614_, lean_object* v_x_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(v_k_613_, v_ref_614_, v_x_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(lean_object* v_mutex_618_, lean_object* v___f_619_){
_start:
{
lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = 0;
v___x_623_ = lean_io_basemutex_lock(v_mutex_618_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_621_, v___x_622_, v___x_625_, v___f_619_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3___boxed(lean_object* v_mutex_627_, lean_object* v___f_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(v_mutex_627_, v___f_628_);
lean_dec(v_mutex_627_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(lean_object* v_mutex_632_, lean_object* v_k_633_){
_start:
{
lean_object* v_ref_635_; lean_object* v_mutex_636_; lean_object* v___f_637_; lean_object* v___f_638_; lean_object* v___f_639_; lean_object* v___f_640_; lean_object* v___x_641_; uint8_t v___x_642_; lean_object* v___x_643_; lean_object* v___y_645_; 
v_ref_635_ = lean_ctor_get(v_mutex_632_, 0);
lean_inc(v_ref_635_);
v_mutex_636_ = lean_ctor_get(v_mutex_632_, 1);
lean_inc_n(v_mutex_636_, 2);
lean_dec_ref(v_mutex_632_);
v___f_637_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0));
v___f_638_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_638_, 0, v_mutex_636_);
v___f_639_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_639_, 0, v_k_633_);
lean_closure_set(v___f_639_, 1, v_ref_635_);
v___f_640_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_640_, 0, v_mutex_636_);
lean_closure_set(v___f_640_, 1, v___f_639_);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = 0;
v___x_643_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_640_, v___f_638_, v___x_641_, v___x_642_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_647_; 
v_a_647_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v___x_643_, 1);
if (lean_obj_tag(v_a_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_a_648_ = lean_ctor_get(v_a_647_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v_a_647_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v_a_647_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v_a_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
v___y_645_ = v___x_653_;
goto v___jp_644_;
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_664_; 
v_a_656_ = lean_ctor_get(v_a_647_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_a_647_);
if (v_isSharedCheck_664_ == 0)
{
v___x_658_ = v_a_647_;
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v_a_647_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_664_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v_fst_660_; lean_object* v___x_662_; 
v_fst_660_ = lean_ctor_get(v_a_656_, 0);
lean_inc(v_fst_660_);
lean_dec(v_a_656_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_fst_660_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_fst_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
v___y_645_ = v___x_662_;
goto v___jp_644_;
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_673_; 
v_a_665_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_673_ == 0)
{
v___x_667_ = v___x_643_;
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_643_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_task_map(v___f_637_, v_a_665_, v___x_641_, v___x_642_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
v___jp_644_:
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___y_645_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___boxed(lean_object* v_mutex_674_, lean_object* v_k_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_mutex_674_, v_k_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_mutex_680_, lean_object* v_k_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_mutex_680_, v_k_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed(lean_object* v_00_u03b1_684_, lean_object* v_00_u03b2_685_, lean_object* v_mutex_686_, lean_object* v_k_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(v_00_u03b1_684_, v_00_u03b2_685_, v_mutex_686_, v_k_687_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__0(uint8_t v___x_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = lean_box(v___x_690_);
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__0___boxed(lean_object* v___x_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
uint8_t v___x_6910__boxed_699_; lean_object* v_res_700_; 
v___x_6910__boxed_699_ = lean_unbox(v___x_696_);
v_res_700_ = l_Std_CancellationToken_selector___lam__0(v___x_6910__boxed_699_, v___y_697_);
lean_dec(v___y_697_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__1(lean_object* v___x_701_, lean_object* v___y_702_){
_start:
{
if (lean_obj_tag(v___y_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_a_703_ = lean_ctor_get(v___y_702_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___y_702_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___y_702_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___y_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
v_isSharedCheck_717_ = !lean_is_exclusive(v___y_702_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; 
v_unused_718_ = lean_ctor_get(v___y_702_, 0);
lean_dec(v_unused_718_);
v___x_712_ = v___y_702_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_dec(v___y_702_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_701_);
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_701_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__2(lean_object* v___y_726_, lean_object* v_waiter_727_, lean_object* v_x_728_){
_start:
{
if (lean_obj_tag(v_x_728_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v_waiter_727_);
v_a_730_ = lean_ctor_get(v_x_728_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v_x_728_);
if (v_isSharedCheck_738_ == 0)
{
v___x_732_ = v_x_728_;
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v_x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_738_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_737_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
}
else
{
lean_object* v_a_739_; lean_object* v_reason_740_; 
v_a_739_ = lean_ctor_get(v_x_728_, 0);
lean_inc(v_a_739_);
lean_dec_ref_known(v_x_728_, 1);
v_reason_740_ = lean_ctor_get(v_a_739_, 0);
lean_inc(v_reason_740_);
lean_dec(v_a_739_);
if (lean_obj_tag(v_reason_740_) == 0)
{
lean_object* v___x_741_; lean_object* v_reason_742_; lean_object* v_consumers_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_754_; 
v___x_741_ = lean_st_ref_take(v___y_726_);
v_reason_742_ = lean_ctor_get(v___x_741_, 0);
v_consumers_743_ = lean_ctor_get(v___x_741_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_754_ == 0)
{
v___x_745_ = v___x_741_;
v_isShared_746_ = v_isSharedCheck_754_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_consumers_743_);
lean_inc(v_reason_742_);
lean_dec(v___x_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_754_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v_waiter_727_);
v___x_748_ = l_Std_Queue_enqueue___redArg(v___x_747_, v_consumers_743_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v___x_748_);
v___x_750_ = v___x_745_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_reason_742_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_748_);
v___x_750_ = v_reuseFailAlloc_753_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_st_ref_put(v___y_726_, v___x_750_);
v___x_752_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__0));
return v___x_752_;
}
}
}
else
{
lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_787_; 
v_isSharedCheck_787_ = !lean_is_exclusive(v_reason_740_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; 
v_unused_788_ = lean_ctor_get(v_reason_740_, 0);
lean_dec(v_unused_788_);
v___x_756_ = v_reason_740_;
v_isShared_757_ = v_isSharedCheck_787_;
goto v_resetjp_755_;
}
else
{
lean_dec(v_reason_740_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_787_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
uint8_t v___x_758_; lean_object* v___f_759_; lean_object* v___f_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___y_764_; 
v___x_758_ = 0;
v___f_759_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__1));
v___f_760_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__2));
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(v_waiter_727_, v___f_759_, v___y_726_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_768_; 
v_a_768_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_762_, 1);
if (lean_obj_tag(v_a_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
v_a_769_ = lean_ctor_get(v_a_768_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v_a_768_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v_a_768_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v_a_768_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
v___y_764_ = v___x_774_;
goto v___jp_763_;
}
}
}
else
{
lean_object* v___x_777_; 
lean_dec_ref_known(v_a_768_, 1);
v___x_777_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___y_764_ = v___x_777_;
goto v___jp_763_;
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_786_; 
lean_del_object(v___x_756_);
v_a_778_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_786_ == 0)
{
v___x_780_ = v___x_762_;
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_762_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_786_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_task_map(v___f_760_, v_a_778_, v___x_761_, v___x_758_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_782_);
v___x_784_ = v___x_780_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
v___jp_763_:
{
lean_object* v___x_766_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 0);
lean_ctor_set(v___x_756_, 0, v___y_764_);
v___x_766_ = v___x_756_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v___y_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__2___boxed(lean_object* v___y_789_, lean_object* v_waiter_790_, lean_object* v_x_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_CancellationToken_selector___lam__2(v___y_789_, v_waiter_790_, v_x_791_);
lean_dec(v___y_789_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__3(lean_object* v_waiter_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___f_797_; lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_inc(v___y_795_);
v___f_797_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__2___boxed), 4, 2);
lean_closure_set(v___f_797_, 0, v___y_795_);
lean_closure_set(v___f_797_, 1, v_waiter_794_);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = 0;
v___x_800_ = lean_st_ref_get(v___y_795_);
v___x_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
v___x_803_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_798_, v___x_799_, v___x_802_, v___f_797_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__3___boxed(lean_object* v_waiter_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_CancellationToken_selector___lam__3(v_waiter_804_, v___y_805_);
lean_dec(v___y_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__4(lean_object* v_token_808_, lean_object* v_waiter_809_){
_start:
{
lean_object* v___f_811_; lean_object* v___x_812_; 
v___f_811_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_811_, 0, v_waiter_809_);
v___x_812_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_token_808_, v___f_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__4___boxed(lean_object* v_token_813_, lean_object* v_waiter_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_CancellationToken_selector___lam__4(v_token_813_, v_waiter_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__5(lean_object* v_x_827_){
_start:
{
if (lean_obj_tag(v_x_827_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_837_; 
v_a_829_ = lean_ctor_get(v_x_827_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v_x_827_);
if (v_isSharedCheck_837_ == 0)
{
v___x_831_ = v_x_827_;
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v_x_827_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_836_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; 
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
}
else
{
lean_object* v_a_838_; uint8_t v___x_839_; 
v_a_838_ = lean_ctor_get(v_x_827_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v_x_827_, 1);
v___x_839_ = lean_unbox(v_a_838_);
lean_dec(v_a_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
v___x_840_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__5___closed__1));
return v___x_840_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__5___closed__4));
return v___x_841_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__5___boxed(lean_object* v_x_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_CancellationToken_selector___lam__5(v_x_842_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__6(lean_object* v_token_845_, lean_object* v___f_846_){
_start:
{
lean_object* v___x_848_; uint8_t v___x_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = 0;
v___x_850_ = l_Std_CancellationToken_isCancelled(v_token_845_);
v___x_851_ = lean_box(v___x_850_);
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
v___x_854_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_848_, v___x_849_, v___x_853_, v___f_846_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__6___boxed(lean_object* v_token_855_, lean_object* v___f_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_CancellationToken_selector___lam__6(v_token_855_, v___f_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__7(lean_object* v_reason_859_, lean_object* v___y_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
lean_dec(v_reason_859_);
v_a_863_ = lean_ctor_get(v_x_861_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v_x_861_);
if (v_isSharedCheck_871_ == 0)
{
v___x_865_ = v_x_861_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v_x_861_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
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
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_870_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; 
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
return v___x_869_;
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_a_872_ = lean_ctor_get(v_x_861_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v_x_861_, 1);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v_reason_859_);
lean_ctor_set(v___x_873_, 1, v_a_872_);
v___x_874_ = lean_st_ref_swap(v___y_860_, v___x_873_);
lean_dec(v___x_874_);
v___x_875_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__0));
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__7___boxed(lean_object* v_reason_876_, lean_object* v___y_877_, lean_object* v_x_878_, lean_object* v___y_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_CancellationToken_selector___lam__7(v_reason_876_, v___y_877_, v_x_878_);
lean_dec(v___y_877_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_object* v___x_883_; 
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v_x_881_);
return v___x_883_;
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_893_; 
v_a_884_ = lean_ctor_get(v_x_881_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v_x_881_);
if (v_isSharedCheck_893_ == 0)
{
v___x_886_ = v_x_881_;
v_isShared_887_ = v_isSharedCheck_893_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v_x_881_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_893_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = l_List_reverse___redArg(v_a_884_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 0, v___x_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_892_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; 
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0___boxed(lean_object* v_x_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(v_x_894_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(lean_object* v_x_897_){
_start:
{
uint8_t v___y_900_; 
if (lean_obj_tag(v_x_897_) == 0)
{
lean_object* v___x_904_; 
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v_x_897_);
return v___x_904_;
}
else
{
lean_object* v_a_905_; uint8_t v___x_906_; 
v_a_905_ = lean_ctor_get(v_x_897_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v_x_897_, 1);
v___x_906_ = lean_unbox(v_a_905_);
lean_dec(v_a_905_);
if (v___x_906_ == 0)
{
uint8_t v___x_907_; 
v___x_907_ = 1;
v___y_900_ = v___x_907_;
goto v___jp_899_;
}
else
{
uint8_t v___x_908_; 
v___x_908_ = 0;
v___y_900_ = v___x_908_;
goto v___jp_899_;
}
}
v___jp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_box(v___y_900_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1___boxed(lean_object* v_x_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(v_x_909_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_912_, lean_object* v_x_913_, lean_object* v_head_914_, lean_object* v_x_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(v_tail_912_, v_x_913_, v_head_914_, v_x_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(lean_object* v_x_924_, lean_object* v_x_925_){
_start:
{
if (lean_obj_tag(v_x_924_) == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_927_, 0, v_x_925_);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
else
{
lean_object* v_head_929_; lean_object* v_tail_930_; lean_object* v___f_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v_head_929_ = lean_ctor_get(v_x_924_, 0);
lean_inc_n(v_head_929_, 2);
v_tail_930_ = lean_ctor_get(v_x_924_, 1);
lean_inc(v_tail_930_);
lean_dec_ref_known(v_x_924_, 2);
v___f_931_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_931_, 0, v_tail_930_);
lean_closure_set(v___f_931_, 1, v_x_925_);
lean_closure_set(v___f_931_, 2, v_head_929_);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = 0;
if (lean_obj_tag(v_head_929_) == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref_known(v_head_929_, 1);
v___x_934_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1));
v___x_935_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_932_, v___x_933_, v___x_934_, v___f_931_);
return v___x_935_;
}
else
{
lean_object* v_finished_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_949_; 
v_finished_936_ = lean_ctor_get(v_head_929_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v_head_929_);
if (v_isSharedCheck_949_ == 0)
{
v___x_938_ = v_head_929_;
v_isShared_939_ = v_isSharedCheck_949_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_finished_936_);
lean_dec(v_head_929_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_949_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_finished_940_; lean_object* v___f_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v_finished_940_ = lean_ctor_get(v_finished_936_, 0);
lean_inc(v_finished_940_);
lean_dec_ref(v_finished_936_);
v___f_941_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2));
v___x_942_ = lean_st_ref_get(v_finished_940_);
lean_dec(v_finished_940_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_942_);
v___x_944_ = v___x_938_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
v___x_944_ = v_reuseFailAlloc_948_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
v___x_946_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_932_, v___x_933_, v___x_945_, v___f_941_);
v___x_947_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_932_, v___x_933_, v___x_946_, v___f_931_);
return v___x_947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_950_, lean_object* v_x_951_, lean_object* v_head_952_, lean_object* v_x_953_){
_start:
{
if (lean_obj_tag(v_x_953_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_963_; 
lean_dec_ref(v_head_952_);
lean_dec(v_x_951_);
lean_dec(v_tail_950_);
v_a_955_ = lean_ctor_get(v_x_953_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_x_953_);
if (v_isSharedCheck_963_ == 0)
{
v___x_957_ = v_x_953_;
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v_x_953_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_963_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_962_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_961_; 
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
return v___x_961_;
}
}
}
else
{
lean_object* v_a_964_; uint8_t v___x_965_; 
v_a_964_ = lean_ctor_get(v_x_953_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v_x_953_, 1);
v___x_965_ = lean_unbox(v_a_964_);
lean_dec(v_a_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
lean_dec_ref(v_head_952_);
v___x_966_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_950_, v_x_951_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_967_, 0, v_head_952_);
lean_ctor_set(v___x_967_, 1, v_x_951_);
v___x_968_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_950_, v___x_967_);
return v___x_968_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___boxed(lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_969_, v_x_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(lean_object* v_a_973_, lean_object* v___x_974_, lean_object* v_x_975_){
_start:
{
if (lean_obj_tag(v_x_975_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_985_; 
lean_dec(v___x_974_);
lean_dec(v_a_973_);
v_a_977_ = lean_ctor_get(v_x_975_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_985_ == 0)
{
v___x_979_ = v_x_975_;
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v_x_975_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_985_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_984_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1002_; 
v_a_986_ = lean_ctor_get(v_x_975_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_x_975_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_988_ = v_x_975_;
v_isShared_989_ = v_isSharedCheck_1002_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v_x_975_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1002_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
uint8_t v___x_990_; 
v___x_990_ = l_List_isEmpty___redArg(v_a_973_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; lean_object* v___x_993_; 
lean_dec(v___x_974_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_a_986_);
lean_ctor_set(v___x_991_, 1, v_a_973_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_991_);
v___x_993_ = v___x_988_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_991_);
v___x_993_ = v_reuseFailAlloc_995_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; 
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
else
{
lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_999_; 
lean_dec(v_a_973_);
v___x_996_ = l_List_reverse___redArg(v_a_986_);
v___x_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_974_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_997_);
v___x_999_ = v___x_988_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1001_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
lean_object* v___x_1000_; 
v___x_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
return v___x_1000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed(lean_object* v_a_1003_, lean_object* v___x_1004_, lean_object* v_x_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(v_a_1003_, v___x_1004_, v_x_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(lean_object* v___x_1008_, lean_object* v_eList_1009_, lean_object* v___f_1010_, lean_object* v_x_1011_){
_start:
{
if (lean_obj_tag(v_x_1011_) == 0)
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1021_; 
lean_dec_ref(v___f_1010_);
lean_dec(v_eList_1009_);
lean_dec(v___x_1008_);
v_a_1013_ = lean_ctor_get(v_x_1011_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_x_1011_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1015_ = v_x_1011_;
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v_x_1011_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1021_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v_a_1022_ = lean_ctor_get(v_x_1011_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v_x_1011_, 1);
lean_inc(v___x_1008_);
v___f_1023_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1023_, 0, v_a_1022_);
lean_closure_set(v___f_1023_, 1, v___x_1008_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = 0;
v___x_1026_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_eList_1009_, v___x_1008_);
v___x_1027_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1024_, v___x_1025_, v___x_1026_, v___f_1010_);
v___x_1028_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1024_, v___x_1025_, v___x_1027_, v___f_1023_);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed(lean_object* v___x_1029_, lean_object* v_eList_1030_, lean_object* v___f_1031_, lean_object* v_x_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(v___x_1029_, v_eList_1030_, v___f_1031_, v_x_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(lean_object* v_q_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_eList_1039_; lean_object* v_dList_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v___f_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_eList_1039_ = lean_ctor_get(v_q_1036_, 0);
lean_inc(v_eList_1039_);
v_dList_1040_ = lean_ctor_get(v_q_1036_, 1);
lean_inc(v_dList_1040_);
lean_dec_ref(v_q_1036_);
v___f_1041_ = ((lean_object*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0));
v___x_1042_ = lean_box(0);
v___f_1043_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1043_, 0, v___x_1042_);
lean_closure_set(v___f_1043_, 1, v_eList_1039_);
lean_closure_set(v___f_1043_, 2, v___f_1041_);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = 0;
v___x_1046_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_dList_1040_, v___x_1042_);
v___x_1047_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1044_, v___x_1045_, v___x_1046_, v___f_1041_);
v___x_1048_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1044_, v___x_1045_, v___x_1047_, v___f_1043_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___boxed(lean_object* v_q_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_q_1049_, v___y_1050_);
lean_dec(v___y_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__8(lean_object* v___y_1053_, lean_object* v_x_1054_){
_start:
{
if (lean_obj_tag(v_x_1054_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1064_; 
v_a_1056_ = lean_ctor_get(v_x_1054_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1054_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1058_ = v_x_1054_;
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v_x_1054_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
return v___x_1062_;
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v_reason_1066_; lean_object* v_consumers_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_a_1065_ = lean_ctor_get(v_x_1054_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v_x_1054_, 1);
v_reason_1066_ = lean_ctor_get(v_a_1065_, 0);
lean_inc(v_reason_1066_);
v_consumers_1067_ = lean_ctor_get(v_a_1065_, 1);
lean_inc_ref(v_consumers_1067_);
lean_dec(v_a_1065_);
lean_inc(v___y_1053_);
v___f_1068_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1068_, 0, v_reason_1066_);
lean_closure_set(v___f_1068_, 1, v___y_1053_);
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = 0;
v___x_1071_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_consumers_1067_, v___y_1053_);
v___x_1072_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1069_, v___x_1070_, v___x_1071_, v___f_1068_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__8___boxed(lean_object* v___y_1073_, lean_object* v_x_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Std_CancellationToken_selector___lam__8(v___y_1073_, v_x_1074_);
lean_dec(v___y_1073_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__9(lean_object* v___y_1077_){
_start:
{
lean_object* v___f_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_inc(v___y_1077_);
v___f_1079_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1079_, 0, v___y_1077_);
v___x_1080_ = lean_unsigned_to_nat(0u);
v___x_1081_ = 0;
v___x_1082_ = lean_st_ref_get(v___y_1077_);
v___x_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
v___x_1085_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1080_, v___x_1081_, v___x_1084_, v___f_1079_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__9___boxed(lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Std_CancellationToken_selector___lam__9(v___y_1086_);
lean_dec(v___y_1086_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector(lean_object* v_token_1091_){
_start:
{
lean_object* v___f_1092_; lean_object* v___f_1093_; lean_object* v___f_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
lean_inc_ref_n(v_token_1091_, 2);
v___f_1092_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1092_, 0, v_token_1091_);
v___f_1093_ = ((lean_object*)(l_Std_CancellationToken_selector___closed__0));
v___f_1094_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__6___boxed), 3, 2);
lean_closure_set(v___f_1094_, 0, v_token_1091_);
lean_closure_set(v___f_1094_, 1, v___f_1093_);
v___f_1095_ = ((lean_object*)(l_Std_CancellationToken_selector___closed__1));
v___x_1096_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed), 5, 4);
lean_closure_set(v___x_1096_, 0, lean_box(0));
lean_closure_set(v___x_1096_, 1, lean_box(0));
lean_closure_set(v___x_1096_, 2, v_token_1091_);
lean_closure_set(v___x_1096_, 3, v___f_1095_);
v___x_1097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1097_, 0, v___f_1094_);
lean_ctor_set(v___x_1097_, 1, v___f_1092_);
lean_ctor_set(v___x_1097_, 2, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_1098_, v_x_1099_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___boxed(lean_object* v_x_1103_, lean_object* v_x_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(v_x_1103_, v_x_1104_, v___y_1105_);
lean_dec(v___y_1105_);
return v_res_1107_;
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

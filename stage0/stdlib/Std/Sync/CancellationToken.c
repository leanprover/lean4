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
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Std_Queue_empty(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_8_);
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
lean_dec_ref(v_t_177_);
v___x_180_ = lean_apply_1(v_k_178_, v_promise_179_);
return v___x_180_;
}
else
{
lean_object* v_finished_181_; lean_object* v___x_182_; 
v_finished_181_ = lean_ctor_get(v_t_177_, 0);
lean_inc_ref(v_finished_181_);
lean_dec_ref(v_t_177_);
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
v___x_223_ = lean_st_ref_set(v_finished_216_, v___x_222_);
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
uint8_t v___x_408__boxed_240_; uint8_t v_res_241_; lean_object* v_r_242_; 
v___x_408__boxed_240_ = lean_unbox(v___x_238_);
v_res_241_ = l_Std_CancellationToken_Consumer_resolve___lam__0(v___x_408__boxed_240_);
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
v___x_259_ = l_Std_Queue_empty(lean_box(0));
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0___redArg(lean_object* v_b_292_){
_start:
{
lean_object* v___x_294_; 
lean_inc_ref(v_b_292_);
v___x_294_ = l_Std_Queue_dequeue_x3f___redArg(v_b_292_);
if (lean_obj_tag(v___x_294_) == 1)
{
lean_object* v_val_295_; lean_object* v_fst_296_; lean_object* v_snd_297_; uint8_t v___x_298_; 
lean_dec_ref(v_b_292_);
v_val_295_ = lean_ctor_get(v___x_294_, 0);
lean_inc(v_val_295_);
lean_dec_ref(v___x_294_);
v_fst_296_ = lean_ctor_get(v_val_295_, 0);
lean_inc(v_fst_296_);
v_snd_297_ = lean_ctor_get(v_val_295_, 1);
lean_inc(v_snd_297_);
lean_dec(v_val_295_);
v___x_298_ = l_Std_CancellationToken_Consumer_resolve(v_fst_296_);
lean_dec(v_fst_296_);
v_b_292_ = v_snd_297_;
goto _start;
}
else
{
lean_dec(v___x_294_);
return v_b_292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0___redArg___boxed(lean_object* v_b_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0___redArg(v_b_300_);
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
lean_object* v_consumers_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_319_; 
v_consumers_308_ = lean_ctor_get(v___x_306_, 1);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v___x_306_, 0);
lean_dec(v_unused_320_);
v___x_310_ = v___x_306_;
v_isShared_311_ = v_isSharedCheck_319_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_consumers_308_);
lean_dec(v___x_306_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_319_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_st_316_; 
v___x_312_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0___redArg(v_consumers_308_);
lean_dec_ref(v___x_312_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v_reason_303_);
v___x_314_ = lean_obj_once(&l_Std_CancellationToken_new___closed__0, &l_Std_CancellationToken_new___closed__0_once, _init_l_Std_CancellationToken_new___closed__0);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v___x_314_);
lean_ctor_set(v___x_310_, 0, v___x_313_);
v_st_316_ = v___x_310_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_314_);
v_st_316_ = v_reuseFailAlloc_318_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; 
v___x_317_ = lean_st_ref_set(v___y_304_, v_st_316_);
return v___x_317_;
}
}
}
else
{
lean_object* v___x_321_; 
lean_dec_ref(v_reason_307_);
lean_dec(v___x_306_);
lean_dec(v_reason_303_);
v___x_321_ = lean_box(0);
return v___x_321_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___lam__0___boxed(lean_object* v_reason_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Std_CancellationToken_cancel___lam__0(v_reason_322_, v___y_323_);
lean_dec(v___y_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel(lean_object* v_x_326_, lean_object* v_reason_327_){
_start:
{
lean_object* v___f_329_; lean_object* v___x_330_; 
v___f_329_ = lean_alloc_closure((void*)(l_Std_CancellationToken_cancel___lam__0___boxed), 3, 1);
lean_closure_set(v___f_329_, 0, v_reason_327_);
v___x_330_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_326_, v___f_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_cancel___boxed(lean_object* v_x_331_, lean_object* v_reason_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Std_CancellationToken_cancel(v_x_331_, v_reason_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0(lean_object* v_b_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0___redArg(v_b_335_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0___boxed(lean_object* v_b_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Std_CancellationToken_cancel_spec__0(v_b_339_, v___y_340_);
lean_dec(v___y_340_);
return v_res_342_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationToken_isCancelled___lam__0(lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v_reason_346_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_reason_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_reason_346_);
lean_dec(v___x_345_);
if (lean_obj_tag(v_reason_346_) == 0)
{
uint8_t v___x_347_; 
v___x_347_ = 0;
return v___x_347_;
}
else
{
uint8_t v___x_348_; 
lean_dec_ref(v_reason_346_);
v___x_348_ = 1;
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_isCancelled___lam__0___boxed(lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Std_CancellationToken_isCancelled___lam__0(v___y_349_);
lean_dec(v___y_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l_Std_CancellationToken_isCancelled(lean_object* v_x_354_){
_start:
{
lean_object* v___f_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___f_356_ = ((lean_object*)(l_Std_CancellationToken_isCancelled___closed__0));
v___x_357_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_354_, v___f_356_);
v___x_358_ = lean_unbox(v___x_357_);
lean_dec(v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_isCancelled___boxed(lean_object* v_x_359_, lean_object* v_a_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Std_CancellationToken_isCancelled(v_x_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___lam__0(lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; lean_object* v_reason_366_; 
v___x_365_ = lean_st_ref_get(v___y_363_);
v_reason_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_reason_366_);
lean_dec(v___x_365_);
return v_reason_366_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___lam__0___boxed(lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_CancellationToken_getCancellationReason___lam__0(v___y_367_);
lean_dec(v___y_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason(lean_object* v_x_371_){
_start:
{
lean_object* v___f_373_; lean_object* v___x_374_; 
v___f_373_ = ((lean_object*)(l_Std_CancellationToken_getCancellationReason___closed__0));
v___x_374_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(v_x_371_, v___f_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_getCancellationReason___boxed(lean_object* v_x_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Std_CancellationToken_getCancellationReason(v_x_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(lean_object* v_mutex_378_, lean_object* v_k_379_){
_start:
{
lean_object* v_ref_381_; lean_object* v_mutex_382_; lean_object* v___x_383_; lean_object* v_r_384_; 
v_ref_381_ = lean_ctor_get(v_mutex_378_, 0);
lean_inc(v_ref_381_);
v_mutex_382_ = lean_ctor_get(v_mutex_378_, 1);
lean_inc(v_mutex_382_);
lean_dec_ref(v_mutex_378_);
v___x_383_ = lean_io_basemutex_lock(v_mutex_382_);
v_r_384_ = lean_apply_2(v_k_379_, v_ref_381_, lean_box(0));
if (lean_obj_tag(v_r_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_393_; 
v_a_385_ = lean_ctor_get(v_r_384_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v_r_384_);
if (v_isSharedCheck_393_ == 0)
{
v___x_387_ = v_r_384_;
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v_r_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_393_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_io_basemutex_unlock(v_mutex_382_);
lean_dec(v_mutex_382_);
if (v_isShared_388_ == 0)
{
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_385_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
v_a_394_ = lean_ctor_get(v_r_384_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v_r_384_);
if (v_isSharedCheck_402_ == 0)
{
v___x_396_ = v_r_384_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v_r_384_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = lean_io_basemutex_unlock(v_mutex_382_);
lean_dec(v_mutex_382_);
if (v_isShared_397_ == 0)
{
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_394_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg___boxed(lean_object* v_mutex_403_, lean_object* v_k_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_mutex_403_, v_k_404_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(lean_object* v_00_u03b1_407_, lean_object* v_00_u03b2_408_, lean_object* v_mutex_409_, lean_object* v_k_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_mutex_409_, v_k_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___boxed(lean_object* v_00_u03b1_413_, lean_object* v_00_u03b2_414_, lean_object* v_mutex_415_, lean_object* v_k_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(v_00_u03b1_413_, v_00_u03b2_414_, v_mutex_415_, v_k_416_);
return v_res_418_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__1(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l_Std_CancellationToken_wait___lam__0___closed__0));
v___x_421_ = lean_mk_io_user_error(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__2(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__1, &l_Std_CancellationToken_wait___lam__0___closed__1_once, _init_l_Std_CancellationToken_wait___lam__0___closed__1);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__3(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__2, &l_Std_CancellationToken_wait___lam__0___closed__2_once, _init_l_Std_CancellationToken_wait___lam__0___closed__2);
v___x_425_ = lean_task_pure(v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l_Std_CancellationToken_wait___lam__0___closed__4(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_427_ = lean_task_pure(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__0(lean_object* v_a_428_){
_start:
{
if (lean_obj_tag(v_a_428_) == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__3, &l_Std_CancellationToken_wait___lam__0___closed__3_once, _init_l_Std_CancellationToken_wait___lam__0___closed__3);
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
v___x_431_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__4, &l_Std_CancellationToken_wait___lam__0___closed__4_once, _init_l_Std_CancellationToken_wait___lam__0___closed__4);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__0___boxed(lean_object* v_a_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_CancellationToken_wait___lam__0(v_a_432_);
lean_dec(v_a_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__1(lean_object* v___f_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; lean_object* v_reason_439_; 
v___x_438_ = lean_st_ref_get(v___y_436_);
v_reason_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_reason_439_);
lean_dec(v___x_438_);
if (lean_obj_tag(v_reason_439_) == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_reason_442_; lean_object* v_consumers_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_458_; 
v___x_440_ = lean_io_promise_new();
v___x_441_ = lean_st_ref_take(v___y_436_);
v_reason_442_ = lean_ctor_get(v___x_441_, 0);
v_consumers_443_ = lean_ctor_get(v___x_441_, 1);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_458_ == 0)
{
v___x_445_ = v___x_441_;
v_isShared_446_ = v_isSharedCheck_458_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_consumers_443_);
lean_inc(v_reason_442_);
lean_dec(v___x_441_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_458_;
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
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_reason_442_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_457_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_451_; uint8_t v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_451_ = lean_st_ref_set(v___y_436_, v___x_450_);
v___x_452_ = 0;
v___x_453_ = lean_io_promise_result_opt(v___x_440_);
lean_dec(v___x_440_);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_io_bind_task(v___x_453_, v___f_435_, v___x_454_, v___x_452_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
}
else
{
lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref(v___f_435_);
v_isSharedCheck_466_ = !lean_is_exclusive(v_reason_439_);
if (v_isSharedCheck_466_ == 0)
{
lean_object* v_unused_467_; 
v_unused_467_ = lean_ctor_get(v_reason_439_, 0);
lean_dec(v_unused_467_);
v___x_460_ = v_reason_439_;
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
else
{
lean_dec(v_reason_439_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_466_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_obj_once(&l_Std_CancellationToken_wait___lam__0___closed__4, &l_Std_CancellationToken_wait___lam__0___closed__4_once, _init_l_Std_CancellationToken_wait___lam__0___closed__4);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 0);
lean_ctor_set(v___x_460_, 0, v___x_462_);
v___x_464_ = v___x_460_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_462_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___lam__1___boxed(lean_object* v___f_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Std_CancellationToken_wait___lam__1(v___f_468_, v___y_469_);
lean_dec(v___y_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait(lean_object* v_x_475_){
_start:
{
lean_object* v___f_477_; lean_object* v___x_478_; 
v___f_477_ = ((lean_object*)(l_Std_CancellationToken_wait___closed__1));
v___x_478_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(v_x_475_, v___f_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_wait___boxed(lean_object* v_x_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_CancellationToken_wait(v_x_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(uint8_t v___x_482_, lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_493_; 
v_a_485_ = lean_ctor_get(v_x_483_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v_x_483_);
if (v_isSharedCheck_493_ == 0)
{
v___x_487_ = v_x_483_;
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v_x_483_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_492_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_491_; 
v___x_491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_491_, 0, v___x_490_);
return v___x_491_;
}
}
}
else
{
lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_502_; 
v_isSharedCheck_502_ = !lean_is_exclusive(v_x_483_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v_x_483_, 0);
lean_dec(v_unused_503_);
v___x_495_ = v_x_483_;
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
else
{
lean_dec(v_x_483_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_box(v___x_482_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_501_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0___boxed(lean_object* v___x_504_, lean_object* v_x_505_, lean_object* v___y_506_){
_start:
{
uint8_t v___x_6814__boxed_507_; lean_object* v_res_508_; 
v___x_6814__boxed_507_ = lean_unbox(v___x_504_);
v_res_508_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(v___x_6814__boxed_507_, v_x_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(lean_object* v_lose_509_, lean_object* v___y_510_, lean_object* v_promise_511_, lean_object* v___f_512_, lean_object* v_x_513_){
_start:
{
if (lean_obj_tag(v_x_513_) == 0)
{
lean_object* v___x_515_; 
lean_dec_ref(v___f_512_);
lean_dec_ref(v_lose_509_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_x_513_);
return v___x_515_;
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_531_; 
v_a_516_ = lean_ctor_get(v_x_513_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_x_513_);
if (v_isSharedCheck_531_ == 0)
{
v___x_518_ = v_x_513_;
v_isShared_519_ = v_isSharedCheck_531_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v_x_513_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_531_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
uint8_t v___x_520_; 
v___x_520_ = lean_unbox(v_a_516_);
lean_dec(v_a_516_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_del_object(v___x_518_);
lean_dec_ref(v___f_512_);
lean_inc(v___y_510_);
v___x_521_ = lean_apply_2(v_lose_509_, v___y_510_, lean_box(0));
return v___x_521_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
lean_dec_ref(v_lose_509_);
v___x_522_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___x_523_ = lean_io_promise_resolve(v___x_522_, v_promise_511_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_523_);
v___x_525_ = v___x_518_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_530_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = 0;
v___x_529_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_527_, v___x_528_, v___x_526_, v___f_512_);
return v___x_529_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed(lean_object* v_lose_532_, lean_object* v___y_533_, lean_object* v_promise_534_, lean_object* v___f_535_, lean_object* v_x_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(v_lose_532_, v___y_533_, v_promise_534_, v___f_535_, v_x_536_);
lean_dec(v_promise_534_);
lean_dec(v___y_533_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(lean_object* v_w_542_, lean_object* v_lose_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_finished_546_; lean_object* v_promise_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___f_550_; lean_object* v___f_551_; uint8_t v___y_553_; uint8_t v___x_562_; 
v_finished_546_ = lean_ctor_get(v_w_542_, 0);
lean_inc(v_finished_546_);
v_promise_547_ = lean_ctor_get(v_w_542_, 1);
lean_inc(v_promise_547_);
lean_dec_ref(v_w_542_);
v___x_548_ = lean_st_ref_take(v_finished_546_);
v___x_549_ = 1;
v___f_550_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0));
lean_inc(v___y_544_);
v___f_551_ = lean_alloc_closure((void*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed), 6, 4);
lean_closure_set(v___f_551_, 0, v_lose_543_);
lean_closure_set(v___f_551_, 1, v___y_544_);
lean_closure_set(v___f_551_, 2, v_promise_547_);
lean_closure_set(v___f_551_, 3, v___f_550_);
v___x_562_ = lean_unbox(v___x_548_);
lean_dec(v___x_548_);
if (v___x_562_ == 0)
{
v___y_553_ = v___x_549_;
goto v___jp_552_;
}
else
{
uint8_t v___x_563_; 
v___x_563_ = 0;
v___y_553_ = v___x_563_;
goto v___jp_552_;
}
v___jp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; 
v___x_554_ = lean_box(v___x_549_);
v___x_555_ = lean_st_ref_set(v_finished_546_, v___x_554_);
lean_dec(v_finished_546_);
v___x_556_ = lean_box(v___y_553_);
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = 0;
v___x_561_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_559_, v___x_560_, v___x_558_, v___f_551_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___boxed(lean_object* v_w_564_, lean_object* v_lose_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(v_w_564_, v_lose_565_, v___y_566_);
lean_dec(v___y_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(lean_object* v_mutex_569_, lean_object* v_x_570_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_572_ = lean_io_basemutex_unlock(v_mutex_569_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0___boxed(lean_object* v_mutex_575_, lean_object* v_x_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(v_mutex_575_, v_x_576_);
lean_dec(v_x_576_);
lean_dec(v_mutex_575_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(lean_object* v_k_579_, lean_object* v_ref_580_, lean_object* v_x_581_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_ref_580_);
lean_dec_ref(v_k_579_);
v_a_583_ = lean_ctor_get(v_x_581_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_591_ == 0)
{
v___x_585_ = v_x_581_;
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v_x_581_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_591_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_590_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
return v___x_589_;
}
}
}
else
{
lean_object* v___x_592_; 
lean_dec_ref(v_x_581_);
v___x_592_ = lean_apply_2(v_k_579_, v_ref_580_, lean_box(0));
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed(lean_object* v_k_593_, lean_object* v_ref_594_, lean_object* v_x_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(v_k_593_, v_ref_594_, v_x_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(lean_object* v_mutex_598_, lean_object* v___f_599_){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; 
v___x_601_ = lean_io_basemutex_lock(v_mutex_598_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = 0;
v___x_606_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_604_, v___x_605_, v___x_603_, v___f_599_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed(lean_object* v_mutex_607_, lean_object* v___f_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(v_mutex_607_, v___f_608_);
lean_dec(v_mutex_607_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(lean_object* v___y_611_){
_start:
{
if (lean_obj_tag(v___y_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
v_a_612_ = lean_ctor_get(v___y_611_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___y_611_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___y_611_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___y_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_628_; 
v_a_620_ = lean_ctor_get(v___y_611_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___y_611_);
if (v_isSharedCheck_628_ == 0)
{
v___x_622_ = v___y_611_;
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___y_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v_fst_624_; lean_object* v___x_626_; 
v_fst_624_ = lean_ctor_get(v_a_620_, 0);
lean_inc(v_fst_624_);
lean_dec(v_a_620_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v_fst_624_);
v___x_626_ = v___x_622_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_fst_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(lean_object* v_mutex_630_, lean_object* v_k_631_){
_start:
{
lean_object* v_ref_633_; lean_object* v_mutex_634_; lean_object* v___f_635_; lean_object* v___f_636_; lean_object* v___f_637_; lean_object* v___x_638_; uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___y_642_; 
v_ref_633_ = lean_ctor_get(v_mutex_630_, 0);
lean_inc(v_ref_633_);
v_mutex_634_ = lean_ctor_get(v_mutex_630_, 1);
lean_inc_n(v_mutex_634_, 2);
lean_dec_ref(v_mutex_630_);
v___f_635_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_635_, 0, v_mutex_634_);
v___f_636_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_636_, 0, v_k_631_);
lean_closure_set(v___f_636_, 1, v_ref_633_);
v___f_637_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_637_, 0, v_mutex_634_);
lean_closure_set(v___f_637_, 1, v___f_636_);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = 0;
v___x_640_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_637_, v___f_635_, v___x_638_, v___x_639_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_644_; 
v_a_644_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_644_);
lean_dec_ref(v___x_640_);
if (lean_obj_tag(v_a_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_a_645_ = lean_ctor_get(v_a_644_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v_a_644_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v_a_644_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v_a_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
v___y_642_ = v___x_650_;
goto v___jp_641_;
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_661_; 
v_a_653_ = lean_ctor_get(v_a_644_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_a_644_);
if (v_isSharedCheck_661_ == 0)
{
v___x_655_ = v_a_644_;
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v_a_644_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_661_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_fst_657_; lean_object* v___x_659_; 
v_fst_657_ = lean_ctor_get(v_a_653_, 0);
lean_inc(v_fst_657_);
lean_dec(v_a_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v_fst_657_);
v___x_659_ = v___x_655_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_fst_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
v___y_642_ = v___x_659_;
goto v___jp_641_;
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_671_; 
v_a_662_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_671_ == 0)
{
v___x_664_ = v___x_640_;
v_isShared_665_ = v_isSharedCheck_671_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_640_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_671_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___f_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v___f_666_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0));
v___x_667_ = lean_task_map(v___f_666_, v_a_662_, v___x_638_, v___x_639_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_667_);
v___x_669_ = v___x_664_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
v___jp_641_:
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___y_642_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___boxed(lean_object* v_mutex_672_, lean_object* v_k_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_mutex_672_, v_k_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_mutex_678_, lean_object* v_k_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_mutex_678_, v_k_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed(lean_object* v_00_u03b1_682_, lean_object* v_00_u03b2_683_, lean_object* v_mutex_684_, lean_object* v_k_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(v_00_u03b1_682_, v_00_u03b2_683_, v_mutex_684_, v_k_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__0(uint8_t v___x_688_, lean_object* v___y_689_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_box(v___x_688_);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__0___boxed(lean_object* v___x_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
uint8_t v___x_7132__boxed_697_; lean_object* v_res_698_; 
v___x_7132__boxed_697_ = lean_unbox(v___x_694_);
v_res_698_ = l_Std_CancellationToken_selector___lam__0(v___x_7132__boxed_697_, v___y_695_);
lean_dec(v___y_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__1(lean_object* v___x_699_, lean_object* v___y_700_){
_start:
{
if (lean_obj_tag(v___y_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
v_a_701_ = lean_ctor_get(v___y_700_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___y_700_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___y_700_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___y_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
v_isSharedCheck_715_ = !lean_is_exclusive(v___y_700_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v___y_700_, 0);
lean_dec(v_unused_716_);
v___x_710_ = v___y_700_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_dec(v___y_700_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_699_);
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_699_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__2(lean_object* v___y_724_, lean_object* v_waiter_725_, lean_object* v_x_726_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v_waiter_725_);
v_a_728_ = lean_ctor_get(v_x_726_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_x_726_);
if (v_isSharedCheck_736_ == 0)
{
v___x_730_ = v_x_726_;
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v_x_726_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_736_;
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
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_735_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
return v___x_734_;
}
}
}
else
{
lean_object* v_a_737_; lean_object* v_reason_738_; 
v_a_737_ = lean_ctor_get(v_x_726_, 0);
lean_inc(v_a_737_);
lean_dec_ref(v_x_726_);
v_reason_738_ = lean_ctor_get(v_a_737_, 0);
lean_inc(v_reason_738_);
lean_dec(v_a_737_);
if (lean_obj_tag(v_reason_738_) == 0)
{
lean_object* v___x_739_; lean_object* v_reason_740_; lean_object* v_consumers_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_752_; 
v___x_739_ = lean_st_ref_take(v___y_724_);
v_reason_740_ = lean_ctor_get(v___x_739_, 0);
v_consumers_741_ = lean_ctor_get(v___x_739_, 1);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_752_ == 0)
{
v___x_743_ = v___x_739_;
v_isShared_744_ = v_isSharedCheck_752_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_consumers_741_);
lean_inc(v_reason_740_);
lean_dec(v___x_739_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_752_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_745_, 0, v_waiter_725_);
v___x_746_ = l_Std_Queue_enqueue___redArg(v___x_745_, v_consumers_741_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v___x_746_);
v___x_748_ = v___x_743_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_reason_740_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___x_746_);
v___x_748_ = v_reuseFailAlloc_751_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = lean_st_ref_set(v___y_724_, v___x_748_);
v___x_750_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__0));
return v___x_750_;
}
}
}
else
{
lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_785_; 
v_isSharedCheck_785_ = !lean_is_exclusive(v_reason_738_);
if (v_isSharedCheck_785_ == 0)
{
lean_object* v_unused_786_; 
v_unused_786_ = lean_ctor_get(v_reason_738_, 0);
lean_dec(v_unused_786_);
v___x_754_ = v_reason_738_;
v_isShared_755_ = v_isSharedCheck_785_;
goto v_resetjp_753_;
}
else
{
lean_dec(v_reason_738_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_785_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
uint8_t v___x_756_; lean_object* v___f_757_; lean_object* v___x_758_; lean_object* v___y_760_; 
v___x_756_ = 0;
v___f_757_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__1));
v___x_758_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(v_waiter_725_, v___f_757_, v___y_724_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_a_764_);
lean_dec_ref(v___x_758_);
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
lean_dec_ref(v_a_764_);
v___x_773_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0));
v___y_760_ = v___x_773_;
goto v___jp_759_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_784_; 
lean_del_object(v___x_754_);
v_a_774_ = lean_ctor_get(v___x_758_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_758_);
if (v_isSharedCheck_784_ == 0)
{
v___x_776_ = v___x_758_;
v_isShared_777_ = v_isSharedCheck_784_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_758_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_784_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___f_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
v___f_778_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__2___closed__2));
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_task_map(v___f_778_, v_a_774_, v___x_779_, v___x_756_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_780_);
v___x_782_ = v___x_776_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
v___jp_759_:
{
lean_object* v___x_762_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 0);
lean_ctor_set(v___x_754_, 0, v___y_760_);
v___x_762_ = v___x_754_;
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
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__2___boxed(lean_object* v___y_787_, lean_object* v_waiter_788_, lean_object* v_x_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_CancellationToken_selector___lam__2(v___y_787_, v_waiter_788_, v_x_789_);
lean_dec(v___y_787_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__3(lean_object* v_waiter_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; lean_object* v___f_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; lean_object* v___x_801_; 
v___x_795_ = lean_st_ref_get(v___y_793_);
lean_inc(v___y_793_);
v___f_796_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__2___boxed), 4, 2);
lean_closure_set(v___f_796_, 0, v___y_793_);
lean_closure_set(v___f_796_, 1, v_waiter_792_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = 0;
v___x_801_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_799_, v___x_800_, v___x_798_, v___f_796_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__3___boxed(lean_object* v_waiter_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_CancellationToken_selector___lam__3(v_waiter_802_, v___y_803_);
lean_dec(v___y_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__4(lean_object* v_token_806_, lean_object* v_waiter_807_){
_start:
{
lean_object* v___f_809_; lean_object* v___x_810_; 
v___f_809_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_809_, 0, v_waiter_807_);
v___x_810_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(v_token_806_, v___f_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__4___boxed(lean_object* v_token_811_, lean_object* v_waiter_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_CancellationToken_selector___lam__4(v_token_811_, v_waiter_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__5(lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_825_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_835_; 
v_a_827_ = lean_ctor_get(v_x_825_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v_x_825_);
if (v_isSharedCheck_835_ == 0)
{
v___x_829_ = v_x_825_;
v_isShared_830_ = v_isSharedCheck_835_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v_x_825_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_835_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_834_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; 
v___x_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
return v___x_833_;
}
}
}
else
{
lean_object* v_a_836_; uint8_t v___x_837_; 
v_a_836_ = lean_ctor_get(v_x_825_, 0);
lean_inc(v_a_836_);
lean_dec_ref(v_x_825_);
v___x_837_ = lean_unbox(v_a_836_);
lean_dec(v_a_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
v___x_838_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__5___closed__1));
return v___x_838_;
}
else
{
lean_object* v___x_839_; 
v___x_839_ = ((lean_object*)(l_Std_CancellationToken_selector___lam__5___closed__4));
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__5___boxed(lean_object* v_x_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_CancellationToken_selector___lam__5(v_x_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__6(lean_object* v_token_843_, lean_object* v___f_844_){
_start:
{
uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; 
v___x_846_ = l_Std_CancellationToken_isCancelled(v_token_843_);
v___x_847_ = lean_box(v___x_846_);
v___x_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = 0;
v___x_852_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_850_, v___x_851_, v___x_849_, v___f_844_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__6___boxed(lean_object* v_token_853_, lean_object* v___f_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_CancellationToken_selector___lam__6(v_token_853_, v___f_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__7(lean_object* v_reason_857_, lean_object* v___y_858_, lean_object* v_x_859_){
_start:
{
if (lean_obj_tag(v_x_859_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_reason_857_);
v_a_861_ = lean_ctor_get(v_x_859_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_x_859_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v_x_859_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v_x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_868_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
lean_object* v___x_867_; 
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
return v___x_867_;
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_880_; 
v_a_870_ = lean_ctor_get(v_x_859_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v_x_859_);
if (v_isSharedCheck_880_ == 0)
{
v___x_872_ = v_x_859_;
v_isShared_873_ = v_isSharedCheck_880_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v_x_859_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_880_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_reason_857_);
lean_ctor_set(v___x_874_, 1, v_a_870_);
v___x_875_ = lean_st_ref_set(v___y_858_, v___x_874_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_875_);
v___x_877_ = v___x_872_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_879_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; 
v___x_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__7___boxed(lean_object* v_reason_881_, lean_object* v___y_882_, lean_object* v_x_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_CancellationToken_selector___lam__7(v_reason_881_, v___y_882_, v_x_883_);
lean_dec(v___y_882_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(lean_object* v_x_886_){
_start:
{
if (lean_obj_tag(v_x_886_) == 0)
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v_x_886_);
return v___x_888_;
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_898_; 
v_a_889_ = lean_ctor_get(v_x_886_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_x_886_);
if (v_isSharedCheck_898_ == 0)
{
v___x_891_ = v_x_886_;
v_isShared_892_ = v_isSharedCheck_898_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v_x_886_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_898_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = l_List_reverse___redArg(v_a_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_893_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_897_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_896_; 
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0___boxed(lean_object* v_x_899_, lean_object* v___y_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(v_x_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(lean_object* v_a_902_, lean_object* v___x_903_, lean_object* v_x_904_){
_start:
{
if (lean_obj_tag(v_x_904_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_914_; 
lean_dec(v___x_903_);
lean_dec(v_a_902_);
v_a_906_ = lean_ctor_get(v_x_904_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v_x_904_);
if (v_isSharedCheck_914_ == 0)
{
v___x_908_ = v_x_904_;
v_isShared_909_ = v_isSharedCheck_914_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v_x_904_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_914_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_913_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
lean_object* v___x_912_; 
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_931_; 
v_a_915_ = lean_ctor_get(v_x_904_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_904_);
if (v_isSharedCheck_931_ == 0)
{
v___x_917_ = v_x_904_;
v_isShared_918_ = v_isSharedCheck_931_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v_x_904_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_931_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
uint8_t v___x_919_; 
v___x_919_ = l_List_isEmpty___redArg(v_a_902_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; lean_object* v___x_922_; 
lean_dec(v___x_903_);
v___x_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_920_, 0, v_a_915_);
lean_ctor_set(v___x_920_, 1, v_a_902_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_920_);
v___x_922_ = v___x_917_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_924_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_923_; 
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
lean_dec(v_a_902_);
v___x_925_ = l_List_reverse___redArg(v_a_915_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_903_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_926_);
v___x_928_ = v___x_917_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_930_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; 
v___x_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
return v___x_929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed(lean_object* v_a_932_, lean_object* v___x_933_, lean_object* v_x_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(v_a_932_, v___x_933_, v_x_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(lean_object* v_x_937_){
_start:
{
uint8_t v___y_940_; 
if (lean_obj_tag(v_x_937_) == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_x_937_);
return v___x_944_;
}
else
{
lean_object* v_a_945_; uint8_t v___x_946_; 
v_a_945_ = lean_ctor_get(v_x_937_, 0);
lean_inc(v_a_945_);
lean_dec_ref(v_x_937_);
v___x_946_ = lean_unbox(v_a_945_);
lean_dec(v_a_945_);
if (v___x_946_ == 0)
{
uint8_t v___x_947_; 
v___x_947_ = 1;
v___y_940_ = v___x_947_;
goto v___jp_939_;
}
else
{
uint8_t v___x_948_; 
v___x_948_ = 0;
v___y_940_ = v___x_948_;
goto v___jp_939_;
}
}
v___jp_939_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_box(v___y_940_);
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1___boxed(lean_object* v_x_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(v_x_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed(lean_object* v_tail_952_, lean_object* v_x_953_, lean_object* v_head_954_, lean_object* v_x_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(v_tail_952_, v_x_953_, v_head_954_, v_x_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
if (lean_obj_tag(v_x_964_) == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v_x_965_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
else
{
lean_object* v_head_969_; lean_object* v_tail_970_; lean_object* v___f_971_; lean_object* v_val_973_; 
v_head_969_ = lean_ctor_get(v_x_964_, 0);
lean_inc_n(v_head_969_, 2);
v_tail_970_ = lean_ctor_get(v_x_964_, 1);
lean_inc(v_tail_970_);
lean_dec_ref(v_x_964_);
v___f_971_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_971_, 0, v_tail_970_);
lean_closure_set(v___f_971_, 1, v_x_965_);
lean_closure_set(v___f_971_, 2, v_head_969_);
if (lean_obj_tag(v_head_969_) == 0)
{
lean_object* v___x_977_; 
lean_dec_ref(v_head_969_);
v___x_977_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1));
v_val_973_ = v___x_977_;
goto v___jp_972_;
}
else
{
lean_object* v_finished_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_992_; 
v_finished_978_ = lean_ctor_get(v_head_969_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v_head_969_);
if (v_isSharedCheck_992_ == 0)
{
v___x_980_ = v_head_969_;
v_isShared_981_ = v_isSharedCheck_992_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_finished_978_);
lean_dec(v_head_969_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_992_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_finished_982_; lean_object* v___x_983_; lean_object* v___f_984_; lean_object* v___x_986_; 
v_finished_982_ = lean_ctor_get(v_finished_978_, 0);
lean_inc(v_finished_982_);
lean_dec_ref(v_finished_978_);
v___x_983_ = lean_st_ref_get(v_finished_982_);
lean_dec(v_finished_982_);
v___f_984_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2));
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_983_);
v___x_986_ = v___x_980_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_983_);
v___x_986_ = v_reuseFailAlloc_991_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; lean_object* v___x_990_; 
v___x_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = 0;
v___x_990_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_988_, v___x_989_, v___x_987_, v___f_984_);
v_val_973_ = v___x_990_;
goto v___jp_972_;
}
}
}
v___jp_972_:
{
lean_object* v___x_974_; uint8_t v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = 0;
v___x_976_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_974_, v___x_975_, v_val_973_, v___f_971_);
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(lean_object* v_tail_993_, lean_object* v_x_994_, lean_object* v_head_995_, lean_object* v_x_996_){
_start:
{
if (lean_obj_tag(v_x_996_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v_head_995_);
lean_dec(v_x_994_);
lean_dec(v_tail_993_);
v_a_998_ = lean_ctor_get(v_x_996_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_x_996_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1000_ = v_x_996_;
v_isShared_1001_ = v_isSharedCheck_1006_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v_x_996_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1006_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
lean_object* v___x_1004_; 
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
}
}
else
{
lean_object* v_a_1007_; uint8_t v___x_1008_; 
v_a_1007_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_a_1007_);
lean_dec_ref(v_x_996_);
v___x_1008_ = lean_unbox(v_a_1007_);
lean_dec(v_a_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_dec_ref(v_head_995_);
v___x_1009_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_993_, v_x_994_);
return v___x_1009_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1010_, 0, v_head_995_);
lean_ctor_set(v___x_1010_, 1, v_x_994_);
v___x_1011_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_993_, v___x_1010_);
return v___x_1011_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___boxed(lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_1012_, v_x_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(lean_object* v_eList_1016_, lean_object* v___x_1017_, lean_object* v___f_1018_, lean_object* v_x_1019_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v___f_1018_);
lean_dec(v___x_1017_);
lean_dec(v_eList_1016_);
v_a_1021_ = lean_ctor_get(v_x_1019_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_x_1019_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1023_ = v_x_1019_;
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v_x_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1029_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
lean_object* v___x_1027_; 
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; 
v_a_1030_ = lean_ctor_get(v_x_1019_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v_x_1019_);
lean_inc(v___x_1017_);
v___x_1031_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_eList_1016_, v___x_1017_);
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = 0;
v___x_1034_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1032_, v___x_1033_, v___x_1031_, v___f_1018_);
v___f_1035_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1035_, 0, v_a_1030_);
lean_closure_set(v___f_1035_, 1, v___x_1017_);
v___x_1036_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1032_, v___x_1033_, v___x_1034_, v___f_1035_);
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed(lean_object* v_eList_1037_, lean_object* v___x_1038_, lean_object* v___f_1039_, lean_object* v_x_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(v_eList_1037_, v___x_1038_, v___f_1039_, v_x_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(lean_object* v_q_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_eList_1047_; lean_object* v_dList_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; 
v_eList_1047_ = lean_ctor_get(v_q_1044_, 0);
lean_inc(v_eList_1047_);
v_dList_1048_ = lean_ctor_get(v_q_1044_, 1);
lean_inc(v_dList_1048_);
lean_dec_ref(v_q_1044_);
v___x_1049_ = lean_box(0);
v___x_1050_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_dList_1048_, v___x_1049_);
v___f_1051_ = ((lean_object*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0));
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = 0;
v___x_1054_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1052_, v___x_1053_, v___x_1050_, v___f_1051_);
v___f_1055_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed), 5, 3);
lean_closure_set(v___f_1055_, 0, v_eList_1047_);
lean_closure_set(v___f_1055_, 1, v___x_1049_);
lean_closure_set(v___f_1055_, 2, v___f_1051_);
v___x_1056_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1052_, v___x_1053_, v___x_1054_, v___f_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___boxed(lean_object* v_q_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_q_1057_, v___y_1058_);
lean_dec(v___y_1058_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__8(lean_object* v___y_1061_, lean_object* v_x_1062_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1072_; 
v_a_1064_ = lean_ctor_get(v_x_1062_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_x_1062_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1066_ = v_x_1062_;
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v_x_1062_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
}
else
{
lean_object* v_a_1073_; lean_object* v_reason_1074_; lean_object* v_consumers_1075_; lean_object* v___x_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; 
v_a_1073_ = lean_ctor_get(v_x_1062_, 0);
lean_inc(v_a_1073_);
lean_dec_ref(v_x_1062_);
v_reason_1074_ = lean_ctor_get(v_a_1073_, 0);
lean_inc(v_reason_1074_);
v_consumers_1075_ = lean_ctor_get(v_a_1073_, 1);
lean_inc_ref(v_consumers_1075_);
lean_dec(v_a_1073_);
v___x_1076_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_consumers_1075_, v___y_1061_);
lean_inc(v___y_1061_);
v___f_1077_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__7___boxed), 4, 2);
lean_closure_set(v___f_1077_, 0, v_reason_1074_);
lean_closure_set(v___f_1077_, 1, v___y_1061_);
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = 0;
v___x_1080_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1078_, v___x_1079_, v___x_1076_, v___f_1077_);
return v___x_1080_;
}
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__8___boxed(lean_object* v___y_1081_, lean_object* v_x_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Std_CancellationToken_selector___lam__8(v___y_1081_, v_x_1082_);
lean_dec(v___y_1081_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__9(lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; 
v___x_1087_ = lean_st_ref_get(v___y_1085_);
lean_inc(v___y_1085_);
v___f_1088_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__8___boxed), 3, 1);
lean_closure_set(v___f_1088_, 0, v___y_1085_);
v___x_1089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = 0;
v___x_1093_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_1091_, v___x_1092_, v___x_1090_, v___f_1088_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector___lam__9___boxed(lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l_Std_CancellationToken_selector___lam__9(v___y_1094_);
lean_dec(v___y_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_CancellationToken_selector(lean_object* v_token_1099_){
_start:
{
lean_object* v___f_1100_; lean_object* v___f_1101_; lean_object* v___f_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
lean_inc_ref_n(v_token_1099_, 2);
v___f_1100_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_1100_, 0, v_token_1099_);
v___f_1101_ = ((lean_object*)(l_Std_CancellationToken_selector___closed__0));
v___f_1102_ = lean_alloc_closure((void*)(l_Std_CancellationToken_selector___lam__6___boxed), 3, 2);
lean_closure_set(v___f_1102_, 0, v_token_1099_);
lean_closure_set(v___f_1102_, 1, v___f_1101_);
v___f_1103_ = ((lean_object*)(l_Std_CancellationToken_selector___closed__1));
v___x_1104_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed), 5, 4);
lean_closure_set(v___x_1104_, 0, lean_box(0));
lean_closure_set(v___x_1104_, 1, lean_box(0));
lean_closure_set(v___x_1104_, 2, v_token_1099_);
lean_closure_set(v___x_1104_, 3, v___f_1103_);
v___x_1105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1105_, 0, v___f_1102_);
lean_ctor_set(v___x_1105_, 1, v___f_1100_);
lean_ctor_set(v___x_1105_, 2, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_1106_, v_x_1107_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___boxed(lean_object* v_x_1111_, lean_object* v_x_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(v_x_1111_, v_x_1112_, v___y_1113_);
lean_dec(v___y_1113_);
return v_res_1115_;
}
}
lean_object* runtime_initialize_Std_Data(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_CancellationToken(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

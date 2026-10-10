// Lean compiler output
// Module: Std.Sync.Notify
// Imports: public import Init.Data.Queue public import Std.Sync.Mutex public import Std.Async.Select
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
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* l_Std_Async_EAsync_tryFinally_x27___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_io_promise_new();
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_Queue_enqueue___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Std_Queue_empty___redArg();
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_normal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_normal_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_select_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_select_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Notify_Consumer_resolve___redArg___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Notify_Consumer_resolve___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Notify_Consumer_resolve___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Notify_Consumer_resolve___redArg___closed__0 = (const lean_object*)&l_Std_Notify_Consumer_resolve___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Notify_Consumer_resolve___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Notify_Consumer_resolve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_Notify_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Notify_new___closed__0;
LEAN_EXPORT lean_object* l_Std_Notify_new();
LEAN_EXPORT lean_object* l_Std_Notify_new___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_notify___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_notify___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Notify_notify___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Notify_notify___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Notify_notify___closed__0 = (const lean_object*)&l_Std_Notify_notify___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Notify_notify(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_notify___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__1 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Notify_notifyOne___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Notify_notifyOne___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Notify_notifyOne___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Notify_notifyOne___closed__0 = (const lean_object*)&l_Std_Notify_notifyOne___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Notify_notifyOne(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Notify_wait___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "notify dropped"};
static const lean_object* l_Std_Notify_wait___lam__0___closed__0 = (const lean_object*)&l_Std_Notify_wait___lam__0___closed__0_value;
static lean_once_cell_t l_Std_Notify_wait___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Notify_wait___lam__0___closed__1;
static lean_once_cell_t l_Std_Notify_wait___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Notify_wait___lam__0___closed__2;
static lean_once_cell_t l_Std_Notify_wait___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Notify_wait___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Notify_wait___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Notify_wait___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Notify_wait___closed__0 = (const lean_object*)&l_Std_Notify_wait___closed__0_value;
static const lean_closure_object l_Std_Notify_wait___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Notify_wait___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Notify_wait___closed__0_value)} };
static const lean_object* l_Std_Notify_wait___closed__1 = (const lean_object*)&l_Std_Notify_wait___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Notify_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_wait___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Notify_selector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Notify_selector___lam__0___closed__0 = (const lean_object*)&l_Std_Notify_selector___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Notify_selector___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Notify_selector___lam__0___closed__0_value)}};
static const lean_object* l_Std_Notify_selector___lam__0___closed__1 = (const lean_object*)&l_Std_Notify_selector___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1_value;
static const lean_closure_object l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2 = (const lean_object*)&l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0 = (const lean_object*)&l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__5___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Notify_selector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Notify_selector___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Notify_selector___closed__0 = (const lean_object*)&l_Std_Notify_selector___closed__0_value;
static const lean_closure_object l_Std_Notify_selector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Notify_selector___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Notify_selector___closed__1 = (const lean_object*)&l_Std_Notify_selector___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Notify_selector(lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Notify_Consumer_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Std_Notify_Consumer_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec_ref(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
if (lean_obj_tag(v_t_11_) == 0)
{
lean_object* v_promise_13_; lean_object* v___x_14_; 
v_promise_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_promise_13_);
lean_dec_ref_known(v_t_11_, 1);
v___x_14_ = lean_apply_1(v_k_12_, v_promise_13_);
return v___x_14_;
}
else
{
lean_object* v_finished_15_; lean_object* v___x_16_; 
v_finished_15_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_finished_15_);
lean_dec_ref_known(v_t_11_, 1);
v___x_16_ = lean_apply_1(v_k_12_, v_finished_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorElim(lean_object* v_00_u03b1_17_, lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorElim___boxed(lean_object* v_00_u03b1_24_, lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_Notify_Consumer_ctorElim(v_00_u03b1_24_, v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_normal_elim___redArg(lean_object* v_t_31_, lean_object* v_normal_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_31_, v_normal_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_normal_elim(lean_object* v_00_u03b1_34_, lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_normal_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_36_, v_normal_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_select_elim___redArg(lean_object* v_t_40_, lean_object* v_select_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_40_, v_select_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_select_elim(lean_object* v_00_u03b1_43_, lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_select_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_45_, v_select_47_);
return v___x_48_;
}
}
uint8_t l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(lean_object* v_x_49_, lean_object* v_w_50_, lean_object* v_lose_51_){
_start:
{
lean_object* v_finished_53_; lean_object* v_promise_54_; lean_object* v___x_55_; uint8_t v___y_57_; uint8_t v___x_65_; 
v_finished_53_ = lean_ctor_get(v_w_50_, 0);
v_promise_54_ = lean_ctor_get(v_w_50_, 1);
v___x_55_ = lean_st_ref_take(v_finished_53_);
v___x_65_ = lean_unbox(v___x_55_);
lean_dec(v___x_55_);
if (v___x_65_ == 0)
{
uint8_t v___x_66_; 
v___x_66_ = 1;
v___y_57_ = v___x_66_;
goto v___jp_56_;
}
else
{
uint8_t v___x_67_; 
v___x_67_ = 0;
v___y_57_ = v___x_67_;
goto v___jp_56_;
}
v___jp_56_:
{
uint8_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = 1;
v___x_59_ = lean_box(v___x_58_);
v___x_60_ = lean_st_ref_put(v_finished_53_, v___x_59_);
if (v___y_57_ == 0)
{
lean_object* v___x_61_; uint8_t v___x_62_; 
lean_dec(v_x_49_);
v___x_61_ = lean_apply_1(v_lose_51_, lean_box(0));
v___x_62_ = lean_unbox(v___x_61_);
return v___x_62_;
}
else
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec_ref(v_lose_51_);
v___x_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_63_, 0, v_x_49_);
v___x_64_ = lean_io_promise_resolve(v___x_63_, v_promise_54_);
return v___y_57_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_49_ = stack[0].m_obj;
lean_object* v_w_50_ = stack[1].m_obj;
lean_object* v_lose_51_ = stack[2].m_obj;
uint8_t v_res_68_;
v_res_68_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(v_x_49_, v_w_50_, v_lose_51_);
stack->m_num = v_res_68_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg___boxed(lean_object* v_x_69_, lean_object* v_w_70_, lean_object* v_lose_71_, lean_object* v___y_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(v_x_69_, v_w_70_, v_lose_71_);
lean_dec_ref(v_w_70_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
uint8_t l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(lean_object* v_00_u03b1_75_, lean_object* v_x_76_, lean_object* v_w_77_, lean_object* v_lose_78_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(v_x_76_, v_w_77_, v_lose_78_);
return v___x_80_;
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_76_ = stack[1].m_obj;
lean_object* v_w_77_ = stack[2].m_obj;
lean_object* v_lose_78_ = stack[3].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(lean_box(0), v_x_76_, v_w_77_, v_lose_78_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___boxed(lean_object* v_00_u03b1_82_, lean_object* v_x_83_, lean_object* v_w_84_, lean_object* v_lose_85_, lean_object* v___y_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(v_00_u03b1_82_, v_x_83_, v_w_84_, v_lose_85_);
lean_dec_ref(v_w_84_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
uint8_t l_Std_Notify_Consumer_resolve___redArg___lam__0(uint8_t v___x_89_){
_start:
{
return v___x_89_;
}
}
LEAN_EXPORT void l_Std_Notify_Consumer_resolve___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_89_ = stack[0].m_num;
uint8_t v_res_91_;
v_res_91_ = l_Std_Notify_Consumer_resolve___redArg___lam__0(v___x_89_);
stack->m_num = v_res_91_;
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___redArg___lam__0___boxed(lean_object* v___x_92_, lean_object* v___y_93_){
_start:
{
uint8_t v___x_390__boxed_94_; uint8_t v_res_95_; lean_object* v_r_96_; 
v___x_390__boxed_94_ = lean_unbox(v___x_92_);
v_res_95_ = l_Std_Notify_Consumer_resolve___redArg___lam__0(v___x_390__boxed_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
uint8_t l_Std_Notify_Consumer_resolve___redArg(lean_object* v_c_100_, lean_object* v_x_101_){
_start:
{
if (lean_obj_tag(v_c_100_) == 0)
{
lean_object* v_promise_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_promise_103_ = lean_ctor_get(v_c_100_, 0);
v___x_104_ = lean_io_promise_resolve(v_x_101_, v_promise_103_);
v___x_105_ = 1;
return v___x_105_;
}
else
{
lean_object* v_finished_106_; lean_object* v_lose_107_; uint8_t v___x_108_; 
v_finished_106_ = lean_ctor_get(v_c_100_, 0);
v_lose_107_ = ((lean_object*)(l_Std_Notify_Consumer_resolve___redArg___closed__0));
v___x_108_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(v_x_101_, v_finished_106_, v_lose_107_);
return v___x_108_;
}
}
}
LEAN_EXPORT void l_Std_Notify_Consumer_resolve___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_100_ = stack[0].m_obj;
lean_object* v_x_101_ = stack[1].m_obj;
uint8_t v_res_109_;
v_res_109_ = l_Std_Notify_Consumer_resolve___redArg(v_c_100_, v_x_101_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___redArg___boxed(lean_object* v_c_110_, lean_object* v_x_111_, lean_object* v_a_112_){
_start:
{
uint8_t v_res_113_; lean_object* v_r_114_; 
v_res_113_ = l_Std_Notify_Consumer_resolve___redArg(v_c_110_, v_x_111_);
lean_dec_ref(v_c_110_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
uint8_t l_Std_Notify_Consumer_resolve(lean_object* v_00_u03b1_115_, lean_object* v_c_116_, lean_object* v_x_117_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = l_Std_Notify_Consumer_resolve___redArg(v_c_116_, v_x_117_);
return v___x_119_;
}
}
LEAN_EXPORT void l_Std_Notify_Consumer_resolve_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_116_ = stack[1].m_obj;
lean_object* v_x_117_ = stack[2].m_obj;
uint8_t v_res_120_;
v_res_120_ = l_Std_Notify_Consumer_resolve(lean_box(0), v_c_116_, v_x_117_);
stack->m_num = v_res_120_;
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___boxed(lean_object* v_00_u03b1_121_, lean_object* v_c_122_, lean_object* v_x_123_, lean_object* v_a_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Std_Notify_Consumer_resolve(v_00_u03b1_121_, v_c_122_, v_x_123_);
lean_dec_ref(v_c_122_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
static lean_object* _init_l_Std_Notify_new___closed__0(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Std_Queue_empty___redArg();
return v___x_127_;
}
}
lean_object* l_Std_Notify_new(){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_obj_once(&l_Std_Notify_new___closed__0, &l_Std_Notify_new___closed__0_once, _init_l_Std_Notify_new___closed__0);
v___x_130_ = l_Std_Mutex_new___redArg(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT void l_Std_Notify_new_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_131_;
v_res_131_ = l_Std_Notify_new();
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Std_Notify_new___boxed(lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_Notify_new();
return v_res_133_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(lean_object* v_mutex_134_, lean_object* v_k_135_){
_start:
{
lean_object* v_ref_137_; lean_object* v_mutex_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_ref_137_ = lean_ctor_get(v_mutex_134_, 0);
lean_inc(v_ref_137_);
v_mutex_138_ = lean_ctor_get(v_mutex_134_, 1);
lean_inc(v_mutex_138_);
lean_dec_ref(v_mutex_134_);
v___x_139_ = lean_io_basemutex_lock(v_mutex_138_);
v___x_140_ = lean_apply_2(v_k_135_, v_ref_137_, lean_box(0));
v___x_141_ = lean_io_basemutex_unlock(v_mutex_138_);
lean_dec(v_mutex_138_);
return v___x_140_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_134_ = stack[0].m_obj;
lean_object* v_k_135_ = stack[1].m_obj;
lean_object* v_res_142_;
v_res_142_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_134_, v_k_135_);
stack->m_obj
 = v_res_142_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg___boxed(lean_object* v_mutex_143_, lean_object* v_k_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_143_, v_k_144_);
return v_res_146_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v_mutex_149_, lean_object* v_k_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_149_, v_k_150_);
return v___x_152_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_149_ = stack[2].m_obj;
lean_object* v_k_150_ = stack[3].m_obj;
lean_object* v_res_153_;
v_res_153_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(lean_box(0), lean_box(0), v_mutex_149_, v_k_150_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___boxed(lean_object* v_00_u03b1_154_, lean_object* v_00_u03b2_155_, lean_object* v_mutex_156_, lean_object* v_k_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(v_00_u03b1_154_, v_00_u03b2_155_, v_mutex_156_, v_k_157_);
return v_res_159_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(lean_object* v_a_160_){
_start:
{
lean_object* v___x_162_; 
lean_inc_ref(v_a_160_);
v___x_162_ = l_Std_Queue_dequeue_x3f___redArg(v_a_160_);
if (lean_obj_tag(v___x_162_) == 1)
{
lean_object* v_val_163_; lean_object* v_fst_164_; lean_object* v_snd_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
lean_dec_ref(v_a_160_);
v_val_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_val_163_);
lean_dec_ref_known(v___x_162_, 1);
v_fst_164_ = lean_ctor_get(v_val_163_, 0);
lean_inc(v_fst_164_);
v_snd_165_ = lean_ctor_get(v_val_163_, 1);
lean_inc(v_snd_165_);
lean_dec(v_val_163_);
v___x_166_ = lean_box(0);
v___x_167_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_164_, v___x_166_);
lean_dec(v_fst_164_);
v_a_160_ = v_snd_165_;
goto _start;
}
else
{
lean_dec(v___x_162_);
return v_a_160_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_160_ = stack[0].m_obj;
lean_object* v_res_169_;
v_res_169_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v_a_160_);
stack->m_obj
 = v_res_169_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg___boxed(lean_object* v_a_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v_a_170_);
return v_res_172_;
}
}
lean_object* l_Std_Notify_notify___lam__0(lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; lean_object* v_st_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_175_ = lean_st_ref_get(v___y_173_);
v_st_176_ = lean_obj_once(&l_Std_Notify_new___closed__0, &l_Std_Notify_new___closed__0_once, _init_l_Std_Notify_new___closed__0);
v___x_177_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v___x_175_);
lean_dec_ref(v___x_177_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_st_ref_swap(v___y_173_, v_st_176_);
lean_dec(v___x_179_);
return v___x_178_;
}
}
LEAN_EXPORT void l_Std_Notify_notify___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_173_ = stack[0].m_obj;
lean_object* v_res_180_;
v_res_180_ = l_Std_Notify_notify___lam__0(v___y_173_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Std_Notify_notify___lam__0___boxed(lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_Notify_notify___lam__0(v___y_181_);
lean_dec(v___y_181_);
return v_res_183_;
}
}
lean_object* l_Std_Notify_notify(lean_object* v_x_185_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; 
v___f_187_ = ((lean_object*)(l_Std_Notify_notify___closed__0));
v___x_188_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_185_, v___f_187_);
return v___x_188_;
}
}
LEAN_EXPORT void l_Std_Notify_notify_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_185_ = stack[0].m_obj;
lean_object* v_res_189_;
v_res_189_ = l_Std_Notify_notify(v_x_185_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Std_Notify_notify___boxed(lean_object* v_x_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Notify_notify(v_x_190_);
return v_res_192_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0(lean_object* v_inst_193_, lean_object* v_a_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v_a_194_);
return v___x_197_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_194_ = stack[1].m_obj;
lean_object* v___y_195_ = stack[2].m_obj;
lean_object* v_res_198_;
v_res_198_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0(lean_box(0), v_a_194_, v___y_195_);
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___boxed(lean_object* v_inst_199_, lean_object* v_a_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0(v_inst_199_, v_a_200_, v___y_201_);
lean_dec(v___y_201_);
return v_res_203_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg(lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_box(0);
v___x_219_ = lean_st_ref_get(v___y_216_);
v___x_220_ = l_Std_Queue_dequeue_x3f___redArg(v___x_219_);
if (lean_obj_tag(v___x_220_) == 1)
{
lean_object* v_val_221_; lean_object* v_fst_222_; lean_object* v_snd_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_val_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v___x_220_, 1);
v_fst_222_ = lean_ctor_get(v_val_221_, 0);
lean_inc(v_fst_222_);
v_snd_223_ = lean_ctor_get(v_val_221_, 1);
lean_inc(v_snd_223_);
lean_dec(v_val_221_);
v___x_224_ = lean_st_ref_swap(v___y_216_, v_snd_223_);
lean_dec(v___x_224_);
v___x_225_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_222_, v___x_218_);
lean_dec(v_fst_222_);
if (v___x_225_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__1));
return v___x_227_;
}
}
else
{
lean_object* v___x_228_; 
lean_dec(v___x_220_);
v___x_228_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__3));
return v___x_228_;
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_216_ = stack[0].m_obj;
lean_object* v_res_229_;
v_res_229_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg(v___y_216_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___boxed(lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg(v___y_230_);
lean_dec(v___y_230_);
return v_res_232_;
}
}
uint8_t l_Std_Notify_notifyOne___lam__0(lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; lean_object* v_fst_236_; 
v___x_235_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg(v___y_233_);
v_fst_236_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_fst_236_);
lean_dec_ref(v___x_235_);
if (lean_obj_tag(v_fst_236_) == 0)
{
uint8_t v___x_237_; 
v___x_237_ = 0;
return v___x_237_;
}
else
{
lean_object* v_val_238_; uint8_t v___x_239_; 
v_val_238_ = lean_ctor_get(v_fst_236_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v_fst_236_, 1);
v___x_239_ = lean_unbox(v_val_238_);
lean_dec(v_val_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT void l_Std_Notify_notifyOne___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_233_ = stack[0].m_obj;
uint8_t v_res_240_;
v_res_240_ = l_Std_Notify_notifyOne___lam__0(v___y_233_);
stack->m_num = v_res_240_;
}
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___lam__0___boxed(lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Std_Notify_notifyOne___lam__0(v___y_241_);
lean_dec(v___y_241_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
uint8_t l_Std_Notify_notifyOne(lean_object* v_x_246_){
_start:
{
lean_object* v___f_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___f_248_ = ((lean_object*)(l_Std_Notify_notifyOne___closed__0));
v___x_249_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_246_, v___f_248_);
v___x_250_ = lean_unbox(v___x_249_);
lean_dec(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT void l_Std_Notify_notifyOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_246_ = stack[0].m_obj;
uint8_t v_res_251_;
v_res_251_ = l_Std_Notify_notifyOne(v_x_246_);
stack->m_num = v_res_251_;
}
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___boxed(lean_object* v_x_252_, lean_object* v_a_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Std_Notify_notifyOne(v_x_252_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0(lean_object* v_inst_256_, lean_object* v_a_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg(v___y_258_);
return v___x_260_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_257_ = stack[1].m_obj;
lean_object* v___y_258_ = stack[2].m_obj;
lean_object* v_res_261_;
v_res_261_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0(lean_box(0), v_a_257_, v___y_258_);
stack->m_obj
 = v_res_261_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___boxed(lean_object* v_inst_262_, lean_object* v_a_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0(v_inst_262_, v_a_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v_a_263_);
return v_res_266_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(lean_object* v_mutex_267_, lean_object* v_k_268_){
_start:
{
lean_object* v_ref_270_; lean_object* v_mutex_271_; lean_object* v___x_272_; lean_object* v_r_273_; 
v_ref_270_ = lean_ctor_get(v_mutex_267_, 0);
lean_inc(v_ref_270_);
v_mutex_271_ = lean_ctor_get(v_mutex_267_, 1);
lean_inc(v_mutex_271_);
lean_dec_ref(v_mutex_267_);
v___x_272_ = lean_io_basemutex_lock(v_mutex_271_);
v_r_273_ = lean_apply_2(v_k_268_, v_ref_270_, lean_box(0));
if (lean_obj_tag(v_r_273_) == 0)
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_282_; 
v_a_274_ = lean_ctor_get(v_r_273_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v_r_273_);
if (v_isSharedCheck_282_ == 0)
{
v___x_276_ = v_r_273_;
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v_r_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_282_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lean_io_basemutex_unlock(v_mutex_271_);
lean_dec(v_mutex_271_);
if (v_isShared_277_ == 0)
{
v___x_280_ = v___x_276_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_274_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_291_; 
v_a_283_ = lean_ctor_get(v_r_273_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v_r_273_);
if (v_isSharedCheck_291_ == 0)
{
v___x_285_ = v_r_273_;
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v_r_273_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_291_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = lean_io_basemutex_unlock(v_mutex_271_);
lean_dec(v_mutex_271_);
if (v_isShared_286_ == 0)
{
v___x_289_ = v___x_285_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_283_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_267_ = stack[0].m_obj;
lean_object* v_k_268_ = stack[1].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_267_, v_k_268_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg___boxed(lean_object* v_mutex_293_, lean_object* v_k_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_293_, v_k_294_);
return v_res_296_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_mutex_299_, lean_object* v_k_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_299_, v_k_300_);
return v___x_302_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_299_ = stack[2].m_obj;
lean_object* v_k_300_ = stack[3].m_obj;
lean_object* v_res_303_;
v_res_303_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(lean_box(0), lean_box(0), v_mutex_299_, v_k_300_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___boxed(lean_object* v_00_u03b1_304_, lean_object* v_00_u03b2_305_, lean_object* v_mutex_306_, lean_object* v_k_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(v_00_u03b1_304_, v_00_u03b2_305_, v_mutex_306_, v_k_307_);
return v_res_309_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__1(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_Std_Notify_wait___lam__0___closed__0));
v___x_312_ = lean_mk_io_user_error(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__2(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__1, &l_Std_Notify_wait___lam__0___closed__1_once, _init_l_Std_Notify_wait___lam__0___closed__1);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__3(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__2, &l_Std_Notify_wait___lam__0___closed__2_once, _init_l_Std_Notify_wait___lam__0___closed__2);
v___x_316_ = lean_task_pure(v___x_315_);
return v___x_316_;
}
}
lean_object* l_Std_Notify_wait___lam__0(lean_object* v_a_317_){
_start:
{
if (lean_obj_tag(v_a_317_) == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__3, &l_Std_Notify_wait___lam__0___closed__3_once, _init_l_Std_Notify_wait___lam__0___closed__3);
return v___x_319_;
}
else
{
lean_object* v_val_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_328_; 
v_val_320_ = lean_ctor_get(v_a_317_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_a_317_);
if (v_isSharedCheck_328_ == 0)
{
v___x_322_ = v_a_317_;
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_val_320_);
lean_dec(v_a_317_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_328_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_val_320_);
v___x_325_ = v_reuseFailAlloc_327_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; 
v___x_326_ = lean_task_pure(v___x_325_);
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Notify_wait___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_317_ = stack[0].m_obj;
lean_object* v_res_329_;
v_res_329_ = l_Std_Notify_wait___lam__0(v_a_317_);
stack->m_obj
 = v_res_329_;
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__0___boxed(lean_object* v_a_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Notify_wait___lam__0(v_a_330_);
return v_res_332_;
}
}
lean_object* l_Std_Notify_wait___lam__1(lean_object* v___f_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_336_ = lean_io_promise_new();
v___x_337_ = lean_st_ref_take(v___y_334_);
lean_inc(v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_336_);
v___x_339_ = l_Std_Queue_enqueue___redArg(v___x_338_, v___x_337_);
v___x_340_ = lean_st_ref_put(v___y_334_, v___x_339_);
v___x_341_ = lean_io_promise_result_opt(v___x_336_);
lean_dec(v___x_336_);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = 0;
v___x_344_ = lean_io_bind_task(v___x_341_, v___f_333_, v___x_342_, v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT void l_Std_Notify_wait___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_333_ = stack[0].m_obj;
lean_object* v___y_334_ = stack[1].m_obj;
lean_object* v_res_346_;
v_res_346_ = l_Std_Notify_wait___lam__1(v___f_333_, v___y_334_);
stack->m_obj
 = v_res_346_;
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__1___boxed(lean_object* v___f_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Notify_wait___lam__1(v___f_347_, v___y_348_);
lean_dec(v___y_348_);
return v_res_350_;
}
}
lean_object* l_Std_Notify_wait(lean_object* v_x_354_){
_start:
{
lean_object* v___f_356_; lean_object* v___x_357_; 
v___f_356_ = ((lean_object*)(l_Std_Notify_wait___closed__1));
v___x_357_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_x_354_, v___f_356_);
return v___x_357_;
}
}
LEAN_EXPORT void l_Std_Notify_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_354_ = stack[0].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Std_Notify_wait(v_x_354_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___boxed(lean_object* v_x_359_, lean_object* v_a_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_Notify_wait(v_x_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(lean_object* v___y_362_){
_start:
{
if (lean_obj_tag(v___y_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_a_363_ = lean_ctor_get(v___y_362_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___y_362_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___y_362_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___y_362_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_379_; 
v_a_371_ = lean_ctor_get(v___y_362_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___y_362_);
if (v_isSharedCheck_379_ == 0)
{
v___x_373_ = v___y_362_;
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___y_362_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_fst_375_; lean_object* v___x_377_; 
v_fst_375_ = lean_ctor_get(v_a_371_, 0);
lean_inc(v_fst_375_);
lean_dec(v_a_371_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v_fst_375_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_fst_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(lean_object* v_mutex_380_, lean_object* v_x_381_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = lean_io_basemutex_unlock(v_mutex_380_);
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_380_ = stack[0].m_obj;
lean_object* v_x_381_ = stack[1].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(v_mutex_380_, v_x_381_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed(lean_object* v_mutex_387_, lean_object* v_x_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(v_mutex_387_, v_x_388_);
lean_dec(v_x_388_);
lean_dec(v_mutex_387_);
return v_res_390_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(lean_object* v_k_391_, lean_object* v_ref_392_, lean_object* v_x_393_){
_start:
{
if (lean_obj_tag(v_x_393_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
lean_dec(v_ref_392_);
lean_dec_ref(v_k_391_);
v_a_395_ = lean_ctor_get(v_x_393_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_393_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v_x_393_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v_x_393_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_402_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; 
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
}
else
{
lean_object* v___x_404_; 
lean_dec_ref_known(v_x_393_, 1);
v___x_404_ = lean_apply_2(v_k_391_, v_ref_392_, lean_box(0));
return v___x_404_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_391_ = stack[0].m_obj;
lean_object* v_ref_392_ = stack[1].m_obj;
lean_object* v_x_393_ = stack[2].m_obj;
lean_object* v_res_405_;
v_res_405_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(v_k_391_, v_ref_392_, v_x_393_);
stack->m_obj
 = v_res_405_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed(lean_object* v_k_406_, lean_object* v_ref_407_, lean_object* v_x_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(v_k_406_, v_ref_407_, v_x_408_);
return v_res_410_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(lean_object* v_mutex_411_, lean_object* v___f_412_){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = 0;
v___x_416_ = lean_io_basemutex_lock(v_mutex_411_);
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
v___x_419_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_414_, v___x_415_, v___x_418_, v___f_412_);
return v___x_419_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_411_ = stack[0].m_obj;
lean_object* v___f_412_ = stack[1].m_obj;
lean_object* v_res_420_;
v_res_420_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(v_mutex_411_, v___f_412_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3___boxed(lean_object* v_mutex_421_, lean_object* v___f_422_, lean_object* v___y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(v_mutex_421_, v___f_422_);
lean_dec(v_mutex_421_);
return v_res_424_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(lean_object* v_mutex_426_, lean_object* v_k_427_){
_start:
{
lean_object* v_ref_429_; lean_object* v_mutex_430_; lean_object* v___f_431_; lean_object* v___f_432_; lean_object* v___f_433_; lean_object* v___f_434_; lean_object* v___x_435_; uint8_t v___x_436_; lean_object* v___x_437_; lean_object* v___y_439_; 
v_ref_429_ = lean_ctor_get(v_mutex_426_, 0);
lean_inc(v_ref_429_);
v_mutex_430_ = lean_ctor_get(v_mutex_426_, 1);
lean_inc_n(v_mutex_430_, 2);
lean_dec_ref(v_mutex_426_);
v___f_431_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0));
v___f_432_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_432_, 0, v_mutex_430_);
v___f_433_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_433_, 0, v_k_427_);
lean_closure_set(v___f_433_, 1, v_ref_429_);
v___f_434_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_434_, 0, v_mutex_430_);
lean_closure_set(v___f_434_, 1, v___f_433_);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = 0;
v___x_437_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_434_, v___f_432_, v___x_435_, v___x_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_441_; 
v_a_441_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_437_, 1);
if (lean_obj_tag(v_a_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_a_442_ = lean_ctor_get(v_a_441_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v_a_441_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v_a_441_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v_a_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
v___y_439_ = v___x_447_;
goto v___jp_438_;
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_458_; 
v_a_450_ = lean_ctor_get(v_a_441_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_a_441_);
if (v_isSharedCheck_458_ == 0)
{
v___x_452_ = v_a_441_;
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v_a_441_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_458_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_fst_454_; lean_object* v___x_456_; 
v_fst_454_ = lean_ctor_get(v_a_450_, 0);
lean_inc(v_fst_454_);
lean_dec(v_a_450_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_fst_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_fst_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
v___y_439_ = v___x_456_;
goto v___jp_438_;
}
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_467_; 
v_a_459_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_467_ == 0)
{
v___x_461_ = v___x_437_;
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_437_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_467_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_465_; 
v___x_463_ = lean_task_map(v___f_431_, v_a_459_, v___x_435_, v___x_436_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_463_);
v___x_465_ = v___x_461_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_463_);
v___x_465_ = v_reuseFailAlloc_466_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
return v___x_465_;
}
}
}
v___jp_438_:
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___y_439_);
return v___x_440_;
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_426_ = stack[0].m_obj;
lean_object* v_k_427_ = stack[1].m_obj;
lean_object* v_res_468_;
v_res_468_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_mutex_426_, v_k_427_);
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___boxed(lean_object* v_mutex_469_, lean_object* v_k_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_mutex_469_, v_k_470_);
return v_res_472_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(lean_object* v_00_u03b1_473_, lean_object* v_00_u03b2_474_, lean_object* v_mutex_475_, lean_object* v_k_476_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_mutex_475_, v_k_476_);
return v___x_478_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_475_ = stack[2].m_obj;
lean_object* v_k_476_ = stack[3].m_obj;
lean_object* v_res_479_;
v_res_479_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(lean_box(0), lean_box(0), v_mutex_475_, v_k_476_);
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed(lean_object* v_00_u03b1_480_, lean_object* v_00_u03b2_481_, lean_object* v_mutex_482_, lean_object* v_k_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(v_00_u03b1_480_, v_00_u03b2_481_, v_mutex_482_, v_k_483_);
return v_res_485_;
}
}
lean_object* l_Std_Notify_selector___lam__0(lean_object* v___y_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_491_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_501_; 
v_a_493_ = lean_ctor_get(v_x_491_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v_x_491_);
if (v_isSharedCheck_501_ == 0)
{
v___x_495_ = v_x_491_;
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v_x_491_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_493_);
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
else
{
lean_object* v_a_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_a_502_ = lean_ctor_get(v_x_491_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v_x_491_, 1);
v___x_503_ = lean_st_ref_swap(v___y_490_, v_a_502_);
lean_dec(v___x_503_);
v___x_504_ = ((lean_object*)(l_Std_Notify_selector___lam__0___closed__1));
return v___x_504_;
}
}
}
LEAN_EXPORT void l_Std_Notify_selector___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_490_ = stack[0].m_obj;
lean_object* v_x_491_ = stack[1].m_obj;
lean_object* v_res_505_;
v_res_505_ = l_Std_Notify_selector___lam__0(v___y_490_, v_x_491_);
stack->m_obj
 = v_res_505_;
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__0___boxed(lean_object* v___y_506_, lean_object* v_x_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_Notify_selector___lam__0(v___y_506_, v_x_507_);
lean_dec(v___y_506_);
return v_res_509_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(lean_object* v_x_510_){
_start:
{
uint8_t v___y_513_; 
if (lean_obj_tag(v_x_510_) == 0)
{
lean_object* v___x_517_; 
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v_x_510_);
return v___x_517_;
}
else
{
lean_object* v_a_518_; uint8_t v___x_519_; 
v_a_518_ = lean_ctor_get(v_x_510_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v_x_510_, 1);
v___x_519_ = lean_unbox(v_a_518_);
lean_dec(v_a_518_);
if (v___x_519_ == 0)
{
uint8_t v___x_520_; 
v___x_520_ = 1;
v___y_513_ = v___x_520_;
goto v___jp_512_;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = 0;
v___y_513_ = v___x_521_;
goto v___jp_512_;
}
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_box(v___y_513_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_510_ = stack[0].m_obj;
lean_object* v_res_522_;
v_res_522_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(v_x_510_);
stack->m_obj
 = v_res_522_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1___boxed(lean_object* v_x_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(v_x_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_526_, lean_object* v_x_527_, lean_object* v_head_528_, lean_object* v_x_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(v_tail_526_, v_x_527_, v_head_528_, v_x_529_);
return v_res_531_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_541_, 0, v_x_539_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
else
{
lean_object* v_head_543_; lean_object* v_tail_544_; lean_object* v___f_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_head_543_ = lean_ctor_get(v_x_538_, 0);
lean_inc_n(v_head_543_, 2);
v_tail_544_ = lean_ctor_get(v_x_538_, 1);
lean_inc(v_tail_544_);
lean_dec_ref_known(v_x_538_, 2);
v___f_545_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_545_, 0, v_tail_544_);
lean_closure_set(v___f_545_, 1, v_x_539_);
lean_closure_set(v___f_545_, 2, v_head_543_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = 0;
if (lean_obj_tag(v_head_543_) == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref_known(v_head_543_, 1);
v___x_548_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1));
v___x_549_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_546_, v___x_547_, v___x_548_, v___f_545_);
return v___x_549_;
}
else
{
lean_object* v_finished_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_563_; 
v_finished_550_ = lean_ctor_get(v_head_543_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_head_543_);
if (v_isSharedCheck_563_ == 0)
{
v___x_552_ = v_head_543_;
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_finished_550_);
lean_dec(v_head_543_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_563_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v_finished_554_; lean_object* v___f_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v_finished_554_ = lean_ctor_get(v_finished_550_, 0);
lean_inc(v_finished_554_);
lean_dec_ref(v_finished_550_);
v___f_555_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2));
v___x_556_ = lean_st_ref_get(v_finished_554_);
lean_dec(v_finished_554_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_556_);
v___x_558_ = v___x_552_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_546_, v___x_547_, v___x_559_, v___f_555_);
v___x_561_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_546_, v___x_547_, v___x_560_, v___f_545_);
return v___x_561_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_538_ = stack[0].m_obj;
lean_object* v_x_539_ = stack[1].m_obj;
lean_object* v_res_564_;
v_res_564_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_538_, v_x_539_);
stack->m_obj
 = v_res_564_;
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_565_, lean_object* v_x_566_, lean_object* v_head_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_578_; 
lean_dec_ref(v_head_567_);
lean_dec(v_x_566_);
lean_dec(v_tail_565_);
v_a_570_ = lean_ctor_get(v_x_568_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v_x_568_);
if (v_isSharedCheck_578_ == 0)
{
v___x_572_ = v_x_568_;
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v_x_568_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_578_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
}
else
{
lean_object* v_a_579_; uint8_t v___x_580_; 
v_a_579_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_a_579_);
lean_dec_ref_known(v_x_568_, 1);
v___x_580_ = lean_unbox(v_a_579_);
lean_dec(v_a_579_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; 
lean_dec_ref(v_head_567_);
v___x_581_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_565_, v_x_566_);
return v___x_581_;
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v_head_567_);
lean_ctor_set(v___x_582_, 1, v_x_566_);
v___x_583_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_565_, v___x_582_);
return v___x_583_;
}
}
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_565_ = stack[0].m_obj;
lean_object* v_x_566_ = stack[1].m_obj;
lean_object* v_head_567_ = stack[2].m_obj;
lean_object* v_x_568_ = stack[3].m_obj;
lean_object* v_res_584_;
v_res_584_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(v_tail_565_, v_x_566_, v_head_567_, v_x_568_);
stack->m_obj
 = v_res_584_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___boxed(lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_585_, v_x_586_);
return v_res_588_;
}
}
lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(lean_object* v_x_589_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
lean_object* v___x_591_; 
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v_x_589_);
return v___x_591_;
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_601_; 
v_a_592_ = lean_ctor_get(v_x_589_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_589_);
if (v_isSharedCheck_601_ == 0)
{
v___x_594_ = v_x_589_;
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v_x_589_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_601_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_596_ = l_List_reverse___redArg(v_a_592_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_596_);
v___x_598_ = v___x_594_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_600_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_589_ = stack[0].m_obj;
lean_object* v_res_602_;
v_res_602_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(v_x_589_);
stack->m_obj
 = v_res_602_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0___boxed(lean_object* v_x_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(v_x_603_);
return v_res_605_;
}
}
lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(lean_object* v_a_606_, lean_object* v___x_607_, lean_object* v_x_608_){
_start:
{
if (lean_obj_tag(v_x_608_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_618_; 
lean_dec(v___x_607_);
lean_dec(v_a_606_);
v_a_610_ = lean_ctor_get(v_x_608_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v_x_608_);
if (v_isSharedCheck_618_ == 0)
{
v___x_612_ = v_x_608_;
v_isShared_613_ = v_isSharedCheck_618_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v_x_608_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_618_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_617_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; 
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_635_; 
v_a_619_ = lean_ctor_get(v_x_608_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v_x_608_);
if (v_isSharedCheck_635_ == 0)
{
v___x_621_ = v_x_608_;
v_isShared_622_ = v_isSharedCheck_635_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v_x_608_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_635_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
uint8_t v___x_623_; 
v___x_623_ = l_List_isEmpty___redArg(v_a_606_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_626_; 
lean_dec(v___x_607_);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_a_619_);
lean_ctor_set(v___x_624_, 1, v_a_606_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_624_);
v___x_626_ = v___x_621_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_628_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
lean_dec(v_a_606_);
v___x_629_ = l_List_reverse___redArg(v_a_619_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_607_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_630_);
v___x_632_ = v___x_621_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_634_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; 
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_606_ = stack[0].m_obj;
lean_object* v___x_607_ = stack[1].m_obj;
lean_object* v_x_608_ = stack[2].m_obj;
lean_object* v_res_636_;
v_res_636_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(v_a_606_, v___x_607_, v_x_608_);
stack->m_obj
 = v_res_636_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed(lean_object* v_a_637_, lean_object* v___x_638_, lean_object* v_x_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(v_a_637_, v___x_638_, v_x_639_);
return v_res_641_;
}
}
lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(lean_object* v___x_642_, lean_object* v_eList_643_, lean_object* v___f_644_, lean_object* v_x_645_){
_start:
{
if (lean_obj_tag(v_x_645_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v___f_644_);
lean_dec(v_eList_643_);
lean_dec(v___x_642_);
v_a_647_ = lean_ctor_get(v_x_645_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_645_);
if (v_isSharedCheck_655_ == 0)
{
v___x_649_ = v_x_645_;
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v_x_645_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_654_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___f_657_; lean_object* v___x_658_; uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v_a_656_ = lean_ctor_get(v_x_645_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v_x_645_, 1);
lean_inc(v___x_642_);
v___f_657_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed), 4, 2);
lean_closure_set(v___f_657_, 0, v_a_656_);
lean_closure_set(v___f_657_, 1, v___x_642_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = 0;
v___x_660_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_eList_643_, v___x_642_);
v___x_661_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_658_, v___x_659_, v___x_660_, v___f_644_);
v___x_662_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_658_, v___x_659_, v___x_661_, v___f_657_);
return v___x_662_;
}
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_642_ = stack[0].m_obj;
lean_object* v_eList_643_ = stack[1].m_obj;
lean_object* v___f_644_ = stack[2].m_obj;
lean_object* v_x_645_ = stack[3].m_obj;
lean_object* v_res_663_;
v_res_663_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(v___x_642_, v_eList_643_, v___f_644_, v_x_645_);
stack->m_obj
 = v_res_663_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed(lean_object* v___x_664_, lean_object* v_eList_665_, lean_object* v___f_666_, lean_object* v_x_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(v___x_664_, v_eList_665_, v___f_666_, v_x_667_);
return v_res_669_;
}
}
lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(lean_object* v_q_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_eList_674_; lean_object* v_dList_675_; lean_object* v___f_676_; lean_object* v___x_677_; lean_object* v___f_678_; lean_object* v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_eList_674_ = lean_ctor_get(v_q_671_, 0);
lean_inc(v_eList_674_);
v_dList_675_ = lean_ctor_get(v_q_671_, 1);
lean_inc(v_dList_675_);
lean_dec_ref(v_q_671_);
v___f_676_ = ((lean_object*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0));
v___x_677_ = lean_box(0);
v___f_678_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_678_, 0, v___x_677_);
lean_closure_set(v___f_678_, 1, v_eList_674_);
lean_closure_set(v___f_678_, 2, v___f_676_);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = 0;
v___x_681_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_dList_675_, v___x_677_);
v___x_682_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_679_, v___x_680_, v___x_681_, v___f_676_);
v___x_683_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_679_, v___x_680_, v___x_682_, v___f_678_);
return v___x_683_;
}
}
LEAN_EXPORT void l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_q_671_ = stack[0].m_obj;
lean_object* v___y_672_ = stack[1].m_obj;
lean_object* v_res_684_;
v_res_684_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_q_671_, v___y_672_);
stack->m_obj
 = v_res_684_;
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___boxed(lean_object* v_q_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_q_685_, v___y_686_);
lean_dec(v___y_686_);
return v_res_688_;
}
}
lean_object* l_Std_Notify_selector___lam__1(lean_object* v___y_689_, lean_object* v___f_690_, lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_691_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_701_; 
lean_dec_ref(v___f_690_);
v_a_693_ = lean_ctor_get(v_x_691_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_691_);
if (v_isSharedCheck_701_ == 0)
{
v___x_695_ = v_x_691_;
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v_x_691_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_701_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_700_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_703_; uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_a_702_ = lean_ctor_get(v_x_691_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v_x_691_, 1);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = 0;
v___x_705_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_a_702_, v___y_689_);
v___x_706_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_703_, v___x_704_, v___x_705_, v___f_690_);
return v___x_706_;
}
}
}
LEAN_EXPORT void l_Std_Notify_selector___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_689_ = stack[0].m_obj;
lean_object* v___f_690_ = stack[1].m_obj;
lean_object* v_x_691_ = stack[2].m_obj;
lean_object* v_res_707_;
v_res_707_ = l_Std_Notify_selector___lam__1(v___y_689_, v___f_690_, v_x_691_);
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__1___boxed(lean_object* v___y_708_, lean_object* v___f_709_, lean_object* v_x_710_, lean_object* v___y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_Notify_selector___lam__1(v___y_708_, v___f_709_, v_x_710_);
lean_dec(v___y_708_);
return v_res_712_;
}
}
lean_object* l_Std_Notify_selector___lam__2(lean_object* v___y_713_){
_start:
{
lean_object* v___f_715_; lean_object* v___f_716_; lean_object* v___x_717_; uint8_t v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_inc_n(v___y_713_, 2);
v___f_715_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__0___boxed), 3, 1);
lean_closure_set(v___f_715_, 0, v___y_713_);
v___f_716_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_716_, 0, v___y_713_);
lean_closure_set(v___f_716_, 1, v___f_715_);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = 0;
v___x_719_ = lean_st_ref_get(v___y_713_);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
v___x_722_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_717_, v___x_718_, v___x_721_, v___f_716_);
return v___x_722_;
}
}
LEAN_EXPORT void l_Std_Notify_selector___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_713_ = stack[0].m_obj;
lean_object* v_res_723_;
v_res_723_ = l_Std_Notify_selector___lam__2(v___y_713_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__2___boxed(lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Std_Notify_selector___lam__2(v___y_724_);
lean_dec(v___y_724_);
return v_res_726_;
}
}
lean_object* l_Std_Notify_selector___lam__3(lean_object* v_waiter_727_, lean_object* v___y_728_){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_730_ = lean_st_ref_take(v___y_728_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v_waiter_727_);
v___x_732_ = l_Std_Queue_enqueue___redArg(v___x_731_, v___x_730_);
v___x_733_ = lean_st_ref_put(v___y_728_, v___x_732_);
v___x_734_ = ((lean_object*)(l_Std_Notify_selector___lam__0___closed__1));
return v___x_734_;
}
}
LEAN_EXPORT void l_Std_Notify_selector___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_727_ = stack[0].m_obj;
lean_object* v___y_728_ = stack[1].m_obj;
lean_object* v_res_735_;
v_res_735_ = l_Std_Notify_selector___lam__3(v_waiter_727_, v___y_728_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__3___boxed(lean_object* v_waiter_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_Notify_selector___lam__3(v_waiter_736_, v___y_737_);
lean_dec(v___y_737_);
return v_res_739_;
}
}
lean_object* l_Std_Notify_selector___lam__4(lean_object* v_notify_740_, lean_object* v_waiter_741_){
_start:
{
lean_object* v___f_743_; lean_object* v___x_744_; 
v___f_743_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_743_, 0, v_waiter_741_);
v___x_744_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_notify_740_, v___f_743_);
return v___x_744_;
}
}
LEAN_EXPORT void l_Std_Notify_selector___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_notify_740_ = stack[0].m_obj;
lean_object* v_waiter_741_ = stack[1].m_obj;
lean_object* v_res_745_;
v_res_745_ = l_Std_Notify_selector___lam__4(v_notify_740_, v_waiter_741_);
stack->m_obj
 = v_res_745_;
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__4___boxed(lean_object* v_notify_746_, lean_object* v_waiter_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Std_Notify_selector___lam__4(v_notify_746_, v_waiter_747_);
return v_res_749_;
}
}
lean_object* l_Std_Notify_selector___lam__5(lean_object* v___x_750_){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_750_);
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT void l_Std_Notify_selector___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_750_ = stack[0].m_obj;
lean_object* v_res_754_;
v_res_754_ = l_Std_Notify_selector___lam__5(v___x_750_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__5___boxed(lean_object* v___x_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_Notify_selector___lam__5(v___x_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector(lean_object* v_notify_761_){
_start:
{
lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___f_762_ = ((lean_object*)(l_Std_Notify_selector___closed__0));
lean_inc_ref(v_notify_761_);
v___f_763_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_763_, 0, v_notify_761_);
v___f_764_ = ((lean_object*)(l_Std_Notify_selector___closed__1));
v___x_765_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed), 5, 4);
lean_closure_set(v___x_765_, 0, lean_box(0));
lean_closure_set(v___x_765_, 1, lean_box(0));
lean_closure_set(v___x_765_, 2, v_notify_761_);
lean_closure_set(v___x_765_, 3, v___f_762_);
v___x_766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_766_, 0, v___f_764_);
lean_ctor_set(v___x_766_, 1, v___f_763_);
lean_ctor_set(v___x_766_, 2, v___x_765_);
return v___x_766_;
}
}
lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_767_, v_x_768_);
return v___x_771_;
}
}
LEAN_EXPORT void l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_767_ = stack[0].m_obj;
lean_object* v_x_768_ = stack[1].m_obj;
lean_object* v___y_769_ = stack[2].m_obj;
lean_object* v_res_772_;
v_res_772_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(v_x_767_, v_x_768_, v___y_769_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___boxed(lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(v_x_773_, v_x_774_, v___y_775_);
lean_dec(v___y_775_);
return v_res_777_;
}
}
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Notify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sync_Notify(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Queue(uint8_t builtin);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* initialize_Std_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sync_Notify(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Queue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Notify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sync_Notify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sync_Notify(builtin);
}
#ifdef __cplusplus
}
#endif

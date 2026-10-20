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
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(lean_object* v_x_49_, lean_object* v_w_50_, lean_object* v_lose_51_){
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
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg___boxed(lean_object* v_x_68_, lean_object* v_w_69_, lean_object* v_lose_70_, lean_object* v___y_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(v_x_68_, v_w_69_, v_lose_70_);
lean_dec_ref(v_w_69_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(lean_object* v_00_u03b1_74_, lean_object* v_x_75_, lean_object* v_w_76_, lean_object* v_lose_77_){
_start:
{
uint8_t v___x_79_; 
v___x_79_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(v_x_75_, v_w_76_, v_lose_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___boxed(lean_object* v_00_u03b1_80_, lean_object* v_x_81_, lean_object* v_w_82_, lean_object* v_lose_83_, lean_object* v___y_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(v_00_u03b1_80_, v_x_81_, v_w_82_, v_lose_83_);
lean_dec_ref(v_w_82_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_Consumer_resolve___redArg___lam__0(uint8_t v___x_87_){
_start:
{
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___redArg___lam__0___boxed(lean_object* v___x_89_, lean_object* v___y_90_){
_start:
{
uint8_t v___x_372__boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v___x_372__boxed_91_ = lean_unbox(v___x_89_);
v_res_92_ = l_Std_Notify_Consumer_resolve___redArg___lam__0(v___x_372__boxed_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_Consumer_resolve___redArg(lean_object* v_c_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_c_97_) == 0)
{
lean_object* v_promise_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_promise_100_ = lean_ctor_get(v_c_97_, 0);
v___x_101_ = lean_io_promise_resolve(v_x_98_, v_promise_100_);
v___x_102_ = 1;
return v___x_102_;
}
else
{
lean_object* v_finished_103_; lean_object* v_lose_104_; uint8_t v___x_105_; 
v_finished_103_ = lean_ctor_get(v_c_97_, 0);
v_lose_104_ = ((lean_object*)(l_Std_Notify_Consumer_resolve___redArg___closed__0));
v___x_105_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(v_x_98_, v_finished_103_, v_lose_104_);
return v___x_105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___redArg___boxed(lean_object* v_c_106_, lean_object* v_x_107_, lean_object* v_a_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_Notify_Consumer_resolve___redArg(v_c_106_, v_x_107_);
lean_dec_ref(v_c_106_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_Consumer_resolve(lean_object* v_00_u03b1_111_, lean_object* v_c_112_, lean_object* v_x_113_){
_start:
{
uint8_t v___x_115_; 
v___x_115_ = l_Std_Notify_Consumer_resolve___redArg(v_c_112_, v_x_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___boxed(lean_object* v_00_u03b1_116_, lean_object* v_c_117_, lean_object* v_x_118_, lean_object* v_a_119_){
_start:
{
uint8_t v_res_120_; lean_object* v_r_121_; 
v_res_120_ = l_Std_Notify_Consumer_resolve(v_00_u03b1_116_, v_c_117_, v_x_118_);
lean_dec_ref(v_c_117_);
v_r_121_ = lean_box(v_res_120_);
return v_r_121_;
}
}
static lean_object* _init_l_Std_Notify_new___closed__0(void){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_Std_Queue_empty___redArg();
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_new(){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_obj_once(&l_Std_Notify_new___closed__0, &l_Std_Notify_new___closed__0_once, _init_l_Std_Notify_new___closed__0);
v___x_125_ = l_Std_Mutex_new___redArg(v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_new___boxed(lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Std_Notify_new();
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(lean_object* v_mutex_128_, lean_object* v_k_129_){
_start:
{
lean_object* v_ref_131_; lean_object* v_mutex_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_ref_131_ = lean_ctor_get(v_mutex_128_, 0);
lean_inc(v_ref_131_);
v_mutex_132_ = lean_ctor_get(v_mutex_128_, 1);
lean_inc(v_mutex_132_);
lean_dec_ref(v_mutex_128_);
v___x_133_ = lean_io_basemutex_lock(v_mutex_132_);
v___x_134_ = lean_apply_2(v_k_129_, v_ref_131_, lean_box(0));
v___x_135_ = lean_io_basemutex_unlock(v_mutex_132_);
lean_dec(v_mutex_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg___boxed(lean_object* v_mutex_136_, lean_object* v_k_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_136_, v_k_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(lean_object* v_00_u03b1_140_, lean_object* v_00_u03b2_141_, lean_object* v_mutex_142_, lean_object* v_k_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_142_, v_k_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___boxed(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_mutex_148_, lean_object* v_k_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(v_00_u03b1_146_, v_00_u03b2_147_, v_mutex_148_, v_k_149_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; 
lean_inc_ref(v_a_152_);
v___x_154_ = l_Std_Queue_dequeue_x3f___redArg(v_a_152_);
if (lean_obj_tag(v___x_154_) == 1)
{
lean_object* v_val_155_; lean_object* v_fst_156_; lean_object* v_snd_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
lean_dec_ref(v_a_152_);
v_val_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_val_155_);
lean_dec_ref_known(v___x_154_, 1);
v_fst_156_ = lean_ctor_get(v_val_155_, 0);
lean_inc(v_fst_156_);
v_snd_157_ = lean_ctor_get(v_val_155_, 1);
lean_inc(v_snd_157_);
lean_dec(v_val_155_);
v___x_158_ = lean_box(0);
v___x_159_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_156_, v___x_158_);
lean_dec(v_fst_156_);
v_a_152_ = v_snd_157_;
goto _start;
}
else
{
lean_dec(v___x_154_);
return v_a_152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg___boxed(lean_object* v_a_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v_a_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notify___lam__0(lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; lean_object* v_st_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_166_ = lean_st_ref_get(v___y_164_);
v_st_167_ = lean_obj_once(&l_Std_Notify_new___closed__0, &l_Std_Notify_new___closed__0_once, _init_l_Std_Notify_new___closed__0);
v___x_168_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v___x_166_);
lean_dec_ref(v___x_168_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_st_ref_swap(v___y_164_, v_st_167_);
lean_dec(v___x_170_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notify___lam__0___boxed(lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_Notify_notify___lam__0(v___y_171_);
lean_dec(v___y_171_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notify(lean_object* v_x_175_){
_start:
{
lean_object* v___f_177_; lean_object* v___x_178_; 
v___f_177_ = ((lean_object*)(l_Std_Notify_notify___closed__0));
v___x_178_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_175_, v___f_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notify___boxed(lean_object* v_x_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_Notify_notify(v_x_179_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0(lean_object* v_inst_182_, lean_object* v_a_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v_a_183_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___boxed(lean_object* v_inst_187_, lean_object* v_a_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0(v_inst_187_, v_a_188_, v___y_189_);
lean_dec(v___y_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg(lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_box(0);
v___x_207_ = lean_st_ref_get(v___y_204_);
v___x_208_ = l_Std_Queue_dequeue_x3f___redArg(v___x_207_);
if (lean_obj_tag(v___x_208_) == 1)
{
lean_object* v_val_209_; lean_object* v_fst_210_; lean_object* v_snd_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_val_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_val_209_);
lean_dec_ref_known(v___x_208_, 1);
v_fst_210_ = lean_ctor_get(v_val_209_, 0);
lean_inc(v_fst_210_);
v_snd_211_ = lean_ctor_get(v_val_209_, 1);
lean_inc(v_snd_211_);
lean_dec(v_val_209_);
v___x_212_ = lean_st_ref_swap(v___y_204_, v_snd_211_);
lean_dec(v___x_212_);
v___x_213_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_210_, v___x_206_);
lean_dec(v_fst_210_);
if (v___x_213_ == 0)
{
goto _start;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__1));
return v___x_215_;
}
}
else
{
lean_object* v___x_216_; 
lean_dec(v___x_208_);
v___x_216_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___closed__3));
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg___boxed(lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg(v___y_217_);
lean_dec(v___y_217_);
return v_res_219_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_notifyOne___lam__0(lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; lean_object* v_fst_223_; 
v___x_222_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg(v___y_220_);
v_fst_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_fst_223_);
lean_dec_ref(v___x_222_);
if (lean_obj_tag(v_fst_223_) == 0)
{
uint8_t v___x_224_; 
v___x_224_ = 0;
return v___x_224_;
}
else
{
lean_object* v_val_225_; uint8_t v___x_226_; 
v_val_225_ = lean_ctor_get(v_fst_223_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v_fst_223_, 1);
v___x_226_ = lean_unbox(v_val_225_);
lean_dec(v_val_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___lam__0___boxed(lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
uint8_t v_res_229_; lean_object* v_r_230_; 
v_res_229_ = l_Std_Notify_notifyOne___lam__0(v___y_227_);
lean_dec(v___y_227_);
v_r_230_ = lean_box(v_res_229_);
return v_r_230_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_notifyOne(lean_object* v_x_232_){
_start:
{
lean_object* v___f_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___f_234_ = ((lean_object*)(l_Std_Notify_notifyOne___closed__0));
v___x_235_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_232_, v___f_234_);
v___x_236_ = lean_unbox(v___x_235_);
lean_dec(v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___boxed(lean_object* v_x_237_, lean_object* v_a_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Std_Notify_notifyOne(v_x_237_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0(lean_object* v_inst_241_, lean_object* v_a_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___redArg(v___y_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0___boxed(lean_object* v_inst_246_, lean_object* v_a_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notifyOne_spec__0(v_inst_246_, v_a_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v_a_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(lean_object* v_mutex_251_, lean_object* v_k_252_){
_start:
{
lean_object* v_ref_254_; lean_object* v_mutex_255_; lean_object* v___x_256_; lean_object* v_r_257_; 
v_ref_254_ = lean_ctor_get(v_mutex_251_, 0);
lean_inc(v_ref_254_);
v_mutex_255_ = lean_ctor_get(v_mutex_251_, 1);
lean_inc(v_mutex_255_);
lean_dec_ref(v_mutex_251_);
v___x_256_ = lean_io_basemutex_lock(v_mutex_255_);
v_r_257_ = lean_apply_2(v_k_252_, v_ref_254_, lean_box(0));
if (lean_obj_tag(v_r_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_266_; 
v_a_258_ = lean_ctor_get(v_r_257_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v_r_257_);
if (v_isSharedCheck_266_ == 0)
{
v___x_260_ = v_r_257_;
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v_r_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_266_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_262_ = lean_io_basemutex_unlock(v_mutex_255_);
lean_dec(v_mutex_255_);
if (v_isShared_261_ == 0)
{
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_258_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_275_; 
v_a_267_ = lean_ctor_get(v_r_257_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_r_257_);
if (v_isSharedCheck_275_ == 0)
{
v___x_269_ = v_r_257_;
v_isShared_270_ = v_isSharedCheck_275_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v_r_257_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_275_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_273_; 
v___x_271_ = lean_io_basemutex_unlock(v_mutex_255_);
lean_dec(v_mutex_255_);
if (v_isShared_270_ == 0)
{
v___x_273_ = v___x_269_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_267_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg___boxed(lean_object* v_mutex_276_, lean_object* v_k_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_276_, v_k_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_mutex_282_, lean_object* v_k_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_282_, v_k_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___boxed(lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_, lean_object* v_mutex_288_, lean_object* v_k_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(v_00_u03b1_286_, v_00_u03b2_287_, v_mutex_288_, v_k_289_);
return v_res_291_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__1(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = ((lean_object*)(l_Std_Notify_wait___lam__0___closed__0));
v___x_294_ = lean_mk_io_user_error(v___x_293_);
return v___x_294_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__2(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__1, &l_Std_Notify_wait___lam__0___closed__1_once, _init_l_Std_Notify_wait___lam__0___closed__1);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__3(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__2, &l_Std_Notify_wait___lam__0___closed__2_once, _init_l_Std_Notify_wait___lam__0___closed__2);
v___x_298_ = lean_task_pure(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__0(lean_object* v_a_299_){
_start:
{
if (lean_obj_tag(v_a_299_) == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__3, &l_Std_Notify_wait___lam__0___closed__3_once, _init_l_Std_Notify_wait___lam__0___closed__3);
return v___x_301_;
}
else
{
lean_object* v_val_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_310_; 
v_val_302_ = lean_ctor_get(v_a_299_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v_a_299_);
if (v_isSharedCheck_310_ == 0)
{
v___x_304_ = v_a_299_;
v_isShared_305_ = v_isSharedCheck_310_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_val_302_);
lean_dec(v_a_299_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_310_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_val_302_);
v___x_307_ = v_reuseFailAlloc_309_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; 
v___x_308_ = lean_task_pure(v___x_307_);
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__0___boxed(lean_object* v_a_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_Notify_wait___lam__0(v_a_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__1(lean_object* v___f_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_317_ = lean_io_promise_new();
v___x_318_ = lean_st_ref_take(v___y_315_);
lean_inc(v___x_317_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
v___x_320_ = l_Std_Queue_enqueue___redArg(v___x_319_, v___x_318_);
v___x_321_ = lean_st_ref_put(v___y_315_, v___x_320_);
v___x_322_ = lean_io_promise_result_opt(v___x_317_);
lean_dec(v___x_317_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = 0;
v___x_325_ = lean_io_bind_task(v___x_322_, v___f_314_, v___x_323_, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__1___boxed(lean_object* v___f_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_Notify_wait___lam__1(v___f_327_, v___y_328_);
lean_dec(v___y_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait(lean_object* v_x_334_){
_start:
{
lean_object* v___f_336_; lean_object* v___x_337_; 
v___f_336_ = ((lean_object*)(l_Std_Notify_wait___closed__1));
v___x_337_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_x_334_, v___f_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___boxed(lean_object* v_x_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_Notify_wait(v_x_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(lean_object* v___y_341_){
_start:
{
if (lean_obj_tag(v___y_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
v_a_342_ = lean_ctor_get(v___y_341_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___y_341_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___y_341_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___y_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_358_; 
v_a_350_ = lean_ctor_get(v___y_341_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___y_341_);
if (v_isSharedCheck_358_ == 0)
{
v___x_352_ = v___y_341_;
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___y_341_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_358_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_fst_354_; lean_object* v___x_356_; 
v_fst_354_ = lean_ctor_get(v_a_350_, 0);
lean_inc(v_fst_354_);
lean_dec(v_a_350_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v_fst_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_fst_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(lean_object* v_mutex_359_, lean_object* v_x_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_io_basemutex_unlock(v_mutex_359_);
v___x_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed(lean_object* v_mutex_365_, lean_object* v_x_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(v_mutex_365_, v_x_366_);
lean_dec(v_x_366_);
lean_dec(v_mutex_365_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(lean_object* v_k_369_, lean_object* v_ref_370_, lean_object* v_x_371_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_381_; 
lean_dec(v_ref_370_);
lean_dec_ref(v_k_369_);
v_a_373_ = lean_ctor_get(v_x_371_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_371_);
if (v_isSharedCheck_381_ == 0)
{
v___x_375_ = v_x_371_;
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v_x_371_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_381_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
return v___x_379_;
}
}
}
else
{
lean_object* v___x_382_; 
lean_dec_ref_known(v_x_371_, 1);
v___x_382_ = lean_apply_2(v_k_369_, v_ref_370_, lean_box(0));
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed(lean_object* v_k_383_, lean_object* v_ref_384_, lean_object* v_x_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(v_k_383_, v_ref_384_, v_x_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(lean_object* v_mutex_388_, lean_object* v___f_389_){
_start:
{
lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = 0;
v___x_393_ = lean_io_basemutex_lock(v_mutex_388_);
v___x_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
v___x_396_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_391_, v___x_392_, v___x_395_, v___f_389_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3___boxed(lean_object* v_mutex_397_, lean_object* v___f_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(v_mutex_397_, v___f_398_);
lean_dec(v_mutex_397_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(lean_object* v_mutex_402_, lean_object* v_k_403_){
_start:
{
lean_object* v_ref_405_; lean_object* v_mutex_406_; lean_object* v___f_407_; lean_object* v___f_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___y_415_; 
v_ref_405_ = lean_ctor_get(v_mutex_402_, 0);
lean_inc(v_ref_405_);
v_mutex_406_ = lean_ctor_get(v_mutex_402_, 1);
lean_inc_n(v_mutex_406_, 2);
lean_dec_ref(v_mutex_402_);
v___f_407_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0));
v___f_408_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_408_, 0, v_mutex_406_);
v___f_409_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_409_, 0, v_k_403_);
lean_closure_set(v___f_409_, 1, v_ref_405_);
v___f_410_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_410_, 0, v_mutex_406_);
lean_closure_set(v___f_410_, 1, v___f_409_);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = 0;
v___x_413_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_410_, v___f_408_, v___x_411_, v___x_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_417_; 
v_a_417_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_413_, 1);
if (lean_obj_tag(v_a_417_) == 0)
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_a_418_ = lean_ctor_get(v_a_417_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_a_417_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v_a_417_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v_a_417_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
v___y_415_ = v___x_423_;
goto v___jp_414_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_434_; 
v_a_426_ = lean_ctor_get(v_a_417_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_a_417_);
if (v_isSharedCheck_434_ == 0)
{
v___x_428_ = v_a_417_;
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v_a_417_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_434_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_fst_430_; lean_object* v___x_432_; 
v_fst_430_ = lean_ctor_get(v_a_426_, 0);
lean_inc(v_fst_430_);
lean_dec(v_a_426_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_fst_430_);
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_fst_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
v___y_415_ = v___x_432_;
goto v___jp_414_;
}
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_443_; 
v_a_435_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_443_ == 0)
{
v___x_437_ = v___x_413_;
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_413_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_443_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_439_ = lean_task_map(v___f_407_, v_a_435_, v___x_411_, v___x_412_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_439_);
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
v___jp_414_:
{
lean_object* v___x_416_; 
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___y_415_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___boxed(lean_object* v_mutex_444_, lean_object* v_k_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_mutex_444_, v_k_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(lean_object* v_00_u03b1_448_, lean_object* v_00_u03b2_449_, lean_object* v_mutex_450_, lean_object* v_k_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_mutex_450_, v_k_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed(lean_object* v_00_u03b1_454_, lean_object* v_00_u03b2_455_, lean_object* v_mutex_456_, lean_object* v_k_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(v_00_u03b1_454_, v_00_u03b2_455_, v_mutex_456_, v_k_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__0(lean_object* v___y_464_, lean_object* v_x_465_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_475_; 
v_a_467_ = lean_ctor_get(v_x_465_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_465_);
if (v_isSharedCheck_475_ == 0)
{
v___x_469_ = v_x_465_;
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v_x_465_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_474_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; 
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
}
}
else
{
lean_object* v_a_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_a_476_ = lean_ctor_get(v_x_465_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v_x_465_, 1);
v___x_477_ = lean_st_ref_swap(v___y_464_, v_a_476_);
lean_dec(v___x_477_);
v___x_478_ = ((lean_object*)(l_Std_Notify_selector___lam__0___closed__1));
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__0___boxed(lean_object* v___y_479_, lean_object* v_x_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_Notify_selector___lam__0(v___y_479_, v_x_480_);
lean_dec(v___y_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(lean_object* v_x_483_){
_start:
{
uint8_t v___y_486_; 
if (lean_obj_tag(v_x_483_) == 0)
{
lean_object* v___x_490_; 
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v_x_483_);
return v___x_490_;
}
else
{
lean_object* v_a_491_; uint8_t v___x_492_; 
v_a_491_ = lean_ctor_get(v_x_483_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v_x_483_, 1);
v___x_492_ = lean_unbox(v_a_491_);
lean_dec(v_a_491_);
if (v___x_492_ == 0)
{
uint8_t v___x_493_; 
v___x_493_ = 1;
v___y_486_ = v___x_493_;
goto v___jp_485_;
}
else
{
uint8_t v___x_494_; 
v___x_494_ = 0;
v___y_486_ = v___x_494_;
goto v___jp_485_;
}
}
v___jp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_box(v___y_486_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1___boxed(lean_object* v_x_495_, lean_object* v___y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(v_x_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_498_, lean_object* v_x_499_, lean_object* v_head_500_, lean_object* v_x_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(v_tail_498_, v_x_499_, v_head_500_, v_x_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v_x_511_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
else
{
lean_object* v_head_515_; lean_object* v_tail_516_; lean_object* v___f_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v_head_515_ = lean_ctor_get(v_x_510_, 0);
lean_inc_n(v_head_515_, 2);
v_tail_516_ = lean_ctor_get(v_x_510_, 1);
lean_inc(v_tail_516_);
lean_dec_ref_known(v_x_510_, 2);
v___f_517_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_517_, 0, v_tail_516_);
lean_closure_set(v___f_517_, 1, v_x_511_);
lean_closure_set(v___f_517_, 2, v_head_515_);
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = 0;
if (lean_obj_tag(v_head_515_) == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec_ref_known(v_head_515_, 1);
v___x_520_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1));
v___x_521_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_518_, v___x_519_, v___x_520_, v___f_517_);
return v___x_521_;
}
else
{
lean_object* v_finished_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_535_; 
v_finished_522_ = lean_ctor_get(v_head_515_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_head_515_);
if (v_isSharedCheck_535_ == 0)
{
v___x_524_ = v_head_515_;
v_isShared_525_ = v_isSharedCheck_535_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_finished_522_);
lean_dec(v_head_515_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_535_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_finished_526_; lean_object* v___f_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v_finished_526_ = lean_ctor_get(v_finished_522_, 0);
lean_inc(v_finished_526_);
lean_dec_ref(v_finished_522_);
v___f_527_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2));
v___x_528_ = lean_st_ref_get(v_finished_526_);
lean_dec(v_finished_526_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_528_);
v___x_530_ = v___x_524_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_534_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_518_, v___x_519_, v___x_531_, v___f_527_);
v___x_533_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_518_, v___x_519_, v___x_532_, v___f_517_);
return v___x_533_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_536_, lean_object* v_x_537_, lean_object* v_head_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_539_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_549_; 
lean_dec_ref(v_head_538_);
lean_dec(v_x_537_);
lean_dec(v_tail_536_);
v_a_541_ = lean_ctor_get(v_x_539_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v_x_539_);
if (v_isSharedCheck_549_ == 0)
{
v___x_543_ = v_x_539_;
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v_x_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_549_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_548_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
lean_object* v___x_547_; 
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
else
{
lean_object* v_a_550_; uint8_t v___x_551_; 
v_a_550_ = lean_ctor_get(v_x_539_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v_x_539_, 1);
v___x_551_ = lean_unbox(v_a_550_);
lean_dec(v_a_550_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_dec_ref(v_head_538_);
v___x_552_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_536_, v_x_537_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_553_, 0, v_head_538_);
lean_ctor_set(v___x_553_, 1, v_x_537_);
v___x_554_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_536_, v___x_553_);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___boxed(lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_555_, v_x_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(lean_object* v_x_559_){
_start:
{
if (lean_obj_tag(v_x_559_) == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_x_559_);
return v___x_561_;
}
else
{
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_571_; 
v_a_562_ = lean_ctor_get(v_x_559_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v_x_559_);
if (v_isSharedCheck_571_ == 0)
{
v___x_564_ = v_x_559_;
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v_x_559_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = l_List_reverse___redArg(v_a_562_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_570_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; 
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0___boxed(lean_object* v_x_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(v_x_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(lean_object* v_a_575_, lean_object* v___x_576_, lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_587_; 
lean_dec(v___x_576_);
lean_dec(v_a_575_);
v_a_579_ = lean_ctor_get(v_x_577_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_577_);
if (v_isSharedCheck_587_ == 0)
{
v___x_581_ = v_x_577_;
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v_x_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_587_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_586_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_604_; 
v_a_588_ = lean_ctor_get(v_x_577_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_577_);
if (v_isSharedCheck_604_ == 0)
{
v___x_590_ = v_x_577_;
v_isShared_591_ = v_isSharedCheck_604_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v_x_577_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_604_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
uint8_t v___x_592_; 
v___x_592_ = l_List_isEmpty___redArg(v_a_575_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_595_; 
lean_dec(v___x_576_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_a_588_);
lean_ctor_set(v___x_593_, 1, v_a_575_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_593_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
lean_dec(v_a_575_);
v___x_598_ = l_List_reverse___redArg(v_a_588_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_576_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_599_);
v___x_601_ = v___x_590_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_603_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
lean_object* v___x_602_; 
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed(lean_object* v_a_605_, lean_object* v___x_606_, lean_object* v_x_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(v_a_605_, v___x_606_, v_x_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(lean_object* v___x_610_, lean_object* v_eList_611_, lean_object* v___f_612_, lean_object* v_x_613_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v___f_612_);
lean_dec(v_eList_611_);
lean_dec(v___x_610_);
v_a_615_ = lean_ctor_get(v_x_613_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_613_);
if (v_isSharedCheck_623_ == 0)
{
v___x_617_ = v_x_613_;
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v_x_613_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_623_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___f_625_; lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_a_624_ = lean_ctor_get(v_x_613_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v_x_613_, 1);
lean_inc(v___x_610_);
v___f_625_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed), 4, 2);
lean_closure_set(v___f_625_, 0, v_a_624_);
lean_closure_set(v___f_625_, 1, v___x_610_);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = 0;
v___x_628_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_eList_611_, v___x_610_);
v___x_629_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_626_, v___x_627_, v___x_628_, v___f_612_);
v___x_630_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_626_, v___x_627_, v___x_629_, v___f_625_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed(lean_object* v___x_631_, lean_object* v_eList_632_, lean_object* v___f_633_, lean_object* v_x_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(v___x_631_, v_eList_632_, v___f_633_, v_x_634_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(lean_object* v_q_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_eList_641_; lean_object* v_dList_642_; lean_object* v___f_643_; lean_object* v___x_644_; lean_object* v___f_645_; lean_object* v___x_646_; uint8_t v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_eList_641_ = lean_ctor_get(v_q_638_, 0);
lean_inc(v_eList_641_);
v_dList_642_ = lean_ctor_get(v_q_638_, 1);
lean_inc(v_dList_642_);
lean_dec_ref(v_q_638_);
v___f_643_ = ((lean_object*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0));
v___x_644_ = lean_box(0);
v___f_645_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_645_, 0, v___x_644_);
lean_closure_set(v___f_645_, 1, v_eList_641_);
lean_closure_set(v___f_645_, 2, v___f_643_);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = 0;
v___x_648_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_dList_642_, v___x_644_);
v___x_649_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_646_, v___x_647_, v___x_648_, v___f_643_);
v___x_650_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_646_, v___x_647_, v___x_649_, v___f_645_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___boxed(lean_object* v_q_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_q_651_, v___y_652_);
lean_dec(v___y_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__1(lean_object* v___y_655_, lean_object* v___f_656_, lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v___f_656_);
v_a_659_ = lean_ctor_get(v_x_657_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_x_657_);
if (v_isSharedCheck_667_ == 0)
{
v___x_661_ = v_x_657_;
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v_x_657_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_667_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_666_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
}
else
{
lean_object* v_a_668_; lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_a_668_ = lean_ctor_get(v_x_657_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v_x_657_, 1);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = 0;
v___x_671_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_a_668_, v___y_655_);
v___x_672_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_669_, v___x_670_, v___x_671_, v___f_656_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__1___boxed(lean_object* v___y_673_, lean_object* v___f_674_, lean_object* v_x_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Std_Notify_selector___lam__1(v___y_673_, v___f_674_, v_x_675_);
lean_dec(v___y_673_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__2(lean_object* v___y_678_){
_start:
{
lean_object* v___f_680_; lean_object* v___f_681_; lean_object* v___x_682_; uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_inc_n(v___y_678_, 2);
v___f_680_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__0___boxed), 3, 1);
lean_closure_set(v___f_680_, 0, v___y_678_);
v___f_681_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_681_, 0, v___y_678_);
lean_closure_set(v___f_681_, 1, v___f_680_);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = 0;
v___x_684_ = lean_st_ref_get(v___y_678_);
v___x_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
v___x_687_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_682_, v___x_683_, v___x_686_, v___f_681_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__2___boxed(lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_Notify_selector___lam__2(v___y_688_);
lean_dec(v___y_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__3(lean_object* v_waiter_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_694_ = lean_st_ref_take(v___y_692_);
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v_waiter_691_);
v___x_696_ = l_Std_Queue_enqueue___redArg(v___x_695_, v___x_694_);
v___x_697_ = lean_st_ref_put(v___y_692_, v___x_696_);
v___x_698_ = ((lean_object*)(l_Std_Notify_selector___lam__0___closed__1));
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__3___boxed(lean_object* v_waiter_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_Notify_selector___lam__3(v_waiter_699_, v___y_700_);
lean_dec(v___y_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__4(lean_object* v_notify_703_, lean_object* v_waiter_704_){
_start:
{
lean_object* v___f_706_; lean_object* v___x_707_; 
v___f_706_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_706_, 0, v_waiter_704_);
v___x_707_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_notify_703_, v___f_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__4___boxed(lean_object* v_notify_708_, lean_object* v_waiter_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_Notify_selector___lam__4(v_notify_708_, v_waiter_709_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__5(lean_object* v___x_712_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__5___boxed(lean_object* v___x_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_Notify_selector___lam__5(v___x_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector(lean_object* v_notify_722_){
_start:
{
lean_object* v___f_723_; lean_object* v___f_724_; lean_object* v___f_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___f_723_ = ((lean_object*)(l_Std_Notify_selector___closed__0));
lean_inc_ref(v_notify_722_);
v___f_724_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_724_, 0, v_notify_722_);
v___f_725_ = ((lean_object*)(l_Std_Notify_selector___closed__1));
v___x_726_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed), 5, 4);
lean_closure_set(v___x_726_, 0, lean_box(0));
lean_closure_set(v___x_726_, 1, lean_box(0));
lean_closure_set(v___x_726_, 2, v_notify_722_);
lean_closure_set(v___x_726_, 3, v___f_723_);
v___x_727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_727_, 0, v___f_725_);
lean_ctor_set(v___x_727_, 1, v___f_724_);
lean_ctor_set(v___x_727_, 2, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_728_, v_x_729_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___boxed(lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(v_x_733_, v_x_734_, v___y_735_);
lean_dec(v___y_735_);
return v_res_737_;
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

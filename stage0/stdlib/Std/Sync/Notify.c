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
lean_object* l_Std_Mutex_new___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Notify_notifyOne___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Notify_notifyOne___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Notify_notifyOne___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Notify_notifyOne___closed__0 = (const lean_object*)&l_Std_Notify_notifyOne___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Notify_notifyOne(lean_object*);
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_Notify_Consumer_ctorIdx___redArg(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx(lean_object* v_00_u03b1_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Std_Notify_Consumer_ctorIdx___redArg(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorIdx___boxed(lean_object* v_00_u03b1_9_, lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Std_Notify_Consumer_ctorIdx(v_00_u03b1_9_, v_x_10_);
lean_dec_ref(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
if (lean_obj_tag(v_t_12_) == 0)
{
lean_object* v_promise_14_; lean_object* v___x_15_; 
v_promise_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_promise_14_);
lean_dec_ref_known(v_t_12_, 1);
v___x_15_ = lean_apply_1(v_k_13_, v_promise_14_);
return v___x_15_;
}
else
{
lean_object* v_finished_16_; lean_object* v___x_17_; 
v_finished_16_ = lean_ctor_get(v_t_12_, 0);
lean_inc_ref(v_finished_16_);
lean_dec_ref_known(v_t_12_, 1);
v___x_17_ = lean_apply_1(v_k_13_, v_finished_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorElim(lean_object* v_00_u03b1_18_, lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_ctorElim___boxed(lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Notify_Consumer_ctorElim(v_00_u03b1_25_, v_motive_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_normal_elim___redArg(lean_object* v_t_32_, lean_object* v_normal_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_32_, v_normal_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_normal_elim(lean_object* v_00_u03b1_35_, lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_normal_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_37_, v_normal_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_select_elim___redArg(lean_object* v_t_41_, lean_object* v_select_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_41_, v_select_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_select_elim(lean_object* v_00_u03b1_44_, lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_select_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_46_, v_select_48_);
return v___x_49_;
}
}
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(lean_object* v_x_50_, lean_object* v_w_51_, lean_object* v_lose_52_){
_start:
{
lean_object* v_finished_54_; lean_object* v_promise_55_; lean_object* v___x_56_; uint8_t v___y_58_; uint8_t v___x_66_; 
v_finished_54_ = lean_ctor_get(v_w_51_, 0);
v_promise_55_ = lean_ctor_get(v_w_51_, 1);
v___x_56_ = lean_st_ref_take(v_finished_54_);
v___x_66_ = lean_unbox(v___x_56_);
lean_dec(v___x_56_);
if (v___x_66_ == 0)
{
uint8_t v___x_67_; 
v___x_67_ = 1;
v___y_58_ = v___x_67_;
goto v___jp_57_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = 0;
v___y_58_ = v___x_68_;
goto v___jp_57_;
}
v___jp_57_:
{
uint8_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = 1;
v___x_60_ = lean_box(v___x_59_);
v___x_61_ = lean_st_ref_put(v_finished_54_, v___x_60_);
if (v___y_58_ == 0)
{
lean_object* v___x_62_; uint8_t v___x_63_; 
lean_dec(v_x_50_);
v___x_62_ = lean_apply_1(v_lose_52_, lean_box(0));
v___x_63_ = lean_unbox(v___x_62_);
return v___x_63_;
}
else
{
lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec_ref(v_lose_52_);
v___x_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_64_, 0, v_x_50_);
v___x_65_ = lean_io_promise_resolve(v___x_64_, v_promise_55_);
return v___y_58_;
}
}
}
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
LEAN_EXPORT uint8_t l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(lean_object* v_00_u03b1_75_, lean_object* v_x_76_, lean_object* v_w_77_, lean_object* v_lose_78_){
_start:
{
uint8_t v___x_80_; 
v___x_80_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(v_x_76_, v_w_77_, v_lose_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___boxed(lean_object* v_00_u03b1_81_, lean_object* v_x_82_, lean_object* v_w_83_, lean_object* v_lose_84_, lean_object* v___y_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(v_00_u03b1_81_, v_x_82_, v_w_83_, v_lose_84_);
lean_dec_ref(v_w_83_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_Consumer_resolve___redArg___lam__0(uint8_t v___x_88_){
_start:
{
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___redArg___lam__0___boxed(lean_object* v___x_90_, lean_object* v___y_91_){
_start:
{
uint8_t v___x_406__boxed_92_; uint8_t v_res_93_; lean_object* v_r_94_; 
v___x_406__boxed_92_ = lean_unbox(v___x_90_);
v_res_93_ = l_Std_Notify_Consumer_resolve___redArg___lam__0(v___x_406__boxed_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_Consumer_resolve___redArg(lean_object* v_c_98_, lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_c_98_) == 0)
{
lean_object* v_promise_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v_promise_101_ = lean_ctor_get(v_c_98_, 0);
v___x_102_ = lean_io_promise_resolve(v_x_99_, v_promise_101_);
v___x_103_ = 1;
return v___x_103_;
}
else
{
lean_object* v_finished_104_; lean_object* v_lose_105_; uint8_t v___x_106_; 
v_finished_104_ = lean_ctor_get(v_c_98_, 0);
v_lose_105_ = ((lean_object*)(l_Std_Notify_Consumer_resolve___redArg___closed__0));
v___x_106_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(v_x_99_, v_finished_104_, v_lose_105_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___redArg___boxed(lean_object* v_c_107_, lean_object* v_x_108_, lean_object* v_a_109_){
_start:
{
uint8_t v_res_110_; lean_object* v_r_111_; 
v_res_110_ = l_Std_Notify_Consumer_resolve___redArg(v_c_107_, v_x_108_);
lean_dec_ref(v_c_107_);
v_r_111_ = lean_box(v_res_110_);
return v_r_111_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_Consumer_resolve(lean_object* v_00_u03b1_112_, lean_object* v_c_113_, lean_object* v_x_114_){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = l_Std_Notify_Consumer_resolve___redArg(v_c_113_, v_x_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_Consumer_resolve___boxed(lean_object* v_00_u03b1_117_, lean_object* v_c_118_, lean_object* v_x_119_, lean_object* v_a_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Std_Notify_Consumer_resolve(v_00_u03b1_117_, v_c_118_, v_x_119_);
lean_dec_ref(v_c_118_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
static lean_object* _init_l_Std_Notify_new___closed__0(void){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = l_Std_Queue_empty___redArg();
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_new(){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_obj_once(&l_Std_Notify_new___closed__0, &l_Std_Notify_new___closed__0_once, _init_l_Std_Notify_new___closed__0);
v___x_126_ = l_Std_Mutex_new___redArg(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_new___boxed(lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Std_Notify_new();
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(lean_object* v_mutex_129_, lean_object* v_k_130_){
_start:
{
lean_object* v_ref_132_; lean_object* v_mutex_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_ref_132_ = lean_ctor_get(v_mutex_129_, 0);
lean_inc(v_ref_132_);
v_mutex_133_ = lean_ctor_get(v_mutex_129_, 1);
lean_inc(v_mutex_133_);
lean_dec_ref(v_mutex_129_);
v___x_134_ = lean_io_basemutex_lock(v_mutex_133_);
v___x_135_ = lean_apply_2(v_k_130_, v_ref_132_, lean_box(0));
v___x_136_ = lean_io_basemutex_unlock(v_mutex_133_);
lean_dec(v_mutex_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg___boxed(lean_object* v_mutex_137_, lean_object* v_k_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_137_, v_k_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_mutex_143_, lean_object* v_k_144_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_143_, v_k_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___boxed(lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v_mutex_149_, lean_object* v_k_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(v_00_u03b1_147_, v_00_u03b2_148_, v_mutex_149_, v_k_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(lean_object* v_a_153_){
_start:
{
lean_object* v___x_155_; 
lean_inc_ref(v_a_153_);
v___x_155_ = l_Std_Queue_dequeue_x3f___redArg(v_a_153_);
if (lean_obj_tag(v___x_155_) == 1)
{
lean_object* v_val_156_; lean_object* v_fst_157_; lean_object* v_snd_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
lean_dec_ref(v_a_153_);
v_val_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_val_156_);
lean_dec_ref_known(v___x_155_, 1);
v_fst_157_ = lean_ctor_get(v_val_156_, 0);
lean_inc(v_fst_157_);
v_snd_158_ = lean_ctor_get(v_val_156_, 1);
lean_inc(v_snd_158_);
lean_dec(v_val_156_);
v___x_159_ = lean_box(0);
v___x_160_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_157_, v___x_159_);
lean_dec(v_fst_157_);
v_a_153_ = v_snd_158_;
goto _start;
}
else
{
lean_dec(v___x_155_);
return v_a_153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg___boxed(lean_object* v_a_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v_a_162_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notify___lam__0(lean_object* v___y_165_){
_start:
{
lean_object* v___x_167_; lean_object* v_st_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_167_ = lean_st_ref_get(v___y_165_);
v_st_168_ = lean_obj_once(&l_Std_Notify_new___closed__0, &l_Std_Notify_new___closed__0_once, _init_l_Std_Notify_new___closed__0);
v___x_169_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v___x_167_);
lean_dec_ref(v___x_169_);
v___x_170_ = lean_box(0);
v___x_171_ = lean_st_ref_swap(v___y_165_, v_st_168_);
lean_dec(v___x_171_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notify___lam__0___boxed(lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_Notify_notify___lam__0(v___y_172_);
lean_dec(v___y_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notify(lean_object* v_x_176_){
_start:
{
lean_object* v___f_178_; lean_object* v___x_179_; 
v___f_178_ = ((lean_object*)(l_Std_Notify_notify___closed__0));
v___x_179_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_176_, v___f_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notify___boxed(lean_object* v_x_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Notify_notify(v_x_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0(lean_object* v_inst_183_, lean_object* v_a_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v_a_184_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___boxed(lean_object* v_inst_188_, lean_object* v_a_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0(v_inst_188_, v_a_189_, v___y_190_);
lean_dec(v___y_190_);
return v_res_192_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_notifyOne___lam__0(lean_object* v___y_193_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_st_ref_get(v___y_193_);
v___x_196_ = l_Std_Queue_dequeue_x3f___redArg(v___x_195_);
if (lean_obj_tag(v___x_196_) == 1)
{
lean_object* v_val_197_; lean_object* v_fst_198_; lean_object* v_snd_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_val_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v___x_196_, 1);
v_fst_198_ = lean_ctor_get(v_val_197_, 0);
lean_inc(v_fst_198_);
v_snd_199_ = lean_ctor_get(v_val_197_, 1);
lean_inc(v_snd_199_);
lean_dec(v_val_197_);
v___x_200_ = lean_st_ref_swap(v___y_193_, v_snd_199_);
lean_dec(v___x_200_);
v___x_201_ = lean_box(0);
v___x_202_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_198_, v___x_201_);
lean_dec(v_fst_198_);
return v___x_202_;
}
else
{
uint8_t v___x_203_; 
lean_dec(v___x_196_);
v___x_203_ = 0;
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___lam__0___boxed(lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = l_Std_Notify_notifyOne___lam__0(v___y_204_);
lean_dec(v___y_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_notifyOne(lean_object* v_x_209_){
_start:
{
lean_object* v___f_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v___f_211_ = ((lean_object*)(l_Std_Notify_notifyOne___closed__0));
v___x_212_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_209_, v___f_211_);
v___x_213_ = lean_unbox(v___x_212_);
lean_dec(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___boxed(lean_object* v_x_214_, lean_object* v_a_215_){
_start:
{
uint8_t v_res_216_; lean_object* v_r_217_; 
v_res_216_ = l_Std_Notify_notifyOne(v_x_214_);
v_r_217_ = lean_box(v_res_216_);
return v_r_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(lean_object* v_mutex_218_, lean_object* v_k_219_){
_start:
{
lean_object* v_ref_221_; lean_object* v_mutex_222_; lean_object* v___x_223_; lean_object* v_r_224_; 
v_ref_221_ = lean_ctor_get(v_mutex_218_, 0);
lean_inc(v_ref_221_);
v_mutex_222_ = lean_ctor_get(v_mutex_218_, 1);
lean_inc(v_mutex_222_);
lean_dec_ref(v_mutex_218_);
v___x_223_ = lean_io_basemutex_lock(v_mutex_222_);
v_r_224_ = lean_apply_2(v_k_219_, v_ref_221_, lean_box(0));
if (lean_obj_tag(v_r_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_233_; 
v_a_225_ = lean_ctor_get(v_r_224_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v_r_224_);
if (v_isSharedCheck_233_ == 0)
{
v___x_227_ = v_r_224_;
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v_r_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_233_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_229_ = lean_io_basemutex_unlock(v_mutex_222_);
lean_dec(v_mutex_222_);
if (v_isShared_228_ == 0)
{
v___x_231_ = v___x_227_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_225_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_242_; 
v_a_234_ = lean_ctor_get(v_r_224_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_r_224_);
if (v_isSharedCheck_242_ == 0)
{
v___x_236_ = v_r_224_;
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v_r_224_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_242_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_240_; 
v___x_238_ = lean_io_basemutex_unlock(v_mutex_222_);
lean_dec(v_mutex_222_);
if (v_isShared_237_ == 0)
{
v___x_240_ = v___x_236_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_234_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg___boxed(lean_object* v_mutex_243_, lean_object* v_k_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_243_, v_k_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_mutex_249_, lean_object* v_k_250_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_249_, v_k_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___boxed(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_mutex_255_, lean_object* v_k_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(v_00_u03b1_253_, v_00_u03b2_254_, v_mutex_255_, v_k_256_);
return v_res_258_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__1(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_Std_Notify_wait___lam__0___closed__0));
v___x_261_ = lean_mk_io_user_error(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__2(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__1, &l_Std_Notify_wait___lam__0___closed__1_once, _init_l_Std_Notify_wait___lam__0___closed__1);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__3(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__2, &l_Std_Notify_wait___lam__0___closed__2_once, _init_l_Std_Notify_wait___lam__0___closed__2);
v___x_265_ = lean_task_pure(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__0(lean_object* v_a_266_){
_start:
{
if (lean_obj_tag(v_a_266_) == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__3, &l_Std_Notify_wait___lam__0___closed__3_once, _init_l_Std_Notify_wait___lam__0___closed__3);
return v___x_268_;
}
else
{
lean_object* v_val_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_val_269_ = lean_ctor_get(v_a_266_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_a_266_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v_a_266_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_val_269_);
lean_dec(v_a_266_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_val_269_);
v___x_274_ = v_reuseFailAlloc_276_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; 
v___x_275_ = lean_task_pure(v___x_274_);
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__0___boxed(lean_object* v_a_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Std_Notify_wait___lam__0(v_a_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__1(lean_object* v___f_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_284_ = lean_io_promise_new();
v___x_285_ = lean_st_ref_take(v___y_282_);
lean_inc(v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
v___x_287_ = l_Std_Queue_enqueue___redArg(v___x_286_, v___x_285_);
v___x_288_ = lean_st_ref_put(v___y_282_, v___x_287_);
v___x_289_ = lean_io_promise_result_opt(v___x_284_);
lean_dec(v___x_284_);
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = 0;
v___x_292_ = lean_io_bind_task(v___x_289_, v___f_281_, v___x_290_, v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__1___boxed(lean_object* v___f_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_Notify_wait___lam__1(v___f_294_, v___y_295_);
lean_dec(v___y_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait(lean_object* v_x_301_){
_start:
{
lean_object* v___f_303_; lean_object* v___x_304_; 
v___f_303_ = ((lean_object*)(l_Std_Notify_wait___closed__1));
v___x_304_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_x_301_, v___f_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___boxed(lean_object* v_x_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_Notify_wait(v_x_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(lean_object* v___y_308_){
_start:
{
if (lean_obj_tag(v___y_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_a_309_ = lean_ctor_get(v___y_308_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___y_308_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___y_308_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___y_308_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_325_; 
v_a_317_ = lean_ctor_get(v___y_308_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___y_308_);
if (v_isSharedCheck_325_ == 0)
{
v___x_319_ = v___y_308_;
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___y_308_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v_fst_321_; lean_object* v___x_323_; 
v_fst_321_ = lean_ctor_get(v_a_317_, 0);
lean_inc(v_fst_321_);
lean_dec(v_a_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 0, v_fst_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_fst_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(lean_object* v_mutex_326_, lean_object* v_x_327_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_io_basemutex_unlock(v_mutex_326_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed(lean_object* v_mutex_332_, lean_object* v_x_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(v_mutex_332_, v_x_333_);
lean_dec(v_x_333_);
lean_dec(v_mutex_332_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(lean_object* v_k_336_, lean_object* v_ref_337_, lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_ref_337_);
lean_dec_ref(v_k_336_);
v_a_340_ = lean_ctor_get(v_x_338_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v_x_338_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v_x_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_347_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
}
else
{
lean_object* v___x_349_; 
lean_dec_ref_known(v_x_338_, 1);
v___x_349_ = lean_apply_2(v_k_336_, v_ref_337_, lean_box(0));
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed(lean_object* v_k_350_, lean_object* v_ref_351_, lean_object* v_x_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(v_k_350_, v_ref_351_, v_x_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(lean_object* v_mutex_355_, lean_object* v___f_356_){
_start:
{
lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = 0;
v___x_360_ = lean_io_basemutex_lock(v_mutex_355_);
v___x_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
v___x_363_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_358_, v___x_359_, v___x_362_, v___f_356_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3___boxed(lean_object* v_mutex_364_, lean_object* v___f_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(v_mutex_364_, v___f_365_);
lean_dec(v_mutex_364_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(lean_object* v_mutex_369_, lean_object* v_k_370_){
_start:
{
lean_object* v_ref_372_; lean_object* v_mutex_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___f_376_; lean_object* v___f_377_; lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___y_382_; 
v_ref_372_ = lean_ctor_get(v_mutex_369_, 0);
lean_inc(v_ref_372_);
v_mutex_373_ = lean_ctor_get(v_mutex_369_, 1);
lean_inc_n(v_mutex_373_, 2);
lean_dec_ref(v_mutex_369_);
v___f_374_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0));
v___f_375_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_375_, 0, v_mutex_373_);
v___f_376_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_376_, 0, v_k_370_);
lean_closure_set(v___f_376_, 1, v_ref_372_);
v___f_377_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_377_, 0, v_mutex_373_);
lean_closure_set(v___f_377_, 1, v___f_376_);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = 0;
v___x_380_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_377_, v___f_375_, v___x_378_, v___x_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_384_; 
v_a_384_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_384_);
lean_dec_ref_known(v___x_380_, 1);
if (lean_obj_tag(v_a_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_385_ = lean_ctor_get(v_a_384_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v_a_384_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v_a_384_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v_a_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
v___y_382_ = v___x_390_;
goto v___jp_381_;
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_a_393_ = lean_ctor_get(v_a_384_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_a_384_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v_a_384_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v_a_384_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_fst_397_; lean_object* v___x_399_; 
v_fst_397_ = lean_ctor_get(v_a_393_, 0);
lean_inc(v_fst_397_);
lean_dec(v_a_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v_fst_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_fst_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
v___y_382_ = v___x_399_;
goto v___jp_381_;
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_410_; 
v_a_402_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_410_ == 0)
{
v___x_404_ = v___x_380_;
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_380_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_410_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_406_ = lean_task_map(v___f_374_, v_a_402_, v___x_378_, v___x_379_);
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v___x_406_);
v___x_408_ = v___x_404_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
v___jp_381_:
{
lean_object* v___x_383_; 
v___x_383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_383_, 0, v___y_382_);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___boxed(lean_object* v_mutex_411_, lean_object* v_k_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_mutex_411_, v_k_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(lean_object* v_00_u03b1_415_, lean_object* v_00_u03b2_416_, lean_object* v_mutex_417_, lean_object* v_k_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_mutex_417_, v_k_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_mutex_423_, lean_object* v_k_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(v_00_u03b1_421_, v_00_u03b2_422_, v_mutex_423_, v_k_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__0(lean_object* v___y_431_, lean_object* v_x_432_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_442_; 
v_a_434_ = lean_ctor_get(v_x_432_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_432_);
if (v_isSharedCheck_442_ == 0)
{
v___x_436_ = v_x_432_;
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v_x_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_441_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_a_443_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_a_443_);
lean_dec_ref_known(v_x_432_, 1);
v___x_444_ = lean_st_ref_swap(v___y_431_, v_a_443_);
lean_dec(v___x_444_);
v___x_445_ = ((lean_object*)(l_Std_Notify_selector___lam__0___closed__1));
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__0___boxed(lean_object* v___y_446_, lean_object* v_x_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_Notify_selector___lam__0(v___y_446_, v_x_447_);
lean_dec(v___y_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(lean_object* v_x_450_){
_start:
{
uint8_t v___y_453_; 
if (lean_obj_tag(v_x_450_) == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_x_450_);
return v___x_457_;
}
else
{
lean_object* v_a_458_; uint8_t v___x_459_; 
v_a_458_ = lean_ctor_get(v_x_450_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v_x_450_, 1);
v___x_459_ = lean_unbox(v_a_458_);
lean_dec(v_a_458_);
if (v___x_459_ == 0)
{
uint8_t v___x_460_; 
v___x_460_ = 1;
v___y_453_ = v___x_460_;
goto v___jp_452_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
v___y_453_ = v___x_461_;
goto v___jp_452_;
}
}
v___jp_452_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_box(v___y_453_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1___boxed(lean_object* v_x_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(v_x_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_465_, lean_object* v_x_466_, lean_object* v_head_467_, lean_object* v_x_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(v_tail_465_, v_x_466_, v_head_467_, v_x_468_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v_x_478_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
else
{
lean_object* v_head_482_; lean_object* v_tail_483_; lean_object* v___f_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_head_482_ = lean_ctor_get(v_x_477_, 0);
lean_inc_n(v_head_482_, 2);
v_tail_483_ = lean_ctor_get(v_x_477_, 1);
lean_inc(v_tail_483_);
lean_dec_ref_known(v_x_477_, 2);
v___f_484_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_484_, 0, v_tail_483_);
lean_closure_set(v___f_484_, 1, v_x_478_);
lean_closure_set(v___f_484_, 2, v_head_482_);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = 0;
if (lean_obj_tag(v_head_482_) == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref_known(v_head_482_, 1);
v___x_487_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1));
v___x_488_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_485_, v___x_486_, v___x_487_, v___f_484_);
return v___x_488_;
}
else
{
lean_object* v_finished_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_502_; 
v_finished_489_ = lean_ctor_get(v_head_482_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v_head_482_);
if (v_isSharedCheck_502_ == 0)
{
v___x_491_ = v_head_482_;
v_isShared_492_ = v_isSharedCheck_502_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_finished_489_);
lean_dec(v_head_482_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_502_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_finished_493_; lean_object* v___f_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
v_finished_493_ = lean_ctor_get(v_finished_489_, 0);
lean_inc(v_finished_493_);
lean_dec_ref(v_finished_489_);
v___f_494_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2));
v___x_495_ = lean_st_ref_get(v_finished_493_);
lean_dec(v_finished_493_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_495_);
v___x_497_ = v___x_491_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_501_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
v___x_499_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_485_, v___x_486_, v___x_498_, v___f_494_);
v___x_500_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_485_, v___x_486_, v___x_499_, v___f_484_);
return v___x_500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_503_, lean_object* v_x_504_, lean_object* v_head_505_, lean_object* v_x_506_){
_start:
{
if (lean_obj_tag(v_x_506_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v_head_505_);
lean_dec(v_x_504_);
lean_dec(v_tail_503_);
v_a_508_ = lean_ctor_get(v_x_506_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_x_506_);
if (v_isSharedCheck_516_ == 0)
{
v___x_510_ = v_x_506_;
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v_x_506_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_516_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_515_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; 
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
else
{
lean_object* v_a_517_; uint8_t v___x_518_; 
v_a_517_ = lean_ctor_get(v_x_506_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v_x_506_, 1);
v___x_518_ = lean_unbox(v_a_517_);
lean_dec(v_a_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_dec_ref(v_head_505_);
v___x_519_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_503_, v_x_504_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_520_, 0, v_head_505_);
lean_ctor_set(v___x_520_, 1, v_x_504_);
v___x_521_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_503_, v___x_520_);
return v___x_521_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___boxed(lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_522_, v_x_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(lean_object* v_x_526_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v___x_528_; 
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v_x_526_);
return v___x_528_;
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_538_; 
v_a_529_ = lean_ctor_get(v_x_526_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_538_ == 0)
{
v___x_531_ = v_x_526_;
v_isShared_532_ = v_isSharedCheck_538_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v_x_526_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_538_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_533_ = l_List_reverse___redArg(v_a_529_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_537_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; 
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0___boxed(lean_object* v_x_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(v_x_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(lean_object* v_a_542_, lean_object* v___x_543_, lean_object* v_x_544_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_554_; 
lean_dec(v___x_543_);
lean_dec(v_a_542_);
v_a_546_ = lean_ctor_get(v_x_544_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v_x_544_);
if (v_isSharedCheck_554_ == 0)
{
v___x_548_ = v_x_544_;
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v_x_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_554_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_553_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; 
v___x_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
return v___x_552_;
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_571_; 
v_a_555_ = lean_ctor_get(v_x_544_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v_x_544_);
if (v_isSharedCheck_571_ == 0)
{
v___x_557_ = v_x_544_;
v_isShared_558_ = v_isSharedCheck_571_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v_x_544_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_571_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint8_t v___x_559_; 
v___x_559_ = l_List_isEmpty___redArg(v_a_542_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_562_; 
lean_dec(v___x_543_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v_a_555_);
lean_ctor_set(v___x_560_, 1, v_a_542_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_560_);
v___x_562_ = v___x_557_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; 
v___x_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
lean_dec(v_a_542_);
v___x_565_ = l_List_reverse___redArg(v_a_555_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_543_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_566_);
v___x_568_ = v___x_557_;
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
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed(lean_object* v_a_572_, lean_object* v___x_573_, lean_object* v_x_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(v_a_572_, v___x_573_, v_x_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(lean_object* v___x_577_, lean_object* v_eList_578_, lean_object* v___f_579_, lean_object* v_x_580_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v___f_579_);
lean_dec(v_eList_578_);
lean_dec(v___x_577_);
v_a_582_ = lean_ctor_get(v_x_580_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v_x_580_);
if (v_isSharedCheck_590_ == 0)
{
v___x_584_ = v_x_580_;
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v_x_580_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_589_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___f_592_; lean_object* v___x_593_; uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_a_591_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v_x_580_, 1);
lean_inc(v___x_577_);
v___f_592_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed), 4, 2);
lean_closure_set(v___f_592_, 0, v_a_591_);
lean_closure_set(v___f_592_, 1, v___x_577_);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = 0;
v___x_595_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_eList_578_, v___x_577_);
v___x_596_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_593_, v___x_594_, v___x_595_, v___f_579_);
v___x_597_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_593_, v___x_594_, v___x_596_, v___f_592_);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed(lean_object* v___x_598_, lean_object* v_eList_599_, lean_object* v___f_600_, lean_object* v_x_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(v___x_598_, v_eList_599_, v___f_600_, v_x_601_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(lean_object* v_q_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_eList_608_; lean_object* v_dList_609_; lean_object* v___f_610_; lean_object* v___x_611_; lean_object* v___f_612_; lean_object* v___x_613_; uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_eList_608_ = lean_ctor_get(v_q_605_, 0);
lean_inc(v_eList_608_);
v_dList_609_ = lean_ctor_get(v_q_605_, 1);
lean_inc(v_dList_609_);
lean_dec_ref(v_q_605_);
v___f_610_ = ((lean_object*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0));
v___x_611_ = lean_box(0);
v___f_612_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_612_, 0, v___x_611_);
lean_closure_set(v___f_612_, 1, v_eList_608_);
lean_closure_set(v___f_612_, 2, v___f_610_);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = 0;
v___x_615_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_dList_609_, v___x_611_);
v___x_616_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_613_, v___x_614_, v___x_615_, v___f_610_);
v___x_617_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_613_, v___x_614_, v___x_616_, v___f_612_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___boxed(lean_object* v_q_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_q_618_, v___y_619_);
lean_dec(v___y_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__1(lean_object* v___y_622_, lean_object* v___f_623_, lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v___f_623_);
v_a_626_ = lean_ctor_get(v_x_624_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v_x_624_);
if (v_isSharedCheck_634_ == 0)
{
v___x_628_ = v_x_624_;
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v_x_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_633_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; 
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_636_; uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_a_635_ = lean_ctor_get(v_x_624_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v_x_624_, 1);
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = 0;
v___x_638_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_a_635_, v___y_622_);
v___x_639_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_636_, v___x_637_, v___x_638_, v___f_623_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__1___boxed(lean_object* v___y_640_, lean_object* v___f_641_, lean_object* v_x_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Std_Notify_selector___lam__1(v___y_640_, v___f_641_, v_x_642_);
lean_dec(v___y_640_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__2(lean_object* v___y_645_){
_start:
{
lean_object* v___f_647_; lean_object* v___f_648_; lean_object* v___x_649_; uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc_n(v___y_645_, 2);
v___f_647_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__0___boxed), 3, 1);
lean_closure_set(v___f_647_, 0, v___y_645_);
v___f_648_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_648_, 0, v___y_645_);
lean_closure_set(v___f_648_, 1, v___f_647_);
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = 0;
v___x_651_ = lean_st_ref_get(v___y_645_);
v___x_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
v___x_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
v___x_654_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_649_, v___x_650_, v___x_653_, v___f_648_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__2___boxed(lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_Notify_selector___lam__2(v___y_655_);
lean_dec(v___y_655_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__3(lean_object* v_waiter_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_661_ = lean_st_ref_take(v___y_659_);
v___x_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_662_, 0, v_waiter_658_);
v___x_663_ = l_Std_Queue_enqueue___redArg(v___x_662_, v___x_661_);
v___x_664_ = lean_st_ref_put(v___y_659_, v___x_663_);
v___x_665_ = ((lean_object*)(l_Std_Notify_selector___lam__0___closed__1));
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__3___boxed(lean_object* v_waiter_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_Notify_selector___lam__3(v_waiter_666_, v___y_667_);
lean_dec(v___y_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__4(lean_object* v_notify_670_, lean_object* v_waiter_671_){
_start:
{
lean_object* v___f_673_; lean_object* v___x_674_; 
v___f_673_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_673_, 0, v_waiter_671_);
v___x_674_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_notify_670_, v___f_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__4___boxed(lean_object* v_notify_675_, lean_object* v_waiter_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_Notify_selector___lam__4(v_notify_675_, v_waiter_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__5(lean_object* v___x_679_){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__5___boxed(lean_object* v___x_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_Notify_selector___lam__5(v___x_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector(lean_object* v_notify_689_){
_start:
{
lean_object* v___f_690_; lean_object* v___f_691_; lean_object* v___f_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___f_690_ = ((lean_object*)(l_Std_Notify_selector___closed__0));
lean_inc_ref(v_notify_689_);
v___f_691_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_691_, 0, v_notify_689_);
v___f_692_ = ((lean_object*)(l_Std_Notify_selector___closed__1));
v___x_693_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed), 5, 4);
lean_closure_set(v___x_693_, 0, lean_box(0));
lean_closure_set(v___x_693_, 1, lean_box(0));
lean_closure_set(v___x_693_, 2, v_notify_689_);
lean_closure_set(v___x_693_, 3, v___f_690_);
v___x_694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_694_, 0, v___f_692_);
lean_ctor_set(v___x_694_, 1, v___f_691_);
lean_ctor_set(v___x_694_, 2, v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v___y_697_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_695_, v_x_696_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___boxed(lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(v_x_700_, v_x_701_, v___y_702_);
lean_dec(v___y_702_);
return v_res_704_;
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

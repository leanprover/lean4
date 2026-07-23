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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Std_Queue_empty(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(lean_object*);
static const lean_closure_object l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Std_Notify_selector___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Notify_selector___lam__3___closed__0 = (const lean_object*)&l_Std_Notify_selector___lam__3___closed__0_value;
static const lean_ctor_object l_Std_Notify_selector___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Notify_selector___lam__3___closed__0_value)}};
static const lean_object* l_Std_Notify_selector___lam__3___closed__1 = (const lean_object*)&l_Std_Notify_selector___lam__3___closed__1_value;
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
v___x_61_ = lean_st_ref_set(v_finished_54_, v___x_60_);
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
uint8_t v___x_400__boxed_92_; uint8_t v_res_93_; lean_object* v_r_94_; 
v___x_400__boxed_92_ = lean_unbox(v___x_90_);
v_res_93_ = l_Std_Notify_Consumer_resolve___redArg___lam__0(v___x_400__boxed_92_);
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
v___x_123_ = l_Std_Queue_empty(lean_box(0));
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
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_st_169_; lean_object* v___x_170_; 
v___x_167_ = lean_st_ref_get(v___y_165_);
v___x_168_ = l___private_Init_While_0__repeatM_erased___at___00Std_Notify_notify_spec__0___redArg(v___x_167_);
lean_dec_ref(v___x_168_);
v_st_169_ = lean_obj_once(&l_Std_Notify_new___closed__0, &l_Std_Notify_new___closed__0_once, _init_l_Std_Notify_new___closed__0);
v___x_170_ = lean_st_ref_set(v___y_165_, v_st_169_);
return v___x_170_;
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
LEAN_EXPORT uint8_t l_Std_Notify_notifyOne___lam__0(lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_st_ref_get(v___y_192_);
v___x_195_ = l_Std_Queue_dequeue_x3f___redArg(v___x_194_);
if (lean_obj_tag(v___x_195_) == 1)
{
lean_object* v_val_196_; lean_object* v_fst_197_; lean_object* v_snd_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_val_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v___x_195_, 1);
v_fst_197_ = lean_ctor_get(v_val_196_, 0);
lean_inc(v_fst_197_);
v_snd_198_ = lean_ctor_get(v_val_196_, 1);
lean_inc(v_snd_198_);
lean_dec(v_val_196_);
v___x_199_ = lean_st_ref_set(v___y_192_, v_snd_198_);
v___x_200_ = lean_box(0);
v___x_201_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_197_, v___x_200_);
lean_dec(v_fst_197_);
return v___x_201_;
}
else
{
uint8_t v___x_202_; 
lean_dec(v___x_195_);
v___x_202_ = 0;
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___lam__0___boxed(lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Std_Notify_notifyOne___lam__0(v___y_203_);
lean_dec(v___y_203_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint8_t l_Std_Notify_notifyOne(lean_object* v_x_208_){
_start:
{
lean_object* v___f_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___f_210_ = ((lean_object*)(l_Std_Notify_notifyOne___closed__0));
v___x_211_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_208_, v___f_210_);
v___x_212_ = lean_unbox(v___x_211_);
lean_dec(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_notifyOne___boxed(lean_object* v_x_213_, lean_object* v_a_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_Std_Notify_notifyOne(v_x_213_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(lean_object* v_mutex_217_, lean_object* v_k_218_){
_start:
{
lean_object* v_ref_220_; lean_object* v_mutex_221_; lean_object* v___x_222_; lean_object* v_r_223_; 
v_ref_220_ = lean_ctor_get(v_mutex_217_, 0);
lean_inc(v_ref_220_);
v_mutex_221_ = lean_ctor_get(v_mutex_217_, 1);
lean_inc(v_mutex_221_);
lean_dec_ref(v_mutex_217_);
v___x_222_ = lean_io_basemutex_lock(v_mutex_221_);
v_r_223_ = lean_apply_2(v_k_218_, v_ref_220_, lean_box(0));
if (lean_obj_tag(v_r_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_a_224_ = lean_ctor_get(v_r_223_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v_r_223_);
if (v_isSharedCheck_232_ == 0)
{
v___x_226_ = v_r_223_;
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v_r_223_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = lean_io_basemutex_unlock(v_mutex_221_);
lean_dec(v_mutex_221_);
if (v_isShared_227_ == 0)
{
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_224_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_241_; 
v_a_233_ = lean_ctor_get(v_r_223_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v_r_223_);
if (v_isSharedCheck_241_ == 0)
{
v___x_235_ = v_r_223_;
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v_r_223_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_241_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_237_ = lean_io_basemutex_unlock(v_mutex_221_);
lean_dec(v_mutex_221_);
if (v_isShared_236_ == 0)
{
v___x_239_ = v___x_235_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_233_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg___boxed(lean_object* v_mutex_242_, lean_object* v_k_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_242_, v_k_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_mutex_248_, lean_object* v_k_249_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_248_, v_k_249_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___boxed(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_mutex_254_, lean_object* v_k_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(v_00_u03b1_252_, v_00_u03b2_253_, v_mutex_254_, v_k_255_);
return v_res_257_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__1(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l_Std_Notify_wait___lam__0___closed__0));
v___x_260_ = lean_mk_io_user_error(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__2(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__1, &l_Std_Notify_wait___lam__0___closed__1_once, _init_l_Std_Notify_wait___lam__0___closed__1);
v___x_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
return v___x_262_;
}
}
static lean_object* _init_l_Std_Notify_wait___lam__0___closed__3(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__2, &l_Std_Notify_wait___lam__0___closed__2_once, _init_l_Std_Notify_wait___lam__0___closed__2);
v___x_264_ = lean_task_pure(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__0(lean_object* v_a_265_){
_start:
{
if (lean_obj_tag(v_a_265_) == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&l_Std_Notify_wait___lam__0___closed__3, &l_Std_Notify_wait___lam__0___closed__3_once, _init_l_Std_Notify_wait___lam__0___closed__3);
return v___x_267_;
}
else
{
lean_object* v_val_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
v_val_268_ = lean_ctor_get(v_a_265_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v_a_265_);
if (v_isSharedCheck_276_ == 0)
{
v___x_270_ = v_a_265_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_val_268_);
lean_dec(v_a_265_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_val_268_);
v___x_273_ = v_reuseFailAlloc_275_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
lean_object* v___x_274_; 
v___x_274_ = lean_task_pure(v___x_273_);
return v___x_274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__0___boxed(lean_object* v_a_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Notify_wait___lam__0(v_a_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__1(lean_object* v___f_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_283_ = lean_io_promise_new();
v___x_284_ = lean_st_ref_take(v___y_281_);
lean_inc(v___x_283_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
v___x_286_ = l_Std_Queue_enqueue___redArg(v___x_285_, v___x_284_);
v___x_287_ = lean_st_ref_set(v___y_281_, v___x_286_);
v___x_288_ = lean_io_promise_result_opt(v___x_283_);
lean_dec(v___x_283_);
v___x_289_ = lean_unsigned_to_nat(0u);
v___x_290_ = 0;
v___x_291_ = lean_io_bind_task(v___x_288_, v___f_280_, v___x_289_, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___lam__1___boxed(lean_object* v___f_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Notify_wait___lam__1(v___f_293_, v___y_294_);
lean_dec(v___y_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait(lean_object* v_x_300_){
_start:
{
lean_object* v___f_302_; lean_object* v___x_303_; 
v___f_302_ = ((lean_object*)(l_Std_Notify_wait___closed__1));
v___x_303_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_x_300_, v___f_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_wait___boxed(lean_object* v_x_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_Notify_wait(v_x_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(lean_object* v_mutex_307_, lean_object* v_x_308_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_io_basemutex_unlock(v_mutex_307_);
v___x_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0___boxed(lean_object* v_mutex_313_, lean_object* v_x_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(v_mutex_313_, v_x_314_);
lean_dec(v_x_314_);
lean_dec(v_mutex_313_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(lean_object* v_k_317_, lean_object* v_ref_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_329_; 
lean_dec(v_ref_318_);
lean_dec_ref(v_k_317_);
v_a_321_ = lean_ctor_get(v_x_319_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_319_);
if (v_isSharedCheck_329_ == 0)
{
v___x_323_ = v_x_319_;
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v_x_319_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_329_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_328_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; 
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
}
}
else
{
lean_object* v___x_330_; 
lean_dec_ref_known(v_x_319_, 1);
v___x_330_ = lean_apply_2(v_k_317_, v_ref_318_, lean_box(0));
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed(lean_object* v_k_331_, lean_object* v_ref_332_, lean_object* v_x_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(v_k_331_, v_ref_332_, v_x_333_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(lean_object* v_mutex_336_, lean_object* v___f_337_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; 
v___x_339_ = lean_io_basemutex_lock(v_mutex_336_);
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
v___x_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = 0;
v___x_344_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_342_, v___x_343_, v___x_341_, v___f_337_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed(lean_object* v_mutex_345_, lean_object* v___f_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(v_mutex_345_, v___f_346_);
lean_dec(v_mutex_345_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(lean_object* v___y_349_){
_start:
{
if (lean_obj_tag(v___y_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
v_a_350_ = lean_ctor_get(v___y_349_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___y_349_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___y_349_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___y_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
v_a_358_ = lean_ctor_get(v___y_349_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___y_349_);
if (v_isSharedCheck_366_ == 0)
{
v___x_360_ = v___y_349_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___y_349_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v_fst_362_; lean_object* v___x_364_; 
v_fst_362_ = lean_ctor_get(v_a_358_, 0);
lean_inc(v_fst_362_);
lean_dec(v_a_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v_fst_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_fst_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(lean_object* v_mutex_368_, lean_object* v_k_369_){
_start:
{
lean_object* v_ref_371_; lean_object* v_mutex_372_; lean_object* v___f_373_; lean_object* v___f_374_; lean_object* v___f_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___y_380_; 
v_ref_371_ = lean_ctor_get(v_mutex_368_, 0);
lean_inc(v_ref_371_);
v_mutex_372_ = lean_ctor_get(v_mutex_368_, 1);
lean_inc_n(v_mutex_372_, 2);
lean_dec_ref(v_mutex_368_);
v___f_373_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_373_, 0, v_mutex_372_);
v___f_374_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_374_, 0, v_k_369_);
lean_closure_set(v___f_374_, 1, v_ref_371_);
v___f_375_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_375_, 0, v_mutex_372_);
lean_closure_set(v___f_375_, 1, v___f_374_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = 0;
v___x_378_ = l_Std_Async_EAsync_tryFinally_x27___redArg(v___f_375_, v___f_373_, v___x_376_, v___x_377_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_382_; 
v_a_382_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_378_, 1);
if (lean_obj_tag(v_a_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
v_a_383_ = lean_ctor_get(v_a_382_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v_a_382_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v_a_382_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v_a_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
v___y_380_ = v___x_388_;
goto v___jp_379_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_399_; 
v_a_391_ = lean_ctor_get(v_a_382_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v_a_382_);
if (v_isSharedCheck_399_ == 0)
{
v___x_393_ = v_a_382_;
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v_a_382_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_399_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v_fst_395_; lean_object* v___x_397_; 
v_fst_395_ = lean_ctor_get(v_a_391_, 0);
lean_inc(v_fst_395_);
lean_dec(v_a_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v_fst_395_);
v___x_397_ = v___x_393_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_fst_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
v___y_380_ = v___x_397_;
goto v___jp_379_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_409_; 
v_a_400_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_409_ == 0)
{
v___x_402_ = v___x_378_;
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_378_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___f_404_ = ((lean_object*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0));
v___x_405_ = lean_task_map(v___f_404_, v_a_400_, v___x_376_, v___x_377_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_405_);
v___x_407_ = v___x_402_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
v___jp_379_:
{
lean_object* v___x_381_; 
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___y_380_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___boxed(lean_object* v_mutex_410_, lean_object* v_k_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_mutex_410_, v_k_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(lean_object* v_00_u03b1_414_, lean_object* v_00_u03b2_415_, lean_object* v_mutex_416_, lean_object* v_k_417_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_mutex_416_, v_k_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed(lean_object* v_00_u03b1_420_, lean_object* v_00_u03b2_421_, lean_object* v_mutex_422_, lean_object* v_k_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(v_00_u03b1_420_, v_00_u03b2_421_, v_mutex_422_, v_k_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__0(lean_object* v___y_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_437_; 
v_a_429_ = lean_ctor_get(v_x_427_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_427_);
if (v_isSharedCheck_437_ == 0)
{
v___x_431_ = v_x_427_;
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v_x_427_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_436_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_435_; 
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_447_; 
v_a_438_ = lean_ctor_get(v_x_427_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_427_);
if (v_isSharedCheck_447_ == 0)
{
v___x_440_ = v_x_427_;
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v_x_427_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_st_ref_set(v___y_426_, v_a_438_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_446_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__0___boxed(lean_object* v___y_448_, lean_object* v_x_449_, lean_object* v___y_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_Notify_selector___lam__0(v___y_448_, v_x_449_);
lean_dec(v___y_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(lean_object* v_x_452_){
_start:
{
uint8_t v___y_455_; 
if (lean_obj_tag(v_x_452_) == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_x_452_);
return v___x_459_;
}
else
{
lean_object* v_a_460_; uint8_t v___x_461_; 
v_a_460_ = lean_ctor_get(v_x_452_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v_x_452_, 1);
v___x_461_ = lean_unbox(v_a_460_);
lean_dec(v_a_460_);
if (v___x_461_ == 0)
{
uint8_t v___x_462_; 
v___x_462_ = 1;
v___y_455_ = v___x_462_;
goto v___jp_454_;
}
else
{
uint8_t v___x_463_; 
v___x_463_ = 0;
v___y_455_ = v___x_463_;
goto v___jp_454_;
}
}
v___jp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_box(v___y_455_);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1___boxed(lean_object* v_x_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(v_x_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v_tail_467_, lean_object* v_x_468_, lean_object* v_head_469_, lean_object* v_x_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(v_tail_467_, v_x_468_, v_head_469_, v_x_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v_x_480_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
else
{
lean_object* v_head_484_; lean_object* v_tail_485_; lean_object* v___f_486_; lean_object* v_val_488_; 
v_head_484_ = lean_ctor_get(v_x_479_, 0);
lean_inc_n(v_head_484_, 2);
v_tail_485_ = lean_ctor_get(v_x_479_, 1);
lean_inc(v_tail_485_);
lean_dec_ref_known(v_x_479_, 2);
v___f_486_ = lean_alloc_closure((void*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_486_, 0, v_tail_485_);
lean_closure_set(v___f_486_, 1, v_x_480_);
lean_closure_set(v___f_486_, 2, v_head_484_);
if (lean_obj_tag(v_head_484_) == 0)
{
lean_object* v___x_492_; 
lean_dec_ref_known(v_head_484_, 1);
v___x_492_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1));
v_val_488_ = v___x_492_;
goto v___jp_487_;
}
else
{
lean_object* v_finished_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_507_; 
v_finished_493_ = lean_ctor_get(v_head_484_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_head_484_);
if (v_isSharedCheck_507_ == 0)
{
v___x_495_ = v_head_484_;
v_isShared_496_ = v_isSharedCheck_507_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_finished_493_);
lean_dec(v_head_484_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_507_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_finished_497_; lean_object* v___x_498_; lean_object* v___f_499_; lean_object* v___x_501_; 
v_finished_497_ = lean_ctor_get(v_finished_493_, 0);
lean_inc(v_finished_497_);
lean_dec_ref(v_finished_493_);
v___x_498_ = lean_st_ref_get(v_finished_497_);
lean_dec(v_finished_497_);
v___f_499_ = ((lean_object*)(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2));
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_498_);
v___x_501_ = v___x_495_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_498_);
v___x_501_ = v_reuseFailAlloc_506_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; lean_object* v___x_505_; 
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = 0;
v___x_505_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_503_, v___x_504_, v___x_502_, v___f_499_);
v_val_488_ = v___x_505_;
goto v___jp_487_;
}
}
}
v___jp_487_:
{
lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = 0;
v___x_491_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_489_, v___x_490_, v_val_488_, v___f_486_);
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(lean_object* v_tail_508_, lean_object* v_x_509_, lean_object* v_head_510_, lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_511_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v_head_510_);
lean_dec(v_x_509_);
lean_dec(v_tail_508_);
v_a_513_ = lean_ctor_get(v_x_511_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v_x_511_);
if (v_isSharedCheck_521_ == 0)
{
v___x_515_ = v_x_511_;
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v_x_511_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_521_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_513_);
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
else
{
lean_object* v_a_522_; uint8_t v___x_523_; 
v_a_522_ = lean_ctor_get(v_x_511_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v_x_511_, 1);
v___x_523_ = lean_unbox(v_a_522_);
lean_dec(v_a_522_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
lean_dec_ref(v_head_510_);
v___x_524_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_508_, v_x_509_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_525_, 0, v_head_510_);
lean_ctor_set(v___x_525_, 1, v_x_509_);
v___x_526_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_508_, v___x_525_);
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___boxed(lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_527_, v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(lean_object* v_x_531_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v___x_533_; 
v___x_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_533_, 0, v_x_531_);
return v___x_533_;
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_543_; 
v_a_534_ = lean_ctor_get(v_x_531_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_543_ == 0)
{
v___x_536_ = v_x_531_;
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v_x_531_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_543_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_List_reverse___redArg(v_a_534_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 0, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0___boxed(lean_object* v_x_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(v_x_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(lean_object* v_a_547_, lean_object* v___x_548_, lean_object* v_x_549_){
_start:
{
if (lean_obj_tag(v_x_549_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_559_; 
lean_dec(v___x_548_);
lean_dec(v_a_547_);
v_a_551_ = lean_ctor_get(v_x_549_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_549_);
if (v_isSharedCheck_559_ == 0)
{
v___x_553_ = v_x_549_;
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v_x_549_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_558_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; 
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_576_; 
v_a_560_ = lean_ctor_get(v_x_549_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_549_);
if (v_isSharedCheck_576_ == 0)
{
v___x_562_ = v_x_549_;
v_isShared_563_ = v_isSharedCheck_576_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v_x_549_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_576_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
uint8_t v___x_564_; 
v___x_564_ = l_List_isEmpty___redArg(v_a_547_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; lean_object* v___x_567_; 
lean_dec(v___x_548_);
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v_a_560_);
lean_ctor_set(v___x_565_, 1, v_a_547_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_565_);
v___x_567_ = v___x_562_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
lean_dec(v_a_547_);
v___x_570_ = l_List_reverse___redArg(v_a_560_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_548_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_571_);
v___x_573_ = v___x_562_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_575_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; 
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed(lean_object* v_a_577_, lean_object* v___x_578_, lean_object* v_x_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(v_a_577_, v___x_578_, v_x_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(lean_object* v_eList_582_, lean_object* v___x_583_, lean_object* v___f_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v___f_584_);
lean_dec(v___x_583_);
lean_dec(v_eList_582_);
v_a_587_ = lean_ctor_get(v_x_585_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v_x_585_);
if (v_isSharedCheck_595_ == 0)
{
v___x_589_ = v_x_585_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v_x_585_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___f_601_; lean_object* v___x_602_; 
v_a_596_ = lean_ctor_get(v_x_585_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v_x_585_, 1);
lean_inc(v___x_583_);
v___x_597_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_eList_582_, v___x_583_);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = 0;
v___x_600_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_598_, v___x_599_, v___x_597_, v___f_584_);
v___f_601_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed), 4, 2);
lean_closure_set(v___f_601_, 0, v_a_596_);
lean_closure_set(v___f_601_, 1, v___x_583_);
v___x_602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_598_, v___x_599_, v___x_600_, v___f_601_);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed(lean_object* v_eList_603_, lean_object* v___x_604_, lean_object* v___f_605_, lean_object* v_x_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(v_eList_603_, v___x_604_, v___f_605_, v_x_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(lean_object* v_q_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_eList_613_; lean_object* v_dList_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___f_617_; lean_object* v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; lean_object* v___f_621_; lean_object* v___x_622_; 
v_eList_613_ = lean_ctor_get(v_q_610_, 0);
lean_inc(v_eList_613_);
v_dList_614_ = lean_ctor_get(v_q_610_, 1);
lean_inc(v_dList_614_);
lean_dec_ref(v_q_610_);
v___x_615_ = lean_box(0);
v___x_616_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_dList_614_, v___x_615_);
v___f_617_ = ((lean_object*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0));
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = 0;
v___x_620_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_618_, v___x_619_, v___x_616_, v___f_617_);
v___f_621_ = lean_alloc_closure((void*)(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed), 5, 3);
lean_closure_set(v___f_621_, 0, v_eList_613_);
lean_closure_set(v___f_621_, 1, v___x_615_);
lean_closure_set(v___f_621_, 2, v___f_617_);
v___x_622_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_618_, v___x_619_, v___x_620_, v___f_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___boxed(lean_object* v_q_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_q_623_, v___y_624_);
lean_dec(v___y_624_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__1(lean_object* v___y_627_, lean_object* v___f_628_, lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_629_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_639_; 
lean_dec_ref(v___f_628_);
v_a_631_ = lean_ctor_get(v_x_629_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_x_629_);
if (v_isSharedCheck_639_ == 0)
{
v___x_633_ = v_x_629_;
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v_x_629_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_639_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_638_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; 
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; 
v_a_640_ = lean_ctor_get(v_x_629_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v_x_629_, 1);
v___x_641_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_a_640_, v___y_627_);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = 0;
v___x_644_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_642_, v___x_643_, v___x_641_, v___f_628_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__1___boxed(lean_object* v___y_645_, lean_object* v___f_646_, lean_object* v_x_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Std_Notify_selector___lam__1(v___y_645_, v___f_646_, v_x_647_);
lean_dec(v___y_645_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__2(lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; lean_object* v___f_653_; lean_object* v___f_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; lean_object* v___x_659_; 
v___x_652_ = lean_st_ref_get(v___y_650_);
lean_inc_n(v___y_650_, 2);
v___f_653_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__0___boxed), 3, 1);
lean_closure_set(v___f_653_, 0, v___y_650_);
v___f_654_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__1___boxed), 4, 2);
lean_closure_set(v___f_654_, 0, v___y_650_);
lean_closure_set(v___f_654_, 1, v___f_653_);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_652_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = 0;
v___x_659_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_657_, v___x_658_, v___x_656_, v___f_654_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__2___boxed(lean_object* v___y_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_Notify_selector___lam__2(v___y_660_);
lean_dec(v___y_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__3(lean_object* v_waiter_667_, lean_object* v___y_668_){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_670_ = lean_st_ref_take(v___y_668_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v_waiter_667_);
v___x_672_ = l_Std_Queue_enqueue___redArg(v___x_671_, v___x_670_);
v___x_673_ = lean_st_ref_set(v___y_668_, v___x_672_);
v___x_674_ = ((lean_object*)(l_Std_Notify_selector___lam__3___closed__1));
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__3___boxed(lean_object* v_waiter_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_Notify_selector___lam__3(v_waiter_675_, v___y_676_);
lean_dec(v___y_676_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__4(lean_object* v_notify_679_, lean_object* v_waiter_680_){
_start:
{
lean_object* v___f_682_; lean_object* v___x_683_; 
v___f_682_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_682_, 0, v_waiter_680_);
v___x_683_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(v_notify_679_, v___f_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__4___boxed(lean_object* v_notify_684_, lean_object* v_waiter_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_Notify_selector___lam__4(v_notify_684_, v_waiter_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__5(lean_object* v___x_688_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector___lam__5___boxed(lean_object* v___x_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_Notify_selector___lam__5(v___x_692_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Notify_selector(lean_object* v_notify_698_){
_start:
{
lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___f_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___f_699_ = ((lean_object*)(l_Std_Notify_selector___closed__0));
lean_inc_ref(v_notify_698_);
v___f_700_ = lean_alloc_closure((void*)(l_Std_Notify_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_700_, 0, v_notify_698_);
v___f_701_ = ((lean_object*)(l_Std_Notify_selector___closed__1));
v___x_702_ = lean_alloc_closure((void*)(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed), 5, 4);
lean_closure_set(v___x_702_, 0, lean_box(0));
lean_closure_set(v___x_702_, 1, lean_box(0));
lean_closure_set(v___x_702_, 2, v_notify_698_);
lean_closure_set(v___x_702_, 3, v___f_699_);
v___x_703_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_703_, 0, v___f_701_);
lean_ctor_set(v___x_703_, 1, v___f_700_);
lean_ctor_set(v___x_703_, 2, v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_704_, v_x_705_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___boxed(lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(v_x_709_, v_x_710_, v___y_711_);
lean_dec(v___y_711_);
return v_res_713_;
}
}
lean_object* runtime_initialize_Init_Data_Queue(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sync_Notify(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

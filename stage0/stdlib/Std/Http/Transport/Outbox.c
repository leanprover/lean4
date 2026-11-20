// Lean compiler output
// Module: Std.Http.Transport.Outbox
// Imports: public import Std.Http.Transport
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
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_io_get_task_state(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Async_Selectable_one___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Async_Selector_sleep(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* lean_io_promise_new();
lean_object* lean_io_promise_result_opt(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
static const lean_ctor_object l_Std_Http_Internal_Outbox_new___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*6 + 8, .m_other = 6, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Http_Internal_Outbox_new___redArg___closed__0 = (const lean_object*)&l_Std_Http_Internal_Outbox_new___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_new___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_new___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_new(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued_spec__0(lean_object*, lean_object*);
static const lean_array_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued___closed__0 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Internal_Outbox_send___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Internal_Outbox_send___redArg___closed__0 = (const lean_object*)&l_Std_Http_Internal_Outbox_send___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Internal_Outbox_send___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Std_Http_Internal_Outbox_send___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Internal_Outbox_send___redArg___closed__1 = (const lean_object*)&l_Std_Http_Internal_Outbox_send___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_writing___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writing___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_writing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writing___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "no write completed within "};
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___closed__0 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___closed__0_value;
static const lean_string_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " ms"};
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___closed__1 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__0 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__0_value;
static const lean_ctor_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__0_value)}};
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__1 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__1_value;
static const lean_ctor_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__2 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__2_value;
static const lean_ctor_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__2_value)}};
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__3 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__3_value;
static const lean_ctor_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__3_value)}};
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__4 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__2___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3___closed__0 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__5(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__5___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___closed__0 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___closed__0_value;
static const lean_closure_object l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___closed__1 = (const lean_object*)&l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___closed__1_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Internal_Outbox_awaitIdle_spec__1(lean_object*);
static const lean_ctor_object l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0___closed__0_value)}};
static const lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_Outbox_awaitIdle___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___closed__0 = (const lean_object*)&l_Std_Http_Internal_Outbox_awaitIdle___redArg___closed__0_value;
static const lean_closure_object l_Std_Http_Internal_Outbox_awaitIdle___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___closed__1 = (const lean_object*)&l_Std_Http_Internal_Outbox_awaitIdle___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Internal_Outbox_awaitIdle_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idleFor_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idleFor_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idleFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idleFor_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_failed___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_failed___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_failed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_failed___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Internal_Outbox_awaitWritten___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___closed__0 = (const lean_object*)&l_Std_Http_Internal_Outbox_awaitWritten___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Internal_Outbox_push___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Internal_Outbox_push___redArg___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Internal_Outbox_push___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Internal_Outbox_push___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Internal_Outbox_push___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Internal_Outbox_push___redArg___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Internal_Outbox_push___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_new___redArg(lean_object* v_socket_6_, lean_object* v_writeTimeout_7_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = ((lean_object*)(l_Std_Http_Internal_Outbox_new___redArg___closed__0));
v___x_10_ = lean_st_mk_ref(v___x_9_);
v___x_11_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_11_, 0, v_socket_6_);
lean_ctor_set(v___x_11_, 1, v_writeTimeout_7_);
lean_ctor_set(v___x_11_, 2, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_new___redArg___boxed(lean_object* v_socket_12_, lean_object* v_writeTimeout_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Std_Http_Internal_Outbox_new___redArg(v_socket_12_, v_writeTimeout_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_new(lean_object* v_00_u03b1_16_, lean_object* v_socket_17_, lean_object* v_writeTimeout_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Std_Http_Internal_Outbox_new___redArg(v_socket_17_, v_writeTimeout_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_new___boxed(lean_object* v_00_u03b1_21_, lean_object* v_socket_22_, lean_object* v_writeTimeout_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_Http_Internal_Outbox_new(v_00_u03b1_21_, v_socket_22_, v_writeTimeout_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued_spec__0_spec__0(lean_object* v_as_26_, size_t v_i_27_, size_t v_stop_28_, lean_object* v_b_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = lean_usize_dec_eq(v_i_27_, v_stop_28_);
if (v___x_30_ == 0)
{
size_t v___x_31_; size_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_31_ = ((size_t)1ULL);
v___x_32_ = lean_usize_sub(v_i_27_, v___x_31_);
v___x_33_ = lean_array_uget_borrowed(v_as_26_, v___x_32_);
v___x_34_ = l_Array_append___redArg(v_b_29_, v___x_33_);
v_i_27_ = v___x_32_;
v_b_29_ = v___x_34_;
goto _start;
}
else
{
return v_b_29_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued_spec__0_spec__0___boxed(lean_object* v_as_36_, lean_object* v_i_37_, lean_object* v_stop_38_, lean_object* v_b_39_){
_start:
{
size_t v_i_boxed_40_; size_t v_stop_boxed_41_; lean_object* v_res_42_; 
v_i_boxed_40_ = lean_unbox_usize(v_i_37_);
lean_dec(v_i_37_);
v_stop_boxed_41_ = lean_unbox_usize(v_stop_38_);
lean_dec(v_stop_38_);
v_res_42_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued_spec__0_spec__0(v_as_36_, v_i_boxed_40_, v_stop_boxed_41_, v_b_39_);
lean_dec_ref(v_as_36_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued_spec__0(lean_object* v_init_43_, lean_object* v_l_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_45_ = lean_array_mk(v_l_44_);
v___x_46_ = lean_array_get_size(v___x_45_);
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_nat_dec_lt(v___x_47_, v___x_46_);
if (v___x_48_ == 0)
{
lean_dec_ref(v___x_45_);
return v_init_43_;
}
else
{
size_t v___x_49_; size_t v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_usize_of_nat(v___x_46_);
v___x_50_ = ((size_t)0ULL);
v___x_51_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued_spec__0_spec__0(v___x_45_, v___x_49_, v___x_50_, v_init_43_);
lean_dec_ref(v___x_45_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued(lean_object* v_x_54_){
_start:
{
lean_object* v_batches_56_; 
if (lean_obj_tag(v_x_54_) == 1)
{
lean_object* v_tail_59_; 
v_tail_59_ = lean_ctor_get(v_x_54_, 1);
if (lean_obj_tag(v_tail_59_) == 0)
{
lean_object* v_head_60_; 
v_head_60_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_head_60_);
lean_dec_ref_known(v_x_54_, 2);
return v_head_60_;
}
else
{
v_batches_56_ = v_x_54_;
goto v___jp_55_;
}
}
else
{
v_batches_56_ = v_x_54_;
goto v___jp_55_;
}
v___jp_55_:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued___closed__0));
v___x_58_ = l_List_foldrTR___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued_spec__0(v___x_57_, v_batches_56_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___lam__0(lean_object* v_inst_61_, lean_object* v_outbox_62_, lean_object* v_state_63_, lean_object* v_result_64_){
_start:
{
lean_object* v___y_67_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v_fst_76_; lean_object* v_snd_77_; 
v___x_73_ = lean_io_mono_ms_now();
v___x_74_ = lean_st_ref_take(v_state_63_);
if (lean_obj_tag(v_result_64_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_112_; 
lean_dec(v___x_73_);
v_a_85_ = lean_ctor_get(v_result_64_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v_result_64_);
if (v_isSharedCheck_112_ == 0)
{
v___x_87_ = v_result_64_;
v_isShared_88_ = v_isSharedCheck_112_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v_result_64_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_112_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_idle_89_; lean_object* v_idleSince_90_; lean_object* v_progressAt_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_108_; 
v_idle_89_ = lean_ctor_get(v___x_74_, 3);
v_idleSince_90_ = lean_ctor_get(v___x_74_, 4);
v_progressAt_91_ = lean_ctor_get(v___x_74_, 5);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; lean_object* v_unused_110_; lean_object* v_unused_111_; 
v_unused_109_ = lean_ctor_get(v___x_74_, 2);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v___x_74_, 1);
lean_dec(v_unused_110_);
v_unused_111_ = lean_ctor_get(v___x_74_, 0);
lean_dec(v_unused_111_);
v___x_93_ = v___x_74_;
v_isShared_94_ = v_isSharedCheck_108_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_progressAt_91_);
lean_inc(v_idleSince_90_);
lean_inc(v_idle_89_);
lean_dec(v___x_74_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_108_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; uint8_t v___x_100_; lean_object* v___x_102_; 
v___x_95_ = lean_unsigned_to_nat(0u);
v___x_96_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued___closed__0));
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_idle_89_);
v___x_98_ = lean_box(0);
v___x_99_ = 0;
v___x_100_ = 1;
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 1);
v___x_102_ = v___x_87_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_85_);
v___x_102_ = v_reuseFailAlloc_107_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_103_ = lean_box(0);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 3, v___x_103_);
lean_ctor_set(v___x_93_, 2, v___x_102_);
lean_ctor_set(v___x_93_, 1, v___x_95_);
lean_ctor_set(v___x_93_, 0, v___x_98_);
v___x_105_ = v___x_93_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_95_);
lean_ctor_set(v_reuseFailAlloc_106_, 2, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_106_, 3, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_106_, 4, v_idleSince_90_);
lean_ctor_set(v_reuseFailAlloc_106_, 5, v_progressAt_91_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*6, v___x_99_);
lean_ctor_set_uint8(v___x_105_, sizeof(void*)*6 + 1, v___x_100_);
v_fst_76_ = v___x_97_;
v_snd_77_ = v___x_105_;
goto v___jp_75_;
}
}
}
}
}
else
{
lean_object* v_queued_113_; lean_object* v_queuedBytes_114_; uint8_t v_writing_115_; uint8_t v_failed_116_; lean_object* v_error_117_; lean_object* v_idle_118_; lean_object* v_idleSince_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_139_; 
lean_dec_ref_known(v_result_64_, 1);
v_queued_113_ = lean_ctor_get(v___x_74_, 0);
v_queuedBytes_114_ = lean_ctor_get(v___x_74_, 1);
v_writing_115_ = lean_ctor_get_uint8(v___x_74_, sizeof(void*)*6);
v_failed_116_ = lean_ctor_get_uint8(v___x_74_, sizeof(void*)*6 + 1);
v_error_117_ = lean_ctor_get(v___x_74_, 2);
v_idle_118_ = lean_ctor_get(v___x_74_, 3);
v_idleSince_119_ = lean_ctor_get(v___x_74_, 4);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v___x_74_, 5);
lean_dec(v_unused_140_);
v___x_121_ = v___x_74_;
v_isShared_122_ = v_isSharedCheck_139_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_idleSince_119_);
lean_inc(v_idle_118_);
lean_inc(v_error_117_);
lean_inc(v_queuedBytes_114_);
lean_inc(v_queued_113_);
lean_dec(v___x_74_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_139_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
uint8_t v___x_123_; 
v___x_123_ = l_List_isEmpty___redArg(v_queued_113_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
lean_dec(v_queuedBytes_114_);
v___x_124_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued(v_queued_113_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_unsigned_to_nat(0u);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 5, v___x_73_);
lean_ctor_set(v___x_121_, 1, v___x_128_);
lean_ctor_set(v___x_121_, 0, v___x_127_);
v___x_130_ = v___x_121_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_128_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_error_117_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v_idle_118_);
lean_ctor_set(v_reuseFailAlloc_131_, 4, v_idleSince_119_);
lean_ctor_set(v_reuseFailAlloc_131_, 5, v___x_73_);
lean_ctor_set_uint8(v_reuseFailAlloc_131_, sizeof(void*)*6, v_writing_115_);
lean_ctor_set_uint8(v_reuseFailAlloc_131_, sizeof(void*)*6 + 1, v_failed_116_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
v_fst_76_ = v___x_126_;
v_snd_77_ = v___x_130_;
goto v___jp_75_;
}
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
lean_dec(v_idleSince_119_);
v___x_132_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued___closed__0));
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_idle_118_);
v___x_134_ = 0;
v___x_135_ = lean_box(0);
lean_inc(v___x_73_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 5, v___x_73_);
lean_ctor_set(v___x_121_, 4, v___x_73_);
lean_ctor_set(v___x_121_, 3, v___x_135_);
v___x_137_ = v___x_121_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_queued_113_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v_queuedBytes_114_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_error_117_);
lean_ctor_set(v_reuseFailAlloc_138_, 3, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_138_, 4, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_138_, 5, v___x_73_);
lean_ctor_set_uint8(v_reuseFailAlloc_138_, sizeof(void*)*6 + 1, v_failed_116_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_ctor_set_uint8(v___x_137_, sizeof(void*)*6, v___x_134_);
v_fst_76_ = v___x_133_;
v_snd_77_ = v___x_137_;
goto v___jp_75_;
}
}
}
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_68_ = lean_array_get_size(v___y_67_);
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_nat_dec_eq(v___x_68_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
v___x_71_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg(v_inst_61_, v_outbox_62_, v___y_67_);
return v___x_71_;
}
else
{
lean_object* v___x_72_; 
lean_dec_ref(v___y_67_);
lean_dec_ref(v_outbox_62_);
lean_dec_ref(v_inst_61_);
v___x_72_ = lean_box(0);
return v___x_72_;
}
}
v___jp_75_:
{
lean_object* v___x_78_; lean_object* v_snd_79_; 
v___x_78_ = lean_st_ref_put(v_state_63_, v_snd_77_);
v_snd_79_ = lean_ctor_get(v_fst_76_, 1);
if (lean_obj_tag(v_snd_79_) == 1)
{
lean_object* v_fst_80_; lean_object* v_val_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
lean_inc_ref(v_snd_79_);
v_fst_80_ = lean_ctor_get(v_fst_76_, 0);
lean_inc(v_fst_80_);
lean_dec_ref(v_fst_76_);
v_val_81_ = lean_ctor_get(v_snd_79_, 0);
lean_inc(v_val_81_);
lean_dec_ref_known(v_snd_79_, 1);
v___x_82_ = lean_box(0);
v___x_83_ = lean_io_promise_resolve(v___x_82_, v_val_81_);
lean_dec(v_val_81_);
v___y_67_ = v_fst_80_;
goto v___jp_66_;
}
else
{
lean_object* v_fst_84_; 
v_fst_84_ = lean_ctor_get(v_fst_76_, 0);
lean_inc(v_fst_84_);
lean_dec_ref(v_fst_76_);
v___y_67_ = v_fst_84_;
goto v___jp_66_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___lam__0___boxed(lean_object* v_inst_141_, lean_object* v_outbox_142_, lean_object* v_state_143_, lean_object* v_result_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___lam__0(v_inst_141_, v_outbox_142_, v_state_143_, v_result_144_);
lean_dec(v_state_143_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg(lean_object* v_inst_147_, lean_object* v_outbox_148_, lean_object* v_data_149_){
_start:
{
lean_object* v_sendAll_151_; lean_object* v_socket_152_; lean_object* v_state_153_; lean_object* v___f_154_; lean_object* v_val_156_; lean_object* v___x_160_; 
v_sendAll_151_ = lean_ctor_get(v_inst_147_, 1);
lean_inc_ref(v_sendAll_151_);
v_socket_152_ = lean_ctor_get(v_outbox_148_, 0);
lean_inc(v_socket_152_);
v_state_153_ = lean_ctor_get(v_outbox_148_, 2);
lean_inc(v_state_153_);
v___f_154_ = lean_alloc_closure((void*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_154_, 0, v_inst_147_);
lean_closure_set(v___f_154_, 1, v_outbox_148_);
lean_closure_set(v___f_154_, 2, v_state_153_);
v___x_160_ = lean_apply_3(v_sendAll_151_, v_socket_152_, v_data_149_, lean_box(0));
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
v___x_162_ = lean_task_pure(v_a_161_);
v_val_156_ = v___x_162_;
goto v___jp_155_;
}
else
{
lean_object* v_a_163_; 
v_a_163_ = lean_ctor_get(v___x_160_, 0);
lean_inc_ref(v_a_163_);
lean_dec_ref_known(v___x_160_, 1);
v_val_156_ = v_a_163_;
goto v___jp_155_;
}
v___jp_155_:
{
lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = 1;
v___x_159_ = l_BaseIO_chainTask___redArg(v_val_156_, v___f_154_, v___x_157_, v___x_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___boxed(lean_object* v_inst_164_, lean_object* v_outbox_165_, lean_object* v_data_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg(v_inst_164_, v_outbox_165_, v_data_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_outbox_171_, lean_object* v_data_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg(v_inst_170_, v_outbox_171_, v_data_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___boxed(lean_object* v_00_u03b1_175_, lean_object* v_inst_176_, lean_object* v_outbox_177_, lean_object* v_data_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write(v_00_u03b1_175_, v_inst_176_, v_outbox_177_, v_data_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send___redArg(lean_object* v_inst_187_, lean_object* v_outbox_188_, lean_object* v_buffer_189_){
_start:
{
lean_object* v_data_191_; lean_object* v_size_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_260_; 
v_data_191_ = lean_ctor_get(v_buffer_189_, 0);
v_size_192_ = lean_ctor_get(v_buffer_189_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_buffer_189_);
if (v_isSharedCheck_260_ == 0)
{
v___x_194_ = v_buffer_189_;
v_isShared_195_ = v_isSharedCheck_260_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_size_192_);
lean_inc(v_data_191_);
lean_dec(v_buffer_189_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_260_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_nat_dec_eq(v_size_192_, v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v_state_199_; lean_object* v___x_200_; lean_object* v_fst_202_; lean_object* v_snd_203_; uint8_t v_failed_213_; 
v___x_198_ = lean_io_mono_ms_now();
v_state_199_ = lean_ctor_get(v_outbox_188_, 2);
lean_inc(v_state_199_);
v___x_200_ = lean_st_ref_take(v_state_199_);
v_failed_213_ = lean_ctor_get_uint8(v___x_200_, sizeof(void*)*6 + 1);
if (v_failed_213_ == 0)
{
uint8_t v_writing_214_; 
v_writing_214_ = lean_ctor_get_uint8(v___x_200_, sizeof(void*)*6);
if (v_writing_214_ == 0)
{
lean_object* v_queued_215_; lean_object* v_queuedBytes_216_; lean_object* v_error_217_; lean_object* v_idle_218_; lean_object* v_idleSince_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_228_; 
lean_del_object(v___x_194_);
lean_dec(v_size_192_);
v_queued_215_ = lean_ctor_get(v___x_200_, 0);
v_queuedBytes_216_ = lean_ctor_get(v___x_200_, 1);
v_error_217_ = lean_ctor_get(v___x_200_, 2);
v_idle_218_ = lean_ctor_get(v___x_200_, 3);
v_idleSince_219_ = lean_ctor_get(v___x_200_, 4);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v___x_200_, 5);
lean_dec(v_unused_229_);
v___x_221_ = v___x_200_;
v_isShared_222_ = v_isSharedCheck_228_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_idleSince_219_);
lean_inc(v_idle_218_);
lean_inc(v_error_217_);
lean_inc(v_queuedBytes_216_);
lean_inc(v_queued_215_);
lean_dec(v___x_200_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_228_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_223_ = 1;
v___x_224_ = ((lean_object*)(l_Std_Http_Internal_Outbox_send___redArg___closed__1));
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 5, v___x_198_);
v___x_226_ = v___x_221_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_queued_215_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_queuedBytes_216_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_error_217_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v_idle_218_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v_idleSince_219_);
lean_ctor_set(v_reuseFailAlloc_227_, 5, v___x_198_);
lean_ctor_set_uint8(v_reuseFailAlloc_227_, sizeof(void*)*6 + 1, v_failed_213_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_ctor_set_uint8(v___x_226_, sizeof(void*)*6, v___x_223_);
v_fst_202_ = v___x_224_;
v_snd_203_ = v___x_226_;
goto v___jp_201_;
}
}
}
else
{
lean_object* v_queued_230_; lean_object* v_queuedBytes_231_; lean_object* v_error_232_; lean_object* v_idle_233_; lean_object* v_idleSince_234_; lean_object* v_progressAt_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_249_; 
lean_dec(v___x_198_);
v_queued_230_ = lean_ctor_get(v___x_200_, 0);
v_queuedBytes_231_ = lean_ctor_get(v___x_200_, 1);
v_error_232_ = lean_ctor_get(v___x_200_, 2);
v_idle_233_ = lean_ctor_get(v___x_200_, 3);
v_idleSince_234_ = lean_ctor_get(v___x_200_, 4);
v_progressAt_235_ = lean_ctor_get(v___x_200_, 5);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_249_ == 0)
{
v___x_237_ = v___x_200_;
v_isShared_238_ = v_isSharedCheck_249_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_progressAt_235_);
lean_inc(v_idleSince_234_);
lean_inc(v_idle_233_);
lean_inc(v_error_232_);
lean_inc(v_queuedBytes_231_);
lean_inc(v_queued_230_);
lean_dec(v___x_200_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_249_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_239_ = lean_nat_add(v_queuedBytes_231_, v_size_192_);
lean_dec(v_size_192_);
lean_dec(v_queuedBytes_231_);
lean_inc(v___x_239_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
v___x_241_ = lean_box(v_failed_213_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 1, v___x_240_);
lean_ctor_set(v___x_194_, 0, v___x_241_);
v___x_243_ = v___x_194_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_240_);
v___x_243_ = v_reuseFailAlloc_248_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
lean_inc_ref(v_data_191_);
v___x_244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_244_, 0, v_data_191_);
lean_ctor_set(v___x_244_, 1, v_queued_230_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_239_);
lean_ctor_set(v___x_237_, 0, v___x_244_);
v___x_246_ = v___x_237_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_247_, 2, v_error_232_);
lean_ctor_set(v_reuseFailAlloc_247_, 3, v_idle_233_);
lean_ctor_set(v_reuseFailAlloc_247_, 4, v_idleSince_234_);
lean_ctor_set(v_reuseFailAlloc_247_, 5, v_progressAt_235_);
lean_ctor_set_uint8(v_reuseFailAlloc_247_, sizeof(void*)*6, v_writing_214_);
lean_ctor_set_uint8(v_reuseFailAlloc_247_, sizeof(void*)*6 + 1, v_failed_213_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
v_fst_202_ = v___x_243_;
v_snd_203_ = v___x_246_;
goto v___jp_201_;
}
}
}
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
lean_dec(v___x_198_);
lean_dec(v_size_192_);
v___x_250_ = lean_box(0);
v___x_251_ = lean_box(v___x_197_);
if (v_isShared_195_ == 0)
{
lean_ctor_set(v___x_194_, 1, v___x_250_);
lean_ctor_set(v___x_194_, 0, v___x_251_);
v___x_253_ = v___x_194_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_250_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
v_fst_202_ = v___x_253_;
v_snd_203_ = v___x_200_;
goto v___jp_201_;
}
}
v___jp_201_:
{
lean_object* v___x_204_; lean_object* v_fst_205_; uint8_t v___x_206_; 
v___x_204_ = lean_st_ref_put(v_state_199_, v_snd_203_);
v_fst_205_ = lean_ctor_get(v_fst_202_, 0);
v___x_206_ = lean_unbox(v_fst_205_);
if (v___x_206_ == 0)
{
lean_object* v_snd_207_; 
lean_dec(v_state_199_);
lean_dec_ref(v_data_191_);
lean_dec_ref(v_outbox_188_);
lean_dec_ref(v_inst_187_);
v_snd_207_ = lean_ctor_get(v_fst_202_, 1);
lean_inc(v_snd_207_);
lean_dec_ref(v_fst_202_);
return v_snd_207_;
}
else
{
lean_object* v_snd_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v_failed_211_; 
v_snd_208_ = lean_ctor_get(v_fst_202_, 1);
lean_inc(v_snd_208_);
lean_dec_ref(v_fst_202_);
v___x_209_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg(v_inst_187_, v_outbox_188_, v_data_191_);
v___x_210_ = lean_st_ref_get(v_state_199_);
lean_dec(v_state_199_);
v_failed_211_ = lean_ctor_get_uint8(v___x_210_, sizeof(void*)*6 + 1);
lean_dec(v___x_210_);
if (v_failed_211_ == 0)
{
return v_snd_208_;
}
else
{
lean_object* v___x_212_; 
lean_dec(v_snd_208_);
v___x_212_ = lean_box(0);
return v___x_212_;
}
}
}
}
else
{
lean_object* v_state_255_; lean_object* v___x_256_; uint8_t v_failed_257_; 
lean_del_object(v___x_194_);
lean_dec(v_size_192_);
lean_dec_ref(v_data_191_);
lean_dec_ref(v_inst_187_);
v_state_255_ = lean_ctor_get(v_outbox_188_, 2);
lean_inc(v_state_255_);
lean_dec_ref(v_outbox_188_);
v___x_256_ = lean_st_ref_get(v_state_255_);
lean_dec(v_state_255_);
v_failed_257_ = lean_ctor_get_uint8(v___x_256_, sizeof(void*)*6 + 1);
lean_dec(v___x_256_);
if (v_failed_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = ((lean_object*)(l_Std_Http_Internal_Outbox_send___redArg___closed__0));
return v___x_258_;
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_box(0);
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send___redArg___boxed(lean_object* v_inst_261_, lean_object* v_outbox_262_, lean_object* v_buffer_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Http_Internal_Outbox_send___redArg(v_inst_261_, v_outbox_262_, v_buffer_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send(lean_object* v_00_u03b1_266_, lean_object* v_inst_267_, lean_object* v_outbox_268_, lean_object* v_buffer_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_Http_Internal_Outbox_send___redArg(v_inst_267_, v_outbox_268_, v_buffer_269_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send___boxed(lean_object* v_00_u03b1_272_, lean_object* v_inst_273_, lean_object* v_outbox_274_, lean_object* v_buffer_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_Http_Internal_Outbox_send(v_00_u03b1_272_, v_inst_273_, v_outbox_274_, v_buffer_275_);
return v_res_277_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_writing___redArg(lean_object* v_outbox_278_){
_start:
{
lean_object* v_state_280_; lean_object* v___x_281_; uint8_t v_writing_282_; 
v_state_280_ = lean_ctor_get(v_outbox_278_, 2);
v___x_281_ = lean_st_ref_get(v_state_280_);
v_writing_282_ = lean_ctor_get_uint8(v___x_281_, sizeof(void*)*6);
lean_dec(v___x_281_);
return v_writing_282_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writing___redArg___boxed(lean_object* v_outbox_283_, lean_object* v_a_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_Std_Http_Internal_Outbox_writing___redArg(v_outbox_283_);
lean_dec_ref(v_outbox_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_writing(lean_object* v_00_u03b1_287_, lean_object* v_outbox_288_){
_start:
{
uint8_t v___x_290_; 
v___x_290_ = l_Std_Http_Internal_Outbox_writing___redArg(v_outbox_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writing___boxed(lean_object* v_00_u03b1_291_, lean_object* v_outbox_292_, lean_object* v_a_293_){
_start:
{
uint8_t v_res_294_; lean_object* v_r_295_; 
v_res_294_ = l_Std_Http_Internal_Outbox_writing(v_00_u03b1_291_, v_outbox_292_);
lean_dec_ref(v_outbox_292_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f___redArg(lean_object* v_outbox_296_){
_start:
{
lean_object* v_state_298_; lean_object* v___x_299_; uint8_t v_writing_302_; 
v_state_298_ = lean_ctor_get(v_outbox_296_, 2);
v___x_299_ = lean_st_ref_get(v_state_298_);
v_writing_302_ = lean_ctor_get_uint8(v___x_299_, sizeof(void*)*6);
if (v_writing_302_ == 0)
{
lean_dec(v___x_299_);
goto v___jp_300_;
}
else
{
uint8_t v_failed_303_; 
v_failed_303_ = lean_ctor_get_uint8(v___x_299_, sizeof(void*)*6 + 1);
lean_dec(v___x_299_);
if (v_failed_303_ == 0)
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_fst_307_; lean_object* v_snd_308_; uint8_t v_writing_312_; 
v___x_304_ = lean_io_promise_new();
v___x_305_ = lean_st_ref_take(v_state_298_);
v_writing_312_ = lean_ctor_get_uint8(v___x_305_, sizeof(void*)*6);
if (v_writing_312_ == 0)
{
lean_dec(v___x_304_);
goto v___jp_310_;
}
else
{
uint8_t v_failed_313_; 
v_failed_313_ = lean_ctor_get_uint8(v___x_305_, sizeof(void*)*6 + 1);
if (v_failed_313_ == 0)
{
lean_object* v_idle_314_; 
v_idle_314_ = lean_ctor_get(v___x_305_, 3);
lean_inc(v_idle_314_);
if (lean_obj_tag(v_idle_314_) == 0)
{
lean_object* v_queued_315_; lean_object* v_queuedBytes_316_; lean_object* v_error_317_; lean_object* v_idleSince_318_; lean_object* v_progressAt_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_329_; 
v_queued_315_ = lean_ctor_get(v___x_305_, 0);
v_queuedBytes_316_ = lean_ctor_get(v___x_305_, 1);
v_error_317_ = lean_ctor_get(v___x_305_, 2);
v_idleSince_318_ = lean_ctor_get(v___x_305_, 4);
v_progressAt_319_ = lean_ctor_get(v___x_305_, 5);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v___x_305_, 3);
lean_dec(v_unused_330_);
v___x_321_ = v___x_305_;
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_progressAt_319_);
lean_inc(v_idleSince_318_);
lean_inc(v_error_317_);
lean_inc(v_queuedBytes_316_);
lean_inc(v_queued_315_);
lean_dec(v___x_305_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_329_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_323_ = lean_io_promise_result_opt(v___x_304_);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___x_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_304_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 3, v___x_325_);
v___x_327_ = v___x_321_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_queued_315_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_queuedBytes_316_);
lean_ctor_set(v_reuseFailAlloc_328_, 2, v_error_317_);
lean_ctor_set(v_reuseFailAlloc_328_, 3, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_328_, 4, v_idleSince_318_);
lean_ctor_set(v_reuseFailAlloc_328_, 5, v_progressAt_319_);
lean_ctor_set_uint8(v_reuseFailAlloc_328_, sizeof(void*)*6, v_writing_312_);
lean_ctor_set_uint8(v_reuseFailAlloc_328_, sizeof(void*)*6 + 1, v_failed_313_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
v_fst_307_ = v___x_324_;
v_snd_308_ = v___x_327_;
goto v___jp_306_;
}
}
}
else
{
lean_object* v_val_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_339_; 
lean_dec(v___x_304_);
v_val_331_ = lean_ctor_get(v_idle_314_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_idle_314_);
if (v_isSharedCheck_339_ == 0)
{
v___x_333_ = v_idle_314_;
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_val_331_);
lean_dec(v_idle_314_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_io_promise_result_opt(v_val_331_);
lean_dec(v_val_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_335_);
v___x_337_ = v___x_333_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
v_fst_307_ = v___x_337_;
v_snd_308_ = v___x_305_;
goto v___jp_306_;
}
}
}
}
else
{
lean_dec(v___x_304_);
goto v___jp_310_;
}
}
v___jp_306_:
{
lean_object* v___x_309_; 
v___x_309_ = lean_st_ref_put(v_state_298_, v_snd_308_);
return v_fst_307_;
}
v___jp_310_:
{
lean_object* v___x_311_; 
v___x_311_ = lean_box(0);
v_fst_307_ = v___x_311_;
v_snd_308_ = v___x_305_;
goto v___jp_306_;
}
}
else
{
goto v___jp_300_;
}
}
v___jp_300_:
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f___redArg___boxed(lean_object* v_outbox_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Std_Http_Internal_Outbox_idle_x3f___redArg(v_outbox_340_);
lean_dec_ref(v_outbox_340_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f(lean_object* v_00_u03b1_343_, lean_object* v_outbox_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Std_Http_Internal_Outbox_idle_x3f___redArg(v_outbox_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f___boxed(lean_object* v_00_u03b1_347_, lean_object* v_outbox_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Http_Internal_Outbox_idle_x3f(v_00_u03b1_347_, v_outbox_348_);
lean_dec_ref(v_outbox_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg(lean_object* v_outbox_353_){
_start:
{
lean_object* v_writeTimeout_355_; lean_object* v_state_356_; lean_object* v___x_357_; uint8_t v_failed_358_; 
v_writeTimeout_355_ = lean_ctor_get(v_outbox_353_, 1);
lean_inc(v_writeTimeout_355_);
v_state_356_ = lean_ctor_get(v_outbox_353_, 2);
lean_inc(v_state_356_);
lean_dec_ref(v_outbox_353_);
v___x_357_ = lean_st_ref_take(v_state_356_);
v_failed_358_ = lean_ctor_get_uint8(v___x_357_, sizeof(void*)*6 + 1);
if (v_failed_358_ == 0)
{
uint8_t v_writing_359_; lean_object* v_idle_360_; lean_object* v_idleSince_361_; lean_object* v_progressAt_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_380_; 
v_writing_359_ = lean_ctor_get_uint8(v___x_357_, sizeof(void*)*6);
v_idle_360_ = lean_ctor_get(v___x_357_, 3);
v_idleSince_361_ = lean_ctor_get(v___x_357_, 4);
v_progressAt_362_ = lean_ctor_get(v___x_357_, 5);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; lean_object* v_unused_382_; lean_object* v_unused_383_; 
v_unused_381_ = lean_ctor_get(v___x_357_, 2);
lean_dec(v_unused_381_);
v_unused_382_ = lean_ctor_get(v___x_357_, 1);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v___x_357_, 0);
lean_dec(v_unused_383_);
v___x_364_ = v___x_357_;
v_isShared_365_ = v_isSharedCheck_380_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_progressAt_362_);
lean_inc(v_idleSince_361_);
lean_inc(v_idle_360_);
lean_dec(v___x_357_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_380_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_366_ = 1;
v___x_367_ = lean_box(0);
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___closed__0));
v___x_370_ = l_Nat_reprFast(v_writeTimeout_355_);
v___x_371_ = lean_string_append(v___x_369_, v___x_370_);
lean_dec_ref(v___x_370_);
v___x_372_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___closed__1));
v___x_373_ = lean_string_append(v___x_371_, v___x_372_);
v___x_374_ = lean_mk_io_user_error(v___x_373_);
v___x_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 2, v___x_375_);
lean_ctor_set(v___x_364_, 1, v___x_368_);
lean_ctor_set(v___x_364_, 0, v___x_367_);
v___x_377_ = v___x_364_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v_idle_360_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v_idleSince_361_);
lean_ctor_set(v_reuseFailAlloc_379_, 5, v_progressAt_362_);
lean_ctor_set_uint8(v_reuseFailAlloc_379_, sizeof(void*)*6, v_writing_359_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*6 + 1, v___x_366_);
v___x_378_ = lean_st_ref_put(v_state_356_, v___x_377_);
lean_dec(v_state_356_);
return v___x_378_;
}
}
}
else
{
lean_object* v___x_384_; 
lean_dec(v_writeTimeout_355_);
v___x_384_ = lean_st_ref_put(v_state_356_, v___x_357_);
lean_dec(v_state_356_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___boxed(lean_object* v_outbox_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg(v_outbox_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire(lean_object* v_00_u03b1_388_, lean_object* v_outbox_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg(v_outbox_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___boxed(lean_object* v_00_u03b1_392_, lean_object* v_outbox_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire(v_00_u03b1_392_, v_outbox_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0(lean_object* v_w_398_, lean_object* v_lose_399_){
_start:
{
lean_object* v_finished_401_; lean_object* v_promise_402_; lean_object* v___x_403_; uint8_t v___y_405_; uint8_t v___x_412_; 
v_finished_401_ = lean_ctor_get(v_w_398_, 0);
v_promise_402_ = lean_ctor_get(v_w_398_, 1);
v___x_403_ = lean_st_ref_take(v_finished_401_);
v___x_412_ = lean_unbox(v___x_403_);
lean_dec(v___x_403_);
if (v___x_412_ == 0)
{
uint8_t v___x_413_; 
v___x_413_ = 1;
v___y_405_ = v___x_413_;
goto v___jp_404_;
}
else
{
uint8_t v___x_414_; 
v___x_414_ = 0;
v___y_405_ = v___x_414_;
goto v___jp_404_;
}
v___jp_404_:
{
uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = 1;
v___x_407_ = lean_box(v___x_406_);
v___x_408_ = lean_st_ref_put(v_finished_401_, v___x_407_);
if (v___y_405_ == 0)
{
lean_object* v___x_409_; 
v___x_409_ = lean_apply_1(v_lose_399_, lean_box(0));
return v___x_409_;
}
else
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec_ref(v_lose_399_);
v___x_410_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0___closed__0));
v___x_411_ = lean_io_promise_resolve(v___x_410_, v_promise_402_);
return v___x_411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0___boxed(lean_object* v_w_415_, lean_object* v_lose_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0(v_w_415_, v_lose_416_);
lean_dec_ref(v_w_415_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0(lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_439_; 
v_a_431_ = lean_ctor_get(v_x_429_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_429_);
if (v_isSharedCheck_439_ == 0)
{
v___x_433_ = v_x_429_;
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v_x_429_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_439_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_438_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; 
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
}
else
{
lean_object* v_a_440_; uint8_t v___x_441_; 
v_a_440_ = lean_ctor_get(v_x_429_, 0);
lean_inc(v_a_440_);
lean_dec_ref_known(v_x_429_, 1);
v___x_441_ = lean_unbox(v_a_440_);
lean_dec(v_a_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; 
v___x_442_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__1));
return v___x_442_;
}
else
{
lean_object* v___x_443_; 
v___x_443_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__4));
return v___x_443_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___boxed(lean_object* v_x_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0(v_x_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__1(lean_object* v___f_447_, lean_object* v_task_448_){
_start:
{
lean_object* v___x_450_; uint8_t v___x_451_; uint8_t v_a_453_; uint8_t v___x_458_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = 0;
v___x_458_ = lean_io_get_task_state(v_task_448_);
if (v___x_458_ == 2)
{
uint8_t v___x_459_; 
v___x_459_ = 1;
v_a_453_ = v___x_459_;
goto v___jp_452_;
}
else
{
v_a_453_ = v___x_451_;
goto v___jp_452_;
}
v___jp_452_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_box(v_a_453_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
v___x_457_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_450_, v___x_451_, v___x_456_, v___f_447_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__1___boxed(lean_object* v___f_460_, lean_object* v_task_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__1(v___f_460_, v_task_461_);
lean_dec_ref(v_task_461_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__2(lean_object* v___x_464_){
_start:
{
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__2___boxed(lean_object* v___x_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__2(v___x_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3(lean_object* v_waiter_471_, lean_object* v_x_472_){
_start:
{
lean_object* v___f_474_; lean_object* v___x_475_; 
v___f_474_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3___closed__0));
v___x_475_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0(v_waiter_471_, v___f_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3___boxed(lean_object* v_waiter_476_, lean_object* v_x_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3(v_waiter_476_, v_x_477_);
lean_dec(v_x_477_);
lean_dec_ref(v_waiter_476_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__4(lean_object* v_task_480_, lean_object* v_waiter_481_){
_start:
{
lean_object* v___f_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___f_483_ = lean_alloc_closure((void*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_483_, 0, v_waiter_481_);
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = 1;
v___x_486_ = l_BaseIO_chainTask___redArg(v_task_480_, v___f_483_, v___x_484_, v___x_485_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__4___boxed(lean_object* v_task_489_, lean_object* v_waiter_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__4(v_task_489_, v_waiter_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__5(lean_object* v___x_493_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__5___boxed(lean_object* v___x_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__5(v___x_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector(lean_object* v_task_503_){
_start:
{
lean_object* v___f_504_; lean_object* v___f_505_; lean_object* v___f_506_; lean_object* v___f_507_; lean_object* v___x_508_; 
v___f_504_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___closed__0));
lean_inc_ref(v_task_503_);
v___f_505_ = lean_alloc_closure((void*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__1___boxed), 3, 2);
lean_closure_set(v___f_505_, 0, v___f_504_);
lean_closure_set(v___f_505_, 1, v_task_503_);
v___f_506_ = lean_alloc_closure((void*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_506_, 0, v_task_503_);
v___f_507_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___closed__1));
v___x_508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_508_, 0, v___f_505_);
lean_ctor_set(v___x_508_, 1, v___f_506_);
lean_ctor_set(v___x_508_, 2, v___f_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Internal_Outbox_awaitIdle_spec__1(lean_object* v_a_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_nat_to_int(v_a_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0(lean_object* v_x_513_){
_start:
{
if (lean_obj_tag(v_x_513_) == 0)
{
lean_object* v___x_515_; 
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v_x_513_);
return v___x_515_;
}
else
{
lean_object* v___x_516_; 
lean_dec_ref_known(v_x_513_, 1);
v___x_516_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___closed__0));
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___boxed(lean_object* v_x_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0(v_x_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2(lean_object* v_x_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___closed__1));
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___boxed(lean_object* v_x_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2(v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__4(lean_object* v_val_531_, lean_object* v___f_532_, lean_object* v___f_533_, uint8_t v___x_534_, lean_object* v___f_535_, lean_object* v_x_536_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref(v___f_535_);
lean_dec_ref(v___f_533_);
lean_dec_ref(v___f_532_);
lean_dec_ref(v_val_531_);
v_a_538_ = lean_ctor_get(v_x_536_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_546_ == 0)
{
v___x_540_ = v_x_536_;
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v_x_536_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_546_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_a_547_ = lean_ctor_get(v_x_536_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v_x_536_, 1);
v___x_548_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector(v_val_531_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___f_532_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v_a_547_);
lean_ctor_set(v___x_550_, 1, v___f_533_);
v___x_551_ = lean_unsigned_to_nat(2u);
v___x_552_ = lean_mk_empty_array_with_capacity(v___x_551_);
v___x_553_ = lean_array_push(v___x_552_, v___x_549_);
v___x_554_ = lean_array_push(v___x_553_, v___x_550_);
v___x_555_ = lean_unsigned_to_nat(0u);
v___x_556_ = l_Std_Async_Selectable_one___redArg(v___x_554_);
v___x_557_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_555_, v___x_534_, v___x_556_, v___f_535_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__4___boxed(lean_object* v_val_558_, lean_object* v___f_559_, lean_object* v___f_560_, lean_object* v___x_561_, lean_object* v___f_562_, lean_object* v_x_563_, lean_object* v___y_564_){
_start:
{
uint8_t v___x_2059__boxed_565_; lean_object* v_res_566_; 
v___x_2059__boxed_565_ = lean_unbox(v___x_561_);
v_res_566_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__4(v_val_558_, v___f_559_, v___f_560_, v___x_2059__boxed_565_, v___f_562_, v_x_563_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__3(uint8_t v___x_567_, lean_object* v_x_568_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_box(v___x_567_);
v___x_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__3___boxed(lean_object* v___x_573_, lean_object* v_x_574_, lean_object* v___y_575_){
_start:
{
uint8_t v___x_2117__boxed_576_; lean_object* v_res_577_; 
v___x_2117__boxed_576_ = lean_unbox(v___x_573_);
v_res_577_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__3(v___x_2117__boxed_576_, v_x_574_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__5(lean_object* v___x_578_, lean_object* v_val_579_, lean_object* v___f_580_, lean_object* v___f_581_, lean_object* v_outbox_582_, lean_object* v___f_583_, lean_object* v_x_584_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
lean_dec_ref(v___f_583_);
lean_dec_ref(v_outbox_582_);
lean_dec_ref(v___f_581_);
lean_dec_ref(v___f_580_);
lean_dec_ref(v_val_579_);
v_a_586_ = lean_ctor_get(v_x_584_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v_x_584_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v_x_584_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_593_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_592_; 
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_617_; 
v_a_595_ = lean_ctor_get(v_x_584_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_617_ == 0)
{
v___x_597_ = v_x_584_;
v_isShared_598_ = v_isSharedCheck_617_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v_x_584_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_617_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
uint8_t v___x_599_; 
v___x_599_ = lean_nat_dec_le(v___x_578_, v_a_595_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___f_601_; lean_object* v___x_602_; lean_object* v___f_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_del_object(v___x_597_);
lean_dec_ref(v___f_583_);
lean_dec_ref(v_outbox_582_);
v___x_600_ = lean_box(v___x_599_);
v___f_601_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_601_, 0, v___x_600_);
v___x_602_ = lean_box(v___x_599_);
v___f_603_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_603_, 0, v_val_579_);
lean_closure_set(v___f_603_, 1, v___f_580_);
lean_closure_set(v___f_603_, 2, v___f_601_);
lean_closure_set(v___f_603_, 3, v___x_602_);
lean_closure_set(v___f_603_, 4, v___f_581_);
v___x_604_ = lean_nat_sub(v___x_578_, v_a_595_);
lean_dec(v_a_595_);
v___x_605_ = lean_nat_to_int(v___x_604_);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = l_Std_Async_Selector_sleep(v___x_605_);
lean_dec(v___x_605_);
v___x_608_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_606_, v___x_599_, v___x_607_, v___f_603_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
lean_dec(v_a_595_);
lean_dec_ref(v___f_581_);
lean_dec_ref(v___f_580_);
lean_dec_ref(v_val_579_);
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = 0;
v___x_611_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg(v_outbox_582_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_611_);
v___x_613_ = v___x_597_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_616_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___x_615_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_609_, v___x_610_, v___x_614_, v___f_583_);
return v___x_615_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__5___boxed(lean_object* v___x_618_, lean_object* v_val_619_, lean_object* v___f_620_, lean_object* v___f_621_, lean_object* v_outbox_622_, lean_object* v___f_623_, lean_object* v_x_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__5(v___x_618_, v_val_619_, v___f_620_, v___f_621_, v_outbox_622_, v___f_623_, v_x_624_);
lean_dec(v___x_618_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__6(lean_object* v_writeTimeout_627_, lean_object* v_val_628_, lean_object* v___f_629_, lean_object* v___f_630_, lean_object* v_outbox_631_, lean_object* v___f_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_643_; 
lean_dec_ref(v___f_632_);
lean_dec_ref(v_outbox_631_);
lean_dec_ref(v___f_630_);
lean_dec_ref(v___f_629_);
lean_dec_ref(v_val_628_);
v_a_635_ = lean_ctor_get(v_x_633_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_643_ == 0)
{
v___x_637_ = v_x_633_;
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v_x_633_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_642_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; 
v___x_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_659_; 
v_a_644_ = lean_ctor_get(v_x_633_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_659_ == 0)
{
v___x_646_ = v_x_633_;
v_isShared_647_ = v_isSharedCheck_659_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v_x_633_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_659_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v_progressAt_648_; lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___x_651_; uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v_progressAt_648_ = lean_ctor_get(v_a_644_, 5);
lean_inc(v_progressAt_648_);
lean_dec(v_a_644_);
v___x_649_ = lean_nat_add(v_progressAt_648_, v_writeTimeout_627_);
lean_dec(v_progressAt_648_);
v___f_650_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_650_, 0, v___x_649_);
lean_closure_set(v___f_650_, 1, v_val_628_);
lean_closure_set(v___f_650_, 2, v___f_629_);
lean_closure_set(v___f_650_, 3, v___f_630_);
lean_closure_set(v___f_650_, 4, v_outbox_631_);
lean_closure_set(v___f_650_, 5, v___f_632_);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = 0;
v___x_653_ = lean_io_mono_ms_now();
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_653_);
v___x_655_ = v___x_646_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_658_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
v___x_657_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_651_, v___x_652_, v___x_656_, v___f_650_);
return v___x_657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__6___boxed(lean_object* v_writeTimeout_660_, lean_object* v_val_661_, lean_object* v___f_662_, lean_object* v___f_663_, lean_object* v_outbox_664_, lean_object* v___f_665_, lean_object* v_x_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__6(v_writeTimeout_660_, v_val_661_, v___f_662_, v___f_663_, v_outbox_664_, v___f_665_, v_x_666_);
lean_dec(v_writeTimeout_660_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__7(lean_object* v_outbox_669_, lean_object* v___f_670_, lean_object* v___f_671_, lean_object* v___f_672_, lean_object* v_x_673_){
_start:
{
if (lean_obj_tag(v_x_673_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v___f_672_);
lean_dec_ref(v___f_671_);
lean_dec_ref(v___f_670_);
lean_dec_ref(v_outbox_669_);
v_a_675_ = lean_ctor_get(v_x_673_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_673_);
if (v_isSharedCheck_683_ == 0)
{
v___x_677_ = v_x_673_;
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v_x_673_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_683_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_682_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_707_; 
v_a_684_ = lean_ctor_get(v_x_673_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_673_);
if (v_isSharedCheck_707_ == 0)
{
v___x_686_ = v_x_673_;
v_isShared_687_ = v_isSharedCheck_707_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v_x_673_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_707_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
if (lean_obj_tag(v_a_684_) == 1)
{
lean_object* v_val_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_705_; 
v_val_688_ = lean_ctor_get(v_a_684_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_a_684_);
if (v_isSharedCheck_705_ == 0)
{
v___x_690_ = v_a_684_;
v_isShared_691_ = v_isSharedCheck_705_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_val_688_);
lean_dec(v_a_684_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_705_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v_writeTimeout_692_; lean_object* v_state_693_; lean_object* v___f_694_; lean_object* v___x_695_; uint8_t v___x_696_; lean_object* v___x_697_; lean_object* v___x_699_; 
v_writeTimeout_692_ = lean_ctor_get(v_outbox_669_, 1);
lean_inc(v_writeTimeout_692_);
v_state_693_ = lean_ctor_get(v_outbox_669_, 2);
lean_inc(v_state_693_);
v___f_694_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_694_, 0, v_writeTimeout_692_);
lean_closure_set(v___f_694_, 1, v_val_688_);
lean_closure_set(v___f_694_, 2, v___f_670_);
lean_closure_set(v___f_694_, 3, v___f_671_);
lean_closure_set(v___f_694_, 4, v_outbox_669_);
lean_closure_set(v___f_694_, 5, v___f_672_);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = 0;
v___x_697_ = lean_st_ref_get(v_state_693_);
lean_dec(v_state_693_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_697_);
v___x_699_ = v___x_686_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_704_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 0);
lean_ctor_set(v___x_690_, 0, v___x_699_);
v___x_701_ = v___x_690_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_703_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; 
v___x_702_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_695_, v___x_696_, v___x_701_, v___f_694_);
return v___x_702_;
}
}
}
}
else
{
lean_object* v___x_706_; 
lean_del_object(v___x_686_);
lean_dec(v_a_684_);
lean_dec_ref(v___f_672_);
lean_dec_ref(v___f_671_);
lean_dec_ref(v___f_670_);
lean_dec_ref(v_outbox_669_);
v___x_706_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___closed__0));
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__7___boxed(lean_object* v_outbox_708_, lean_object* v___f_709_, lean_object* v___f_710_, lean_object* v___f_711_, lean_object* v_x_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__7(v_outbox_708_, v___f_709_, v___f_710_, v___f_711_, v_x_712_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__1(lean_object* v_outbox_717_, lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v_outbox_717_);
v_a_720_ = lean_ctor_get(v_x_718_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_728_ == 0)
{
v___x_722_ = v_x_718_;
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v_x_718_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_728_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_727_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
}
else
{
lean_object* v_a_729_; uint8_t v___x_730_; 
v_a_729_ = lean_ctor_get(v_x_718_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v_x_718_, 1);
v___x_730_ = lean_unbox(v_a_729_);
lean_dec(v_a_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_outbox_717_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; 
lean_dec_ref(v_outbox_717_);
v___x_732_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___closed__0));
return v___x_732_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__1___boxed(lean_object* v_outbox_733_, lean_object* v_x_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__1(v_outbox_733_, v_x_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg(lean_object* v_outbox_737_){
_start:
{
lean_object* v___f_739_; lean_object* v___f_740_; lean_object* v___f_741_; lean_object* v___f_742_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___f_739_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___closed__0));
lean_inc_ref_n(v_outbox_737_, 2);
v___f_740_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_740_, 0, v_outbox_737_);
v___f_741_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___closed__1));
v___f_742_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_742_, 0, v_outbox_737_);
lean_closure_set(v___f_742_, 1, v___f_741_);
lean_closure_set(v___f_742_, 2, v___f_740_);
lean_closure_set(v___f_742_, 3, v___f_739_);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = 0;
v___x_745_ = l_Std_Http_Internal_Outbox_idle_x3f___redArg(v_outbox_737_);
lean_dec_ref(v_outbox_737_);
v___x_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
v___x_748_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_743_, v___x_744_, v___x_747_, v___f_742_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___boxed(lean_object* v_outbox_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_outbox_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle(lean_object* v_00_u03b1_752_, lean_object* v_outbox_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_outbox_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___boxed(lean_object* v_00_u03b1_756_, lean_object* v_outbox_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_Http_Internal_Outbox_awaitIdle(v_00_u03b1_756_, v_outbox_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Internal_Outbox_awaitIdle_spec__0(lean_object* v_a_760_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_nat_to_int(v_a_760_);
v___x_762_ = l_Rat_ofInt(v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idleFor_x3f___redArg(lean_object* v_outbox_763_){
_start:
{
lean_object* v_state_765_; lean_object* v___x_766_; uint8_t v_writing_767_; 
v_state_765_ = lean_ctor_get(v_outbox_763_, 2);
v___x_766_ = lean_st_ref_get(v_state_765_);
v_writing_767_ = lean_ctor_get_uint8(v___x_766_, sizeof(void*)*6);
if (v_writing_767_ == 0)
{
lean_object* v_idleSince_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_idleSince_768_ = lean_ctor_get(v___x_766_, 4);
lean_inc(v_idleSince_768_);
lean_dec(v___x_766_);
v___x_769_ = lean_io_mono_ms_now();
v___x_770_ = lean_nat_sub(v___x_769_, v_idleSince_768_);
lean_dec(v_idleSince_768_);
lean_dec(v___x_769_);
v___x_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; 
lean_dec(v___x_766_);
v___x_772_ = lean_box(0);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idleFor_x3f___redArg___boxed(lean_object* v_outbox_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_Http_Internal_Outbox_idleFor_x3f___redArg(v_outbox_773_);
lean_dec_ref(v_outbox_773_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idleFor_x3f(lean_object* v_00_u03b1_776_, lean_object* v_outbox_777_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_Http_Internal_Outbox_idleFor_x3f___redArg(v_outbox_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idleFor_x3f___boxed(lean_object* v_00_u03b1_780_, lean_object* v_outbox_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Std_Http_Internal_Outbox_idleFor_x3f(v_00_u03b1_780_, v_outbox_781_);
lean_dec_ref(v_outbox_781_);
return v_res_783_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_failed___redArg(lean_object* v_outbox_784_){
_start:
{
lean_object* v_state_786_; lean_object* v___x_787_; uint8_t v_failed_788_; 
v_state_786_ = lean_ctor_get(v_outbox_784_, 2);
v___x_787_ = lean_st_ref_get(v_state_786_);
v_failed_788_ = lean_ctor_get_uint8(v___x_787_, sizeof(void*)*6 + 1);
lean_dec(v___x_787_);
return v_failed_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_failed___redArg___boxed(lean_object* v_outbox_789_, lean_object* v_a_790_){
_start:
{
uint8_t v_res_791_; lean_object* v_r_792_; 
v_res_791_ = l_Std_Http_Internal_Outbox_failed___redArg(v_outbox_789_);
lean_dec_ref(v_outbox_789_);
v_r_792_ = lean_box(v_res_791_);
return v_r_792_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_failed(lean_object* v_00_u03b1_793_, lean_object* v_outbox_794_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = l_Std_Http_Internal_Outbox_failed___redArg(v_outbox_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_failed___boxed(lean_object* v_00_u03b1_797_, lean_object* v_outbox_798_, lean_object* v_a_799_){
_start:
{
uint8_t v_res_800_; lean_object* v_r_801_; 
v_res_800_ = l_Std_Http_Internal_Outbox_failed(v_00_u03b1_797_, v_outbox_798_);
lean_dec_ref(v_outbox_798_);
v_r_801_ = lean_box(v_res_800_);
return v_r_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__0(lean_object* v_x_802_){
_start:
{
uint8_t v___y_805_; 
if (lean_obj_tag(v_x_802_) == 0)
{
lean_object* v___x_809_; 
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v_x_802_);
return v___x_809_;
}
else
{
lean_object* v_a_810_; uint8_t v___x_811_; 
v_a_810_ = lean_ctor_get(v_x_802_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v_x_802_, 1);
v___x_811_ = lean_unbox(v_a_810_);
lean_dec(v_a_810_);
if (v___x_811_ == 0)
{
uint8_t v___x_812_; 
v___x_812_ = 1;
v___y_805_ = v___x_812_;
goto v___jp_804_;
}
else
{
uint8_t v___x_813_; 
v___x_813_ = 0;
v___y_805_ = v___x_813_;
goto v___jp_804_;
}
}
v___jp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = lean_box(v___y_805_);
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__0___boxed(lean_object* v_x_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__0(v_x_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__1(lean_object* v_outbox_817_, lean_object* v___f_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_819_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_829_; 
lean_dec_ref(v___f_818_);
v_a_821_ = lean_ctor_get(v_x_819_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v_x_819_);
if (v_isSharedCheck_829_ == 0)
{
v___x_823_ = v_x_819_;
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v_x_819_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_829_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_828_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; 
v___x_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
return v___x_827_;
}
}
}
else
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_842_; 
v_isSharedCheck_842_ = !lean_is_exclusive(v_x_819_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_x_819_, 0);
lean_dec(v_unused_843_);
v___x_831_ = v_x_819_;
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
else
{
lean_dec(v_x_819_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_842_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; uint8_t v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = 0;
v___x_835_ = l_Std_Http_Internal_Outbox_failed___redArg(v_outbox_817_);
v___x_836_ = lean_box(v___x_835_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_836_);
v___x_838_ = v___x_831_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_841_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
v___x_840_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_833_, v___x_834_, v___x_839_, v___f_818_);
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__1___boxed(lean_object* v_outbox_844_, lean_object* v___f_845_, lean_object* v_x_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__1(v_outbox_844_, v___f_845_, v_x_846_);
lean_dec_ref(v_outbox_844_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg(lean_object* v_outbox_850_){
_start:
{
lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___f_852_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitWritten___redArg___closed__0));
lean_inc_ref(v_outbox_850_);
v___f_853_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_853_, 0, v_outbox_850_);
lean_closure_set(v___f_853_, 1, v___f_852_);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = 0;
v___x_856_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_outbox_850_);
v___x_857_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_854_, v___x_855_, v___x_856_, v___f_853_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___boxed(lean_object* v_outbox_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg(v_outbox_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten(lean_object* v_00_u03b1_861_, lean_object* v_outbox_862_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg(v_outbox_862_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___boxed(lean_object* v_00_u03b1_865_, lean_object* v_outbox_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Std_Http_Internal_Outbox_awaitWritten(v_00_u03b1_865_, v_outbox_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___redArg(lean_object* v_outbox_869_){
_start:
{
lean_object* v_state_871_; lean_object* v___x_872_; lean_object* v_queued_873_; lean_object* v_queuedBytes_874_; uint8_t v_writing_875_; uint8_t v_failed_876_; lean_object* v_error_877_; lean_object* v_idle_878_; lean_object* v_idleSince_879_; lean_object* v_progressAt_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_889_; 
v_state_871_ = lean_ctor_get(v_outbox_869_, 2);
v___x_872_ = lean_st_ref_take(v_state_871_);
v_queued_873_ = lean_ctor_get(v___x_872_, 0);
v_queuedBytes_874_ = lean_ctor_get(v___x_872_, 1);
v_writing_875_ = lean_ctor_get_uint8(v___x_872_, sizeof(void*)*6);
v_failed_876_ = lean_ctor_get_uint8(v___x_872_, sizeof(void*)*6 + 1);
v_error_877_ = lean_ctor_get(v___x_872_, 2);
v_idle_878_ = lean_ctor_get(v___x_872_, 3);
v_idleSince_879_ = lean_ctor_get(v___x_872_, 4);
v_progressAt_880_ = lean_ctor_get(v___x_872_, 5);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_889_ == 0)
{
v___x_882_ = v___x_872_;
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_progressAt_880_);
lean_inc(v_idleSince_879_);
lean_inc(v_idle_878_);
lean_inc(v_error_877_);
lean_inc(v_queuedBytes_874_);
lean_inc(v_queued_873_);
lean_dec(v___x_872_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_889_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_box(0);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 2, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_queued_873_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_queuedBytes_874_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_idle_878_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_idleSince_879_);
lean_ctor_set(v_reuseFailAlloc_888_, 5, v_progressAt_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, sizeof(void*)*6, v_writing_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_888_, sizeof(void*)*6 + 1, v_failed_876_);
v___x_886_ = v_reuseFailAlloc_888_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; 
v___x_887_ = lean_st_ref_put(v_state_871_, v___x_886_);
return v_error_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___redArg___boxed(lean_object* v_outbox_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_Http_Internal_Outbox_takeError_x3f___redArg(v_outbox_890_);
lean_dec_ref(v_outbox_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f(lean_object* v_00_u03b1_893_, lean_object* v_outbox_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Std_Http_Internal_Outbox_takeError_x3f___redArg(v_outbox_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___boxed(lean_object* v_00_u03b1_897_, lean_object* v_outbox_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Std_Http_Internal_Outbox_takeError_x3f(v_00_u03b1_897_, v_outbox_898_);
lean_dec_ref(v_outbox_898_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg___lam__0(lean_object* v_limit_906_, lean_object* v_outbox_907_, lean_object* v_x_908_){
_start:
{
if (lean_obj_tag(v_x_908_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v_outbox_907_);
v_a_910_ = lean_ctor_get(v_x_908_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v_x_908_);
if (v_isSharedCheck_918_ == 0)
{
v___x_912_ = v_x_908_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v_x_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_917_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; 
v___x_916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
return v___x_916_;
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_938_; 
v_a_919_ = lean_ctor_get(v_x_908_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v_x_908_);
if (v_isSharedCheck_938_ == 0)
{
v___x_921_ = v_x_908_;
v_isShared_922_ = v_isSharedCheck_938_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v_x_908_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_938_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
if (lean_obj_tag(v_a_919_) == 0)
{
lean_object* v___x_923_; 
lean_del_object(v___x_921_);
lean_dec_ref(v_outbox_907_);
v___x_923_ = ((lean_object*)(l_Std_Http_Internal_Outbox_push___redArg___lam__0___closed__1));
return v___x_923_;
}
else
{
lean_object* v_val_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_937_; 
v_val_924_ = lean_ctor_get(v_a_919_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v_a_919_);
if (v_isSharedCheck_937_ == 0)
{
v___x_926_ = v_a_919_;
v_isShared_927_ = v_isSharedCheck_937_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_val_924_);
lean_dec(v_a_919_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_937_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
uint8_t v___x_928_; 
v___x_928_ = lean_nat_dec_le(v_val_924_, v_limit_906_);
lean_dec(v_val_924_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_del_object(v___x_926_);
lean_del_object(v___x_921_);
v___x_929_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg(v_outbox_907_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_932_; 
lean_dec_ref(v_outbox_907_);
v___x_930_ = lean_box(v___x_928_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_930_);
v___x_932_ = v___x_921_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_936_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_934_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 0);
lean_ctor_set(v___x_926_, 0, v___x_932_);
v___x_934_ = v___x_926_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg___lam__0___boxed(lean_object* v_limit_939_, lean_object* v_outbox_940_, lean_object* v_x_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Std_Http_Internal_Outbox_push___redArg___lam__0(v_limit_939_, v_outbox_940_, v_x_941_);
lean_dec(v_limit_939_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg(lean_object* v_inst_944_, lean_object* v_outbox_945_, lean_object* v_buffer_946_, lean_object* v_limit_947_){
_start:
{
lean_object* v___f_949_; lean_object* v___x_950_; uint8_t v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
lean_inc_ref(v_outbox_945_);
v___f_949_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_push___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_949_, 0, v_limit_947_);
lean_closure_set(v___f_949_, 1, v_outbox_945_);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = 0;
v___x_952_ = l_Std_Http_Internal_Outbox_send___redArg(v_inst_944_, v_outbox_945_, v_buffer_946_);
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
v___x_955_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_950_, v___x_951_, v___x_954_, v___f_949_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg___boxed(lean_object* v_inst_956_, lean_object* v_outbox_957_, lean_object* v_buffer_958_, lean_object* v_limit_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_Http_Internal_Outbox_push___redArg(v_inst_956_, v_outbox_957_, v_buffer_958_, v_limit_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push(lean_object* v_00_u03b1_962_, lean_object* v_inst_963_, lean_object* v_outbox_964_, lean_object* v_buffer_965_, lean_object* v_limit_966_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_Http_Internal_Outbox_push___redArg(v_inst_963_, v_outbox_964_, v_buffer_965_, v_limit_966_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___boxed(lean_object* v_00_u03b1_969_, lean_object* v_inst_970_, lean_object* v_outbox_971_, lean_object* v_buffer_972_, lean_object* v_limit_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_Http_Internal_Outbox_push(v_00_u03b1_969_, v_inst_970_, v_outbox_971_, v_buffer_972_, v_limit_973_);
return v_res_975_;
}
}
lean_object* runtime_initialize_Std_Http_Transport(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Transport_Outbox(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Http_Transport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Transport_Outbox(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Transport(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Transport_Outbox(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Transport(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Transport_Outbox(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Transport_Outbox(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Transport_Outbox(builtin);
}
#ifdef __cplusplus
}
#endif

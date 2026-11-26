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
static const lean_ctor_object l_Std_Http_Internal_Outbox_new___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 8, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writeDeadline_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writeDeadline_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writeDeadline_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writeDeadline_x3f___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_a_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_111_; 
lean_dec(v___x_73_);
v_a_85_ = lean_ctor_get(v_result_64_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v_result_64_);
if (v_isSharedCheck_111_ == 0)
{
v___x_87_ = v_result_64_;
v_isShared_88_ = v_isSharedCheck_111_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_a_85_);
lean_dec(v_result_64_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_111_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_idle_89_; lean_object* v_progressAt_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_107_; 
v_idle_89_ = lean_ctor_get(v___x_74_, 3);
v_progressAt_90_ = lean_ctor_get(v___x_74_, 4);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; lean_object* v_unused_109_; lean_object* v_unused_110_; 
v_unused_108_ = lean_ctor_get(v___x_74_, 2);
lean_dec(v_unused_108_);
v_unused_109_ = lean_ctor_get(v___x_74_, 1);
lean_dec(v_unused_109_);
v_unused_110_ = lean_ctor_get(v___x_74_, 0);
lean_dec(v_unused_110_);
v___x_92_ = v___x_74_;
v_isShared_93_ = v_isSharedCheck_107_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_progressAt_90_);
lean_inc(v_idle_89_);
lean_dec(v___x_74_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_107_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; uint8_t v___x_99_; lean_object* v___x_101_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued___closed__0));
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v_idle_89_);
v___x_97_ = lean_box(0);
v___x_98_ = 0;
v___x_99_ = 1;
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 1);
v___x_101_ = v___x_87_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_85_);
v___x_101_ = v_reuseFailAlloc_106_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_102_ = lean_box(0);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 3, v___x_102_);
lean_ctor_set(v___x_92_, 2, v___x_101_);
lean_ctor_set(v___x_92_, 1, v___x_94_);
lean_ctor_set(v___x_92_, 0, v___x_97_);
v___x_104_ = v___x_92_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_105_, 3, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_105_, 4, v_progressAt_90_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*5, v___x_98_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*5 + 1, v___x_99_);
v_fst_76_ = v___x_96_;
v_snd_77_ = v___x_104_;
goto v___jp_75_;
}
}
}
}
}
else
{
lean_object* v_queued_112_; lean_object* v_queuedBytes_113_; uint8_t v_writing_114_; uint8_t v_failed_115_; lean_object* v_error_116_; lean_object* v_idle_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_137_; 
lean_dec_ref_known(v_result_64_, 1);
v_queued_112_ = lean_ctor_get(v___x_74_, 0);
v_queuedBytes_113_ = lean_ctor_get(v___x_74_, 1);
v_writing_114_ = lean_ctor_get_uint8(v___x_74_, sizeof(void*)*5);
v_failed_115_ = lean_ctor_get_uint8(v___x_74_, sizeof(void*)*5 + 1);
v_error_116_ = lean_ctor_get(v___x_74_, 2);
v_idle_117_ = lean_ctor_get(v___x_74_, 3);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v___x_74_, 4);
lean_dec(v_unused_138_);
v___x_119_ = v___x_74_;
v_isShared_120_ = v_isSharedCheck_137_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_idle_117_);
lean_inc(v_error_116_);
lean_inc(v_queuedBytes_113_);
lean_inc(v_queued_112_);
lean_dec(v___x_74_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_137_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
uint8_t v___x_121_; 
v___x_121_ = l_List_isEmpty___redArg(v_queued_112_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
lean_dec(v_queuedBytes_113_);
v___x_122_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued(v_queued_112_);
v___x_123_ = lean_box(0);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_unsigned_to_nat(0u);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 4, v___x_73_);
lean_ctor_set(v___x_119_, 1, v___x_126_);
lean_ctor_set(v___x_119_, 0, v___x_125_);
v___x_128_ = v___x_119_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_129_, 2, v_error_116_);
lean_ctor_set(v_reuseFailAlloc_129_, 3, v_idle_117_);
lean_ctor_set(v_reuseFailAlloc_129_, 4, v___x_73_);
lean_ctor_set_uint8(v_reuseFailAlloc_129_, sizeof(void*)*5, v_writing_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_129_, sizeof(void*)*5 + 1, v_failed_115_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
v_fst_76_ = v___x_124_;
v_snd_77_ = v___x_128_;
goto v___jp_75_;
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_130_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_joinQueued___closed__0));
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_idle_117_);
v___x_132_ = 0;
v___x_133_ = lean_box(0);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 4, v___x_73_);
lean_ctor_set(v___x_119_, 3, v___x_133_);
v___x_135_ = v___x_119_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_queued_112_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_queuedBytes_113_);
lean_ctor_set(v_reuseFailAlloc_136_, 2, v_error_116_);
lean_ctor_set(v_reuseFailAlloc_136_, 3, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_136_, 4, v___x_73_);
lean_ctor_set_uint8(v_reuseFailAlloc_136_, sizeof(void*)*5 + 1, v_failed_115_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*5, v___x_132_);
v_fst_76_ = v___x_131_;
v_snd_77_ = v___x_135_;
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
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___lam__0___boxed(lean_object* v_inst_139_, lean_object* v_outbox_140_, lean_object* v_state_141_, lean_object* v_result_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___lam__0(v_inst_139_, v_outbox_140_, v_state_141_, v_result_142_);
lean_dec(v_state_141_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg(lean_object* v_inst_145_, lean_object* v_outbox_146_, lean_object* v_data_147_){
_start:
{
lean_object* v_sendAll_149_; lean_object* v_socket_150_; lean_object* v_state_151_; lean_object* v___f_152_; lean_object* v_val_154_; lean_object* v___x_158_; 
v_sendAll_149_ = lean_ctor_get(v_inst_145_, 1);
lean_inc_ref(v_sendAll_149_);
v_socket_150_ = lean_ctor_get(v_outbox_146_, 0);
lean_inc(v_socket_150_);
v_state_151_ = lean_ctor_get(v_outbox_146_, 2);
lean_inc(v_state_151_);
v___f_152_ = lean_alloc_closure((void*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_152_, 0, v_inst_145_);
lean_closure_set(v___f_152_, 1, v_outbox_146_);
lean_closure_set(v___f_152_, 2, v_state_151_);
v___x_158_ = lean_apply_3(v_sendAll_149_, v_socket_150_, v_data_147_, lean_box(0));
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
v___x_160_ = lean_task_pure(v_a_159_);
v_val_154_ = v___x_160_;
goto v___jp_153_;
}
else
{
lean_object* v_a_161_; 
v_a_161_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_a_161_);
lean_dec_ref_known(v___x_158_, 1);
v_val_154_ = v_a_161_;
goto v___jp_153_;
}
v___jp_153_:
{
lean_object* v___x_155_; uint8_t v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = 1;
v___x_157_ = l_BaseIO_chainTask___redArg(v_val_154_, v___f_152_, v___x_155_, v___x_156_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg___boxed(lean_object* v_inst_162_, lean_object* v_outbox_163_, lean_object* v_data_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg(v_inst_162_, v_outbox_163_, v_data_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write(lean_object* v_00_u03b1_167_, lean_object* v_inst_168_, lean_object* v_outbox_169_, lean_object* v_data_170_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg(v_inst_168_, v_outbox_169_, v_data_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___boxed(lean_object* v_00_u03b1_173_, lean_object* v_inst_174_, lean_object* v_outbox_175_, lean_object* v_data_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write(v_00_u03b1_173_, v_inst_174_, v_outbox_175_, v_data_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send___redArg(lean_object* v_inst_185_, lean_object* v_outbox_186_, lean_object* v_buffer_187_){
_start:
{
lean_object* v_data_189_; lean_object* v_size_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_256_; 
v_data_189_ = lean_ctor_get(v_buffer_187_, 0);
v_size_190_ = lean_ctor_get(v_buffer_187_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_buffer_187_);
if (v_isSharedCheck_256_ == 0)
{
v___x_192_ = v_buffer_187_;
v_isShared_193_ = v_isSharedCheck_256_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_size_190_);
lean_inc(v_data_189_);
lean_dec(v_buffer_187_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_256_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_nat_dec_eq(v_size_190_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; lean_object* v_state_197_; lean_object* v___x_198_; lean_object* v_fst_200_; lean_object* v_snd_201_; uint8_t v_failed_211_; 
v___x_196_ = lean_io_mono_ms_now();
v_state_197_ = lean_ctor_get(v_outbox_186_, 2);
lean_inc(v_state_197_);
v___x_198_ = lean_st_ref_take(v_state_197_);
v_failed_211_ = lean_ctor_get_uint8(v___x_198_, sizeof(void*)*5 + 1);
if (v_failed_211_ == 0)
{
uint8_t v_writing_212_; 
v_writing_212_ = lean_ctor_get_uint8(v___x_198_, sizeof(void*)*5);
if (v_writing_212_ == 0)
{
lean_object* v_queued_213_; lean_object* v_queuedBytes_214_; lean_object* v_error_215_; lean_object* v_idle_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_225_; 
lean_del_object(v___x_192_);
lean_dec(v_size_190_);
v_queued_213_ = lean_ctor_get(v___x_198_, 0);
v_queuedBytes_214_ = lean_ctor_get(v___x_198_, 1);
v_error_215_ = lean_ctor_get(v___x_198_, 2);
v_idle_216_ = lean_ctor_get(v___x_198_, 3);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; 
v_unused_226_ = lean_ctor_get(v___x_198_, 4);
lean_dec(v_unused_226_);
v___x_218_ = v___x_198_;
v_isShared_219_ = v_isSharedCheck_225_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_idle_216_);
lean_inc(v_error_215_);
lean_inc(v_queuedBytes_214_);
lean_inc(v_queued_213_);
lean_dec(v___x_198_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_225_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_220_ = 1;
v___x_221_ = ((lean_object*)(l_Std_Http_Internal_Outbox_send___redArg___closed__1));
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 4, v___x_196_);
v___x_223_ = v___x_218_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_queued_213_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_queuedBytes_214_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_error_215_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v_idle_216_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v___x_196_);
lean_ctor_set_uint8(v_reuseFailAlloc_224_, sizeof(void*)*5 + 1, v_failed_211_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*5, v___x_220_);
v_fst_200_ = v___x_221_;
v_snd_201_ = v___x_223_;
goto v___jp_199_;
}
}
}
else
{
lean_object* v_queued_227_; lean_object* v_queuedBytes_228_; lean_object* v_error_229_; lean_object* v_idle_230_; lean_object* v_progressAt_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_245_; 
lean_dec(v___x_196_);
v_queued_227_ = lean_ctor_get(v___x_198_, 0);
v_queuedBytes_228_ = lean_ctor_get(v___x_198_, 1);
v_error_229_ = lean_ctor_get(v___x_198_, 2);
v_idle_230_ = lean_ctor_get(v___x_198_, 3);
v_progressAt_231_ = lean_ctor_get(v___x_198_, 4);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_245_ == 0)
{
v___x_233_ = v___x_198_;
v_isShared_234_ = v_isSharedCheck_245_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_progressAt_231_);
lean_inc(v_idle_230_);
lean_inc(v_error_229_);
lean_inc(v_queuedBytes_228_);
lean_inc(v_queued_227_);
lean_dec(v___x_198_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_245_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
v___x_235_ = lean_nat_add(v_queuedBytes_228_, v_size_190_);
lean_dec(v_size_190_);
lean_dec(v_queuedBytes_228_);
lean_inc(v___x_235_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
v___x_237_ = lean_box(v_failed_211_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_236_);
lean_ctor_set(v___x_192_, 0, v___x_237_);
v___x_239_ = v___x_192_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_236_);
v___x_239_ = v_reuseFailAlloc_244_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
lean_inc_ref(v_data_189_);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v_data_189_);
lean_ctor_set(v___x_240_, 1, v_queued_227_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v___x_235_);
lean_ctor_set(v___x_233_, 0, v___x_240_);
v___x_242_ = v___x_233_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_235_);
lean_ctor_set(v_reuseFailAlloc_243_, 2, v_error_229_);
lean_ctor_set(v_reuseFailAlloc_243_, 3, v_idle_230_);
lean_ctor_set(v_reuseFailAlloc_243_, 4, v_progressAt_231_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*5, v_writing_212_);
lean_ctor_set_uint8(v_reuseFailAlloc_243_, sizeof(void*)*5 + 1, v_failed_211_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
v_fst_200_ = v___x_239_;
v_snd_201_ = v___x_242_;
goto v___jp_199_;
}
}
}
}
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
lean_dec(v___x_196_);
lean_dec(v_size_190_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_box(v___x_195_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_246_);
lean_ctor_set(v___x_192_, 0, v___x_247_);
v___x_249_ = v___x_192_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_246_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
v_fst_200_ = v___x_249_;
v_snd_201_ = v___x_198_;
goto v___jp_199_;
}
}
v___jp_199_:
{
lean_object* v___x_202_; lean_object* v_fst_203_; uint8_t v___x_204_; 
v___x_202_ = lean_st_ref_put(v_state_197_, v_snd_201_);
v_fst_203_ = lean_ctor_get(v_fst_200_, 0);
v___x_204_ = lean_unbox(v_fst_203_);
if (v___x_204_ == 0)
{
lean_object* v_snd_205_; 
lean_dec(v_state_197_);
lean_dec_ref(v_data_189_);
lean_dec_ref(v_outbox_186_);
lean_dec_ref(v_inst_185_);
v_snd_205_ = lean_ctor_get(v_fst_200_, 1);
lean_inc(v_snd_205_);
lean_dec_ref(v_fst_200_);
return v_snd_205_;
}
else
{
lean_object* v_snd_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v_failed_209_; 
v_snd_206_ = lean_ctor_get(v_fst_200_, 1);
lean_inc(v_snd_206_);
lean_dec_ref(v_fst_200_);
v___x_207_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_write___redArg(v_inst_185_, v_outbox_186_, v_data_189_);
v___x_208_ = lean_st_ref_get(v_state_197_);
lean_dec(v_state_197_);
v_failed_209_ = lean_ctor_get_uint8(v___x_208_, sizeof(void*)*5 + 1);
lean_dec(v___x_208_);
if (v_failed_209_ == 0)
{
return v_snd_206_;
}
else
{
lean_object* v___x_210_; 
lean_dec(v_snd_206_);
v___x_210_ = lean_box(0);
return v___x_210_;
}
}
}
}
else
{
lean_object* v_state_251_; lean_object* v___x_252_; uint8_t v_failed_253_; 
lean_del_object(v___x_192_);
lean_dec(v_size_190_);
lean_dec_ref(v_data_189_);
lean_dec_ref(v_inst_185_);
v_state_251_ = lean_ctor_get(v_outbox_186_, 2);
lean_inc(v_state_251_);
lean_dec_ref(v_outbox_186_);
v___x_252_ = lean_st_ref_get(v_state_251_);
lean_dec(v_state_251_);
v_failed_253_ = lean_ctor_get_uint8(v___x_252_, sizeof(void*)*5 + 1);
lean_dec(v___x_252_);
if (v_failed_253_ == 0)
{
lean_object* v___x_254_; 
v___x_254_ = ((lean_object*)(l_Std_Http_Internal_Outbox_send___redArg___closed__0));
return v___x_254_;
}
else
{
lean_object* v___x_255_; 
v___x_255_ = lean_box(0);
return v___x_255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send___redArg___boxed(lean_object* v_inst_257_, lean_object* v_outbox_258_, lean_object* v_buffer_259_, lean_object* v_a_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Std_Http_Internal_Outbox_send___redArg(v_inst_257_, v_outbox_258_, v_buffer_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send(lean_object* v_00_u03b1_262_, lean_object* v_inst_263_, lean_object* v_outbox_264_, lean_object* v_buffer_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_Http_Internal_Outbox_send___redArg(v_inst_263_, v_outbox_264_, v_buffer_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_send___boxed(lean_object* v_00_u03b1_268_, lean_object* v_inst_269_, lean_object* v_outbox_270_, lean_object* v_buffer_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Http_Internal_Outbox_send(v_00_u03b1_268_, v_inst_269_, v_outbox_270_, v_buffer_271_);
return v_res_273_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_writing___redArg(lean_object* v_outbox_274_){
_start:
{
lean_object* v_state_276_; lean_object* v___x_277_; uint8_t v_writing_278_; 
v_state_276_ = lean_ctor_get(v_outbox_274_, 2);
v___x_277_ = lean_st_ref_get(v_state_276_);
v_writing_278_ = lean_ctor_get_uint8(v___x_277_, sizeof(void*)*5);
lean_dec(v___x_277_);
return v_writing_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writing___redArg___boxed(lean_object* v_outbox_279_, lean_object* v_a_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Std_Http_Internal_Outbox_writing___redArg(v_outbox_279_);
lean_dec_ref(v_outbox_279_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_writing(lean_object* v_00_u03b1_283_, lean_object* v_outbox_284_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = l_Std_Http_Internal_Outbox_writing___redArg(v_outbox_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writing___boxed(lean_object* v_00_u03b1_287_, lean_object* v_outbox_288_, lean_object* v_a_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Std_Http_Internal_Outbox_writing(v_00_u03b1_287_, v_outbox_288_);
lean_dec_ref(v_outbox_288_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f___redArg(lean_object* v_outbox_292_){
_start:
{
lean_object* v_state_294_; lean_object* v___x_295_; uint8_t v_writing_298_; 
v_state_294_ = lean_ctor_get(v_outbox_292_, 2);
v___x_295_ = lean_st_ref_get(v_state_294_);
v_writing_298_ = lean_ctor_get_uint8(v___x_295_, sizeof(void*)*5);
if (v_writing_298_ == 0)
{
lean_dec(v___x_295_);
goto v___jp_296_;
}
else
{
uint8_t v_failed_299_; 
v_failed_299_ = lean_ctor_get_uint8(v___x_295_, sizeof(void*)*5 + 1);
lean_dec(v___x_295_);
if (v_failed_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v_fst_303_; lean_object* v_snd_304_; uint8_t v_writing_308_; 
v___x_300_ = lean_io_promise_new();
v___x_301_ = lean_st_ref_take(v_state_294_);
v_writing_308_ = lean_ctor_get_uint8(v___x_301_, sizeof(void*)*5);
if (v_writing_308_ == 0)
{
lean_dec(v___x_300_);
goto v___jp_306_;
}
else
{
uint8_t v_failed_309_; 
v_failed_309_ = lean_ctor_get_uint8(v___x_301_, sizeof(void*)*5 + 1);
if (v_failed_309_ == 0)
{
lean_object* v_idle_310_; 
v_idle_310_ = lean_ctor_get(v___x_301_, 3);
lean_inc(v_idle_310_);
if (lean_obj_tag(v_idle_310_) == 0)
{
lean_object* v_queued_311_; lean_object* v_queuedBytes_312_; lean_object* v_error_313_; lean_object* v_progressAt_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_324_; 
v_queued_311_ = lean_ctor_get(v___x_301_, 0);
v_queuedBytes_312_ = lean_ctor_get(v___x_301_, 1);
v_error_313_ = lean_ctor_get(v___x_301_, 2);
v_progressAt_314_ = lean_ctor_get(v___x_301_, 4);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_324_ == 0)
{
lean_object* v_unused_325_; 
v_unused_325_ = lean_ctor_get(v___x_301_, 3);
lean_dec(v_unused_325_);
v___x_316_ = v___x_301_;
v_isShared_317_ = v_isSharedCheck_324_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_progressAt_314_);
lean_inc(v_error_313_);
lean_inc(v_queuedBytes_312_);
lean_inc(v_queued_311_);
lean_dec(v___x_301_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_324_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_318_ = lean_io_promise_result_opt(v___x_300_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_300_);
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 3, v___x_320_);
v___x_322_ = v___x_316_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_queued_311_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_queuedBytes_312_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_error_313_);
lean_ctor_set(v_reuseFailAlloc_323_, 3, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_323_, 4, v_progressAt_314_);
lean_ctor_set_uint8(v_reuseFailAlloc_323_, sizeof(void*)*5, v_writing_308_);
lean_ctor_set_uint8(v_reuseFailAlloc_323_, sizeof(void*)*5 + 1, v_failed_309_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
v_fst_303_ = v___x_319_;
v_snd_304_ = v___x_322_;
goto v___jp_302_;
}
}
}
else
{
lean_object* v_val_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
lean_dec(v___x_300_);
v_val_326_ = lean_ctor_get(v_idle_310_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_idle_310_);
if (v_isSharedCheck_334_ == 0)
{
v___x_328_ = v_idle_310_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_val_326_);
lean_dec(v_idle_310_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = lean_io_promise_result_opt(v_val_326_);
lean_dec(v_val_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
v_fst_303_ = v___x_332_;
v_snd_304_ = v___x_301_;
goto v___jp_302_;
}
}
}
}
else
{
lean_dec(v___x_300_);
goto v___jp_306_;
}
}
v___jp_302_:
{
lean_object* v___x_305_; 
v___x_305_ = lean_st_ref_put(v_state_294_, v_snd_304_);
return v_fst_303_;
}
v___jp_306_:
{
lean_object* v___x_307_; 
v___x_307_ = lean_box(0);
v_fst_303_ = v___x_307_;
v_snd_304_ = v___x_301_;
goto v___jp_302_;
}
}
else
{
goto v___jp_296_;
}
}
v___jp_296_:
{
lean_object* v___x_297_; 
v___x_297_ = lean_box(0);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f___redArg___boxed(lean_object* v_outbox_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_Http_Internal_Outbox_idle_x3f___redArg(v_outbox_335_);
lean_dec_ref(v_outbox_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f(lean_object* v_00_u03b1_338_, lean_object* v_outbox_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Std_Http_Internal_Outbox_idle_x3f___redArg(v_outbox_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_idle_x3f___boxed(lean_object* v_00_u03b1_342_, lean_object* v_outbox_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Http_Internal_Outbox_idle_x3f(v_00_u03b1_342_, v_outbox_343_);
lean_dec_ref(v_outbox_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg(lean_object* v_outbox_348_){
_start:
{
lean_object* v_writeTimeout_350_; lean_object* v_state_351_; lean_object* v___x_352_; uint8_t v_failed_353_; 
v_writeTimeout_350_ = lean_ctor_get(v_outbox_348_, 1);
lean_inc(v_writeTimeout_350_);
v_state_351_ = lean_ctor_get(v_outbox_348_, 2);
lean_inc(v_state_351_);
lean_dec_ref(v_outbox_348_);
v___x_352_ = lean_st_ref_take(v_state_351_);
v_failed_353_ = lean_ctor_get_uint8(v___x_352_, sizeof(void*)*5 + 1);
if (v_failed_353_ == 0)
{
uint8_t v_writing_354_; lean_object* v_idle_355_; lean_object* v_progressAt_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_374_; 
v_writing_354_ = lean_ctor_get_uint8(v___x_352_, sizeof(void*)*5);
v_idle_355_ = lean_ctor_get(v___x_352_, 3);
v_progressAt_356_ = lean_ctor_get(v___x_352_, 4);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_374_ == 0)
{
lean_object* v_unused_375_; lean_object* v_unused_376_; lean_object* v_unused_377_; 
v_unused_375_ = lean_ctor_get(v___x_352_, 2);
lean_dec(v_unused_375_);
v_unused_376_ = lean_ctor_get(v___x_352_, 1);
lean_dec(v_unused_376_);
v_unused_377_ = lean_ctor_get(v___x_352_, 0);
lean_dec(v_unused_377_);
v___x_358_ = v___x_352_;
v_isShared_359_ = v_isSharedCheck_374_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_progressAt_356_);
lean_inc(v_idle_355_);
lean_dec(v___x_352_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_374_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_360_ = 1;
v___x_361_ = lean_box(0);
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___closed__0));
v___x_364_ = l_Nat_reprFast(v_writeTimeout_350_);
v___x_365_ = lean_string_append(v___x_363_, v___x_364_);
lean_dec_ref(v___x_364_);
v___x_366_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___closed__1));
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
v___x_368_ = lean_mk_io_user_error(v___x_367_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 2, v___x_369_);
lean_ctor_set(v___x_358_, 1, v___x_362_);
lean_ctor_set(v___x_358_, 0, v___x_361_);
v___x_371_ = v___x_358_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_idle_355_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v_progressAt_356_);
lean_ctor_set_uint8(v_reuseFailAlloc_373_, sizeof(void*)*5, v_writing_354_);
v___x_371_ = v_reuseFailAlloc_373_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; 
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*5 + 1, v___x_360_);
v___x_372_ = lean_st_ref_put(v_state_351_, v___x_371_);
lean_dec(v_state_351_);
return v___x_372_;
}
}
}
else
{
lean_object* v___x_378_; 
lean_dec(v_writeTimeout_350_);
v___x_378_ = lean_st_ref_put(v_state_351_, v___x_352_);
lean_dec(v_state_351_);
return v___x_378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg___boxed(lean_object* v_outbox_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg(v_outbox_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire(lean_object* v_00_u03b1_382_, lean_object* v_outbox_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg(v_outbox_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___boxed(lean_object* v_00_u03b1_386_, lean_object* v_outbox_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire(v_00_u03b1_386_, v_outbox_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0(lean_object* v_w_392_, lean_object* v_lose_393_){
_start:
{
lean_object* v_finished_395_; lean_object* v_promise_396_; lean_object* v___x_397_; uint8_t v___y_399_; uint8_t v___x_406_; 
v_finished_395_ = lean_ctor_get(v_w_392_, 0);
v_promise_396_ = lean_ctor_get(v_w_392_, 1);
v___x_397_ = lean_st_ref_take(v_finished_395_);
v___x_406_ = lean_unbox(v___x_397_);
lean_dec(v___x_397_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
v___x_407_ = 1;
v___y_399_ = v___x_407_;
goto v___jp_398_;
}
else
{
uint8_t v___x_408_; 
v___x_408_ = 0;
v___y_399_ = v___x_408_;
goto v___jp_398_;
}
v___jp_398_:
{
uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = 1;
v___x_401_ = lean_box(v___x_400_);
v___x_402_ = lean_st_ref_put(v_finished_395_, v___x_401_);
if (v___y_399_ == 0)
{
lean_object* v___x_403_; 
v___x_403_ = lean_apply_1(v_lose_393_, lean_box(0));
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec_ref(v_lose_393_);
v___x_404_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0___closed__0));
v___x_405_ = lean_io_promise_resolve(v___x_404_, v_promise_396_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0___boxed(lean_object* v_w_409_, lean_object* v_lose_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0(v_w_409_, v_lose_410_);
lean_dec_ref(v_w_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0(lean_object* v_x_423_){
_start:
{
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_433_; 
v_a_425_ = lean_ctor_get(v_x_423_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_x_423_);
if (v_isSharedCheck_433_ == 0)
{
v___x_427_ = v_x_423_;
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v_x_423_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_433_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_432_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
return v___x_431_;
}
}
}
else
{
lean_object* v_a_434_; uint8_t v___x_435_; 
v_a_434_ = lean_ctor_get(v_x_423_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v_x_423_, 1);
v___x_435_ = lean_unbox(v_a_434_);
lean_dec(v_a_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
v___x_436_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__1));
return v___x_436_;
}
else
{
lean_object* v___x_437_; 
v___x_437_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___closed__4));
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0___boxed(lean_object* v_x_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__0(v_x_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__1(lean_object* v___f_441_, lean_object* v_task_442_){
_start:
{
lean_object* v___x_444_; uint8_t v___x_445_; uint8_t v_a_447_; uint8_t v___x_452_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = 0;
v___x_452_ = lean_io_get_task_state(v_task_442_);
if (v___x_452_ == 2)
{
uint8_t v___x_453_; 
v___x_453_ = 1;
v_a_447_ = v___x_453_;
goto v___jp_446_;
}
else
{
v_a_447_ = v___x_445_;
goto v___jp_446_;
}
v___jp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_448_ = lean_box(v_a_447_);
v___x_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
v___x_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
v___x_451_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_444_, v___x_445_, v___x_450_, v___f_441_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__1___boxed(lean_object* v___f_454_, lean_object* v_task_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__1(v___f_454_, v_task_455_);
lean_dec_ref(v_task_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__2(lean_object* v___x_458_){
_start:
{
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__2___boxed(lean_object* v___x_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__2(v___x_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3(lean_object* v_waiter_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; 
v___f_468_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3___closed__0));
v___x_469_ = l_Std_Async_Waiter_race___at___00__private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector_spec__0(v_waiter_465_, v___f_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3___boxed(lean_object* v_waiter_470_, lean_object* v_x_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3(v_waiter_470_, v_x_471_);
lean_dec(v_x_471_);
lean_dec_ref(v_waiter_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__4(lean_object* v_task_474_, lean_object* v_waiter_475_){
_start:
{
lean_object* v___f_477_; lean_object* v___x_478_; uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___f_477_ = lean_alloc_closure((void*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_477_, 0, v_waiter_475_);
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = 1;
v___x_480_ = l_BaseIO_chainTask___redArg(v_task_474_, v___f_477_, v___x_478_, v___x_479_);
v___x_481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
v___x_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__4___boxed(lean_object* v_task_483_, lean_object* v_waiter_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__4(v_task_483_, v_waiter_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__5(lean_object* v___x_487_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
v___x_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__5___boxed(lean_object* v___x_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__5(v___x_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector(lean_object* v_task_497_){
_start:
{
lean_object* v___f_498_; lean_object* v___f_499_; lean_object* v___f_500_; lean_object* v___f_501_; lean_object* v___x_502_; 
v___f_498_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___closed__0));
lean_inc_ref(v_task_497_);
v___f_499_ = lean_alloc_closure((void*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__1___boxed), 3, 2);
lean_closure_set(v___f_499_, 0, v___f_498_);
lean_closure_set(v___f_499_, 1, v_task_497_);
v___f_500_ = lean_alloc_closure((void*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_500_, 0, v_task_497_);
v___f_501_ = ((lean_object*)(l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector___closed__1));
v___x_502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_502_, 0, v___f_499_);
lean_ctor_set(v___x_502_, 1, v___f_500_);
lean_ctor_set(v___x_502_, 2, v___f_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Internal_Outbox_awaitIdle_spec__1(lean_object* v_a_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_nat_to_int(v_a_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0(lean_object* v_x_507_){
_start:
{
if (lean_obj_tag(v_x_507_) == 0)
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_x_507_);
return v___x_509_;
}
else
{
lean_object* v___x_510_; 
lean_dec_ref_known(v_x_507_, 1);
v___x_510_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___closed__0));
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___boxed(lean_object* v_x_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0(v_x_511_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2(lean_object* v_x_519_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___closed__1));
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2___boxed(lean_object* v_x_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__2(v_x_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__4(lean_object* v_val_525_, lean_object* v___f_526_, lean_object* v___f_527_, uint8_t v___x_528_, lean_object* v___f_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_530_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v___f_529_);
lean_dec_ref(v___f_527_);
lean_dec_ref(v___f_526_);
lean_dec_ref(v_val_525_);
v_a_532_ = lean_ctor_get(v_x_530_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v_x_530_);
if (v_isSharedCheck_540_ == 0)
{
v___x_534_ = v_x_530_;
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v_x_530_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_540_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_a_541_ = lean_ctor_get(v_x_530_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v_x_530_, 1);
v___x_542_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_taskSelector(v_val_525_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
lean_ctor_set(v___x_543_, 1, v___f_526_);
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v_a_541_);
lean_ctor_set(v___x_544_, 1, v___f_527_);
v___x_545_ = lean_unsigned_to_nat(2u);
v___x_546_ = lean_mk_empty_array_with_capacity(v___x_545_);
v___x_547_ = lean_array_push(v___x_546_, v___x_543_);
v___x_548_ = lean_array_push(v___x_547_, v___x_544_);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = l_Std_Async_Selectable_one___redArg(v___x_548_);
v___x_551_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_549_, v___x_528_, v___x_550_, v___f_529_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__4___boxed(lean_object* v_val_552_, lean_object* v___f_553_, lean_object* v___f_554_, lean_object* v___x_555_, lean_object* v___f_556_, lean_object* v_x_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___x_2059__boxed_559_; lean_object* v_res_560_; 
v___x_2059__boxed_559_ = lean_unbox(v___x_555_);
v_res_560_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__4(v_val_552_, v___f_553_, v___f_554_, v___x_2059__boxed_559_, v___f_556_, v_x_557_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__3(uint8_t v___x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_box(v___x_561_);
v___x_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__3___boxed(lean_object* v___x_567_, lean_object* v_x_568_, lean_object* v___y_569_){
_start:
{
uint8_t v___x_2117__boxed_570_; lean_object* v_res_571_; 
v___x_2117__boxed_570_ = lean_unbox(v___x_567_);
v_res_571_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__3(v___x_2117__boxed_570_, v_x_568_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__5(lean_object* v___x_572_, lean_object* v_val_573_, lean_object* v___f_574_, lean_object* v___f_575_, lean_object* v_outbox_576_, lean_object* v___f_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_578_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v___f_577_);
lean_dec_ref(v_outbox_576_);
lean_dec_ref(v___f_575_);
lean_dec_ref(v___f_574_);
lean_dec_ref(v_val_573_);
v_a_580_ = lean_ctor_get(v_x_578_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_588_ == 0)
{
v___x_582_ = v_x_578_;
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v_x_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_588_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_587_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; 
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
return v___x_586_;
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_611_; 
v_a_589_ = lean_ctor_get(v_x_578_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_578_);
if (v_isSharedCheck_611_ == 0)
{
v___x_591_ = v_x_578_;
v_isShared_592_ = v_isSharedCheck_611_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v_x_578_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_611_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
uint8_t v___x_593_; 
v___x_593_ = lean_nat_dec_le(v___x_572_, v_a_589_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___f_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
lean_del_object(v___x_591_);
lean_dec_ref(v___f_577_);
lean_dec_ref(v_outbox_576_);
v___x_594_ = lean_box(v___x_593_);
v___f_595_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__3___boxed), 3, 1);
lean_closure_set(v___f_595_, 0, v___x_594_);
v___x_596_ = lean_box(v___x_593_);
v___f_597_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__4___boxed), 7, 5);
lean_closure_set(v___f_597_, 0, v_val_573_);
lean_closure_set(v___f_597_, 1, v___f_574_);
lean_closure_set(v___f_597_, 2, v___f_595_);
lean_closure_set(v___f_597_, 3, v___x_596_);
lean_closure_set(v___f_597_, 4, v___f_575_);
v___x_598_ = lean_nat_sub(v___x_572_, v_a_589_);
lean_dec(v_a_589_);
v___x_599_ = lean_nat_to_int(v___x_598_);
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = l_Std_Async_Selector_sleep(v___x_599_);
lean_dec(v___x_599_);
v___x_602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_600_, v___x_593_, v___x_601_, v___f_597_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec(v_a_589_);
lean_dec_ref(v___f_575_);
lean_dec_ref(v___f_574_);
lean_dec_ref(v_val_573_);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = 0;
v___x_605_ = l___private_Std_Http_Transport_Outbox_0__Std_Http_Internal_Outbox_expire___redArg(v_outbox_576_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 0, v___x_605_);
v___x_607_ = v___x_591_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_610_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
v___x_609_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_603_, v___x_604_, v___x_608_, v___f_577_);
return v___x_609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__5___boxed(lean_object* v___x_612_, lean_object* v_val_613_, lean_object* v___f_614_, lean_object* v___f_615_, lean_object* v_outbox_616_, lean_object* v___f_617_, lean_object* v_x_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__5(v___x_612_, v_val_613_, v___f_614_, v___f_615_, v_outbox_616_, v___f_617_, v_x_618_);
lean_dec(v___x_612_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__6(lean_object* v_writeTimeout_621_, lean_object* v_val_622_, lean_object* v___f_623_, lean_object* v___f_624_, lean_object* v_outbox_625_, lean_object* v___f_626_, lean_object* v_x_627_){
_start:
{
if (lean_obj_tag(v_x_627_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
lean_dec_ref(v___f_626_);
lean_dec_ref(v_outbox_625_);
lean_dec_ref(v___f_624_);
lean_dec_ref(v___f_623_);
lean_dec_ref(v_val_622_);
v_a_629_ = lean_ctor_get(v_x_627_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v_x_627_);
if (v_isSharedCheck_637_ == 0)
{
v___x_631_ = v_x_627_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v_x_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_636_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; 
v___x_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
return v___x_635_;
}
}
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_653_; 
v_a_638_ = lean_ctor_get(v_x_627_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v_x_627_);
if (v_isSharedCheck_653_ == 0)
{
v___x_640_ = v_x_627_;
v_isShared_641_ = v_isSharedCheck_653_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v_x_627_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_653_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_progressAt_642_; lean_object* v___x_643_; lean_object* v___f_644_; lean_object* v___x_645_; uint8_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v_progressAt_642_ = lean_ctor_get(v_a_638_, 4);
lean_inc(v_progressAt_642_);
lean_dec(v_a_638_);
v___x_643_ = lean_nat_add(v_progressAt_642_, v_writeTimeout_621_);
lean_dec(v_progressAt_642_);
v___f_644_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__5___boxed), 8, 6);
lean_closure_set(v___f_644_, 0, v___x_643_);
lean_closure_set(v___f_644_, 1, v_val_622_);
lean_closure_set(v___f_644_, 2, v___f_623_);
lean_closure_set(v___f_644_, 3, v___f_624_);
lean_closure_set(v___f_644_, 4, v_outbox_625_);
lean_closure_set(v___f_644_, 5, v___f_626_);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = 0;
v___x_647_ = lean_io_mono_ms_now();
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_647_);
v___x_649_ = v___x_640_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_652_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_645_, v___x_646_, v___x_650_, v___f_644_);
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__6___boxed(lean_object* v_writeTimeout_654_, lean_object* v_val_655_, lean_object* v___f_656_, lean_object* v___f_657_, lean_object* v_outbox_658_, lean_object* v___f_659_, lean_object* v_x_660_, lean_object* v___y_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__6(v_writeTimeout_654_, v_val_655_, v___f_656_, v___f_657_, v_outbox_658_, v___f_659_, v_x_660_);
lean_dec(v_writeTimeout_654_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__7(lean_object* v_outbox_663_, lean_object* v___f_664_, lean_object* v___f_665_, lean_object* v___f_666_, lean_object* v_x_667_){
_start:
{
if (lean_obj_tag(v_x_667_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v___f_666_);
lean_dec_ref(v___f_665_);
lean_dec_ref(v___f_664_);
lean_dec_ref(v_outbox_663_);
v_a_669_ = lean_ctor_get(v_x_667_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v_x_667_);
if (v_isSharedCheck_677_ == 0)
{
v___x_671_ = v_x_667_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v_x_667_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_676_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; 
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_701_; 
v_a_678_ = lean_ctor_get(v_x_667_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_x_667_);
if (v_isSharedCheck_701_ == 0)
{
v___x_680_ = v_x_667_;
v_isShared_681_ = v_isSharedCheck_701_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v_x_667_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_701_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
if (lean_obj_tag(v_a_678_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_699_; 
v_val_682_ = lean_ctor_get(v_a_678_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_699_ == 0)
{
v___x_684_ = v_a_678_;
v_isShared_685_ = v_isSharedCheck_699_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v_a_678_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_699_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_writeTimeout_686_; lean_object* v_state_687_; lean_object* v___f_688_; lean_object* v___x_689_; uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v_writeTimeout_686_ = lean_ctor_get(v_outbox_663_, 1);
lean_inc(v_writeTimeout_686_);
v_state_687_ = lean_ctor_get(v_outbox_663_, 2);
lean_inc(v_state_687_);
v___f_688_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__6___boxed), 8, 6);
lean_closure_set(v___f_688_, 0, v_writeTimeout_686_);
lean_closure_set(v___f_688_, 1, v_val_682_);
lean_closure_set(v___f_688_, 2, v___f_664_);
lean_closure_set(v___f_688_, 3, v___f_665_);
lean_closure_set(v___f_688_, 4, v_outbox_663_);
lean_closure_set(v___f_688_, 5, v___f_666_);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = 0;
v___x_691_ = lean_st_ref_get(v_state_687_);
lean_dec(v_state_687_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_691_);
v___x_693_ = v___x_680_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_698_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set_tag(v___x_684_, 0);
lean_ctor_set(v___x_684_, 0, v___x_693_);
v___x_695_ = v___x_684_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_697_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; 
v___x_696_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_689_, v___x_690_, v___x_695_, v___f_688_);
return v___x_696_;
}
}
}
}
else
{
lean_object* v___x_700_; 
lean_del_object(v___x_680_);
lean_dec(v_a_678_);
lean_dec_ref(v___f_666_);
lean_dec_ref(v___f_665_);
lean_dec_ref(v___f_664_);
lean_dec_ref(v_outbox_663_);
v___x_700_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___closed__0));
return v___x_700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__7___boxed(lean_object* v_outbox_702_, lean_object* v___f_703_, lean_object* v___f_704_, lean_object* v___f_705_, lean_object* v_x_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__7(v_outbox_702_, v___f_703_, v___f_704_, v___f_705_, v_x_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__1(lean_object* v_outbox_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_722_; 
lean_dec_ref(v_outbox_711_);
v_a_714_ = lean_ctor_get(v_x_712_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_712_);
if (v_isSharedCheck_722_ == 0)
{
v___x_716_ = v_x_712_;
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v_x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_721_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; 
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
}
else
{
lean_object* v_a_723_; uint8_t v___x_724_; 
v_a_723_ = lean_ctor_get(v_x_712_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v_x_712_, 1);
v___x_724_ = lean_unbox(v_a_723_);
lean_dec(v_a_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; 
v___x_725_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_outbox_711_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; 
lean_dec_ref(v_outbox_711_);
v___x_726_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__0___closed__0));
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__1___boxed(lean_object* v_outbox_727_, lean_object* v_x_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__1(v_outbox_727_, v_x_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg(lean_object* v_outbox_731_){
_start:
{
lean_object* v___f_733_; lean_object* v___f_734_; lean_object* v___f_735_; lean_object* v___f_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___f_733_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___closed__0));
lean_inc_ref_n(v_outbox_731_, 2);
v___f_734_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__1___boxed), 3, 1);
lean_closure_set(v___f_734_, 0, v_outbox_731_);
v___f_735_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___closed__1));
v___f_736_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitIdle___redArg___lam__7___boxed), 6, 4);
lean_closure_set(v___f_736_, 0, v_outbox_731_);
lean_closure_set(v___f_736_, 1, v___f_735_);
lean_closure_set(v___f_736_, 2, v___f_734_);
lean_closure_set(v___f_736_, 3, v___f_733_);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = 0;
v___x_739_ = l_Std_Http_Internal_Outbox_idle_x3f___redArg(v_outbox_731_);
lean_dec_ref(v_outbox_731_);
v___x_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
v___x_742_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_737_, v___x_738_, v___x_741_, v___f_736_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___redArg___boxed(lean_object* v_outbox_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_outbox_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle(lean_object* v_00_u03b1_746_, lean_object* v_outbox_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_outbox_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitIdle___boxed(lean_object* v_00_u03b1_750_, lean_object* v_outbox_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Std_Http_Internal_Outbox_awaitIdle(v_00_u03b1_750_, v_outbox_751_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Internal_Outbox_awaitIdle_spec__0(lean_object* v_a_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_nat_to_int(v_a_754_);
v___x_756_ = l_Rat_ofInt(v___x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writeDeadline_x3f___redArg(lean_object* v_outbox_757_){
_start:
{
lean_object* v_writeTimeout_759_; lean_object* v_state_760_; lean_object* v___x_761_; uint8_t v_writing_764_; 
v_writeTimeout_759_ = lean_ctor_get(v_outbox_757_, 1);
v_state_760_ = lean_ctor_get(v_outbox_757_, 2);
v___x_761_ = lean_st_ref_get(v_state_760_);
v_writing_764_ = lean_ctor_get_uint8(v___x_761_, sizeof(void*)*5);
if (v_writing_764_ == 0)
{
lean_dec(v___x_761_);
goto v___jp_762_;
}
else
{
uint8_t v_failed_765_; 
v_failed_765_ = lean_ctor_get_uint8(v___x_761_, sizeof(void*)*5 + 1);
if (v_failed_765_ == 0)
{
lean_object* v_progressAt_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_progressAt_766_ = lean_ctor_get(v___x_761_, 4);
lean_inc(v_progressAt_766_);
lean_dec(v___x_761_);
v___x_767_ = lean_nat_add(v_progressAt_766_, v_writeTimeout_759_);
lean_dec(v_progressAt_766_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
else
{
lean_dec(v___x_761_);
goto v___jp_762_;
}
}
v___jp_762_:
{
lean_object* v___x_763_; 
v___x_763_ = lean_box(0);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writeDeadline_x3f___redArg___boxed(lean_object* v_outbox_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_Http_Internal_Outbox_writeDeadline_x3f___redArg(v_outbox_769_);
lean_dec_ref(v_outbox_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writeDeadline_x3f(lean_object* v_00_u03b1_772_, lean_object* v_outbox_773_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Std_Http_Internal_Outbox_writeDeadline_x3f___redArg(v_outbox_773_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_writeDeadline_x3f___boxed(lean_object* v_00_u03b1_776_, lean_object* v_outbox_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_Http_Internal_Outbox_writeDeadline_x3f(v_00_u03b1_776_, v_outbox_777_);
lean_dec_ref(v_outbox_777_);
return v_res_779_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_failed___redArg(lean_object* v_outbox_780_){
_start:
{
lean_object* v_state_782_; lean_object* v___x_783_; uint8_t v_failed_784_; 
v_state_782_ = lean_ctor_get(v_outbox_780_, 2);
v___x_783_ = lean_st_ref_get(v_state_782_);
v_failed_784_ = lean_ctor_get_uint8(v___x_783_, sizeof(void*)*5 + 1);
lean_dec(v___x_783_);
return v_failed_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_failed___redArg___boxed(lean_object* v_outbox_785_, lean_object* v_a_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Std_Http_Internal_Outbox_failed___redArg(v_outbox_785_);
lean_dec_ref(v_outbox_785_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Internal_Outbox_failed(lean_object* v_00_u03b1_789_, lean_object* v_outbox_790_){
_start:
{
uint8_t v___x_792_; 
v___x_792_ = l_Std_Http_Internal_Outbox_failed___redArg(v_outbox_790_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_failed___boxed(lean_object* v_00_u03b1_793_, lean_object* v_outbox_794_, lean_object* v_a_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Std_Http_Internal_Outbox_failed(v_00_u03b1_793_, v_outbox_794_);
lean_dec_ref(v_outbox_794_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__0(lean_object* v_x_798_){
_start:
{
uint8_t v___y_801_; 
if (lean_obj_tag(v_x_798_) == 0)
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_x_798_);
return v___x_805_;
}
else
{
lean_object* v_a_806_; uint8_t v___x_807_; 
v_a_806_ = lean_ctor_get(v_x_798_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v_x_798_, 1);
v___x_807_ = lean_unbox(v_a_806_);
lean_dec(v_a_806_);
if (v___x_807_ == 0)
{
uint8_t v___x_808_; 
v___x_808_ = 1;
v___y_801_ = v___x_808_;
goto v___jp_800_;
}
else
{
uint8_t v___x_809_; 
v___x_809_ = 0;
v___y_801_ = v___x_809_;
goto v___jp_800_;
}
}
v___jp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = lean_box(v___y_801_);
v___x_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__0___boxed(lean_object* v_x_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__0(v_x_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__1(lean_object* v_outbox_813_, lean_object* v___f_814_, lean_object* v_x_815_){
_start:
{
if (lean_obj_tag(v_x_815_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_825_; 
lean_dec_ref(v___f_814_);
v_a_817_ = lean_ctor_get(v_x_815_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v_x_815_);
if (v_isSharedCheck_825_ == 0)
{
v___x_819_ = v_x_815_;
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v_x_815_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_825_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_824_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_object* v___x_823_; 
v___x_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
return v___x_823_;
}
}
}
else
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_838_; 
v_isSharedCheck_838_ = !lean_is_exclusive(v_x_815_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v_x_815_, 0);
lean_dec(v_unused_839_);
v___x_827_ = v_x_815_;
v_isShared_828_ = v_isSharedCheck_838_;
goto v_resetjp_826_;
}
else
{
lean_dec(v_x_815_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_838_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; uint8_t v___x_830_; uint8_t v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = 0;
v___x_831_ = l_Std_Http_Internal_Outbox_failed___redArg(v_outbox_813_);
v___x_832_ = lean_box(v___x_831_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_832_);
v___x_834_ = v___x_827_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_837_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
v___x_836_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_829_, v___x_830_, v___x_835_, v___f_814_);
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__1___boxed(lean_object* v_outbox_840_, lean_object* v___f_841_, lean_object* v_x_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__1(v_outbox_840_, v___f_841_, v_x_842_);
lean_dec_ref(v_outbox_840_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg(lean_object* v_outbox_846_){
_start:
{
lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___x_850_; uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___f_848_ = ((lean_object*)(l_Std_Http_Internal_Outbox_awaitWritten___redArg___closed__0));
lean_inc_ref(v_outbox_846_);
v___f_849_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_awaitWritten___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_849_, 0, v_outbox_846_);
lean_closure_set(v___f_849_, 1, v___f_848_);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = 0;
v___x_852_ = l_Std_Http_Internal_Outbox_awaitIdle___redArg(v_outbox_846_);
v___x_853_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_850_, v___x_851_, v___x_852_, v___f_849_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___redArg___boxed(lean_object* v_outbox_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg(v_outbox_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten(lean_object* v_00_u03b1_857_, lean_object* v_outbox_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg(v_outbox_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_awaitWritten___boxed(lean_object* v_00_u03b1_861_, lean_object* v_outbox_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_Http_Internal_Outbox_awaitWritten(v_00_u03b1_861_, v_outbox_862_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___redArg(lean_object* v_outbox_865_){
_start:
{
lean_object* v_state_867_; lean_object* v___x_868_; lean_object* v_queued_869_; lean_object* v_queuedBytes_870_; uint8_t v_writing_871_; uint8_t v_failed_872_; lean_object* v_error_873_; lean_object* v_idle_874_; lean_object* v_progressAt_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_884_; 
v_state_867_ = lean_ctor_get(v_outbox_865_, 2);
v___x_868_ = lean_st_ref_take(v_state_867_);
v_queued_869_ = lean_ctor_get(v___x_868_, 0);
v_queuedBytes_870_ = lean_ctor_get(v___x_868_, 1);
v_writing_871_ = lean_ctor_get_uint8(v___x_868_, sizeof(void*)*5);
v_failed_872_ = lean_ctor_get_uint8(v___x_868_, sizeof(void*)*5 + 1);
v_error_873_ = lean_ctor_get(v___x_868_, 2);
v_idle_874_ = lean_ctor_get(v___x_868_, 3);
v_progressAt_875_ = lean_ctor_get(v___x_868_, 4);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_884_ == 0)
{
v___x_877_ = v___x_868_;
v_isShared_878_ = v_isSharedCheck_884_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_progressAt_875_);
lean_inc(v_idle_874_);
lean_inc(v_error_873_);
lean_inc(v_queuedBytes_870_);
lean_inc(v_queued_869_);
lean_dec(v___x_868_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_884_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = lean_box(0);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 2, v___x_879_);
v___x_881_ = v___x_877_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_queued_869_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_queuedBytes_870_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v_idle_874_);
lean_ctor_set(v_reuseFailAlloc_883_, 4, v_progressAt_875_);
lean_ctor_set_uint8(v_reuseFailAlloc_883_, sizeof(void*)*5, v_writing_871_);
lean_ctor_set_uint8(v_reuseFailAlloc_883_, sizeof(void*)*5 + 1, v_failed_872_);
v___x_881_ = v_reuseFailAlloc_883_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; 
v___x_882_ = lean_st_ref_put(v_state_867_, v___x_881_);
return v_error_873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___redArg___boxed(lean_object* v_outbox_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Std_Http_Internal_Outbox_takeError_x3f___redArg(v_outbox_885_);
lean_dec_ref(v_outbox_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f(lean_object* v_00_u03b1_888_, lean_object* v_outbox_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Std_Http_Internal_Outbox_takeError_x3f___redArg(v_outbox_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_takeError_x3f___boxed(lean_object* v_00_u03b1_892_, lean_object* v_outbox_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_Http_Internal_Outbox_takeError_x3f(v_00_u03b1_892_, v_outbox_893_);
lean_dec_ref(v_outbox_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg___lam__0(lean_object* v_limit_901_, lean_object* v_outbox_902_, lean_object* v_x_903_){
_start:
{
if (lean_obj_tag(v_x_903_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_913_; 
lean_dec_ref(v_outbox_902_);
v_a_905_ = lean_ctor_get(v_x_903_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v_x_903_);
if (v_isSharedCheck_913_ == 0)
{
v___x_907_ = v_x_903_;
v_isShared_908_ = v_isSharedCheck_913_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v_x_903_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_913_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_912_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_933_; 
v_a_914_ = lean_ctor_get(v_x_903_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v_x_903_);
if (v_isSharedCheck_933_ == 0)
{
v___x_916_ = v_x_903_;
v_isShared_917_ = v_isSharedCheck_933_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v_x_903_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_933_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
if (lean_obj_tag(v_a_914_) == 0)
{
lean_object* v___x_918_; 
lean_del_object(v___x_916_);
lean_dec_ref(v_outbox_902_);
v___x_918_ = ((lean_object*)(l_Std_Http_Internal_Outbox_push___redArg___lam__0___closed__1));
return v___x_918_;
}
else
{
lean_object* v_val_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_932_; 
v_val_919_ = lean_ctor_get(v_a_914_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v_a_914_);
if (v_isSharedCheck_932_ == 0)
{
v___x_921_ = v_a_914_;
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_val_919_);
lean_dec(v_a_914_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_932_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
uint8_t v___x_923_; 
v___x_923_ = lean_nat_dec_le(v_val_919_, v_limit_901_);
lean_dec(v_val_919_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; 
lean_del_object(v___x_921_);
lean_del_object(v___x_916_);
v___x_924_ = l_Std_Http_Internal_Outbox_awaitWritten___redArg(v_outbox_902_);
return v___x_924_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_927_; 
lean_dec_ref(v_outbox_902_);
v___x_925_ = lean_box(v___x_923_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_925_);
v___x_927_ = v___x_916_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_931_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
lean_object* v___x_929_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 0);
lean_ctor_set(v___x_921_, 0, v___x_927_);
v___x_929_ = v___x_921_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg___lam__0___boxed(lean_object* v_limit_934_, lean_object* v_outbox_935_, lean_object* v_x_936_, lean_object* v___y_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Std_Http_Internal_Outbox_push___redArg___lam__0(v_limit_934_, v_outbox_935_, v_x_936_);
lean_dec(v_limit_934_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg(lean_object* v_inst_939_, lean_object* v_outbox_940_, lean_object* v_buffer_941_, lean_object* v_limit_942_){
_start:
{
lean_object* v___f_944_; lean_object* v___x_945_; uint8_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_inc_ref(v_outbox_940_);
v___f_944_ = lean_alloc_closure((void*)(l_Std_Http_Internal_Outbox_push___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_944_, 0, v_limit_942_);
lean_closure_set(v___f_944_, 1, v_outbox_940_);
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = 0;
v___x_947_ = l_Std_Http_Internal_Outbox_send___redArg(v_inst_939_, v_outbox_940_, v_buffer_941_);
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
v___x_950_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_945_, v___x_946_, v___x_949_, v___f_944_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___redArg___boxed(lean_object* v_inst_951_, lean_object* v_outbox_952_, lean_object* v_buffer_953_, lean_object* v_limit_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Std_Http_Internal_Outbox_push___redArg(v_inst_951_, v_outbox_952_, v_buffer_953_, v_limit_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push(lean_object* v_00_u03b1_957_, lean_object* v_inst_958_, lean_object* v_outbox_959_, lean_object* v_buffer_960_, lean_object* v_limit_961_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Std_Http_Internal_Outbox_push___redArg(v_inst_958_, v_outbox_959_, v_buffer_960_, v_limit_961_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_Outbox_push___boxed(lean_object* v_00_u03b1_964_, lean_object* v_inst_965_, lean_object* v_outbox_966_, lean_object* v_buffer_967_, lean_object* v_limit_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_Http_Internal_Outbox_push(v_00_u03b1_964_, v_inst_965_, v_outbox_966_, v_buffer_967_, v_limit_968_);
return v_res_970_;
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

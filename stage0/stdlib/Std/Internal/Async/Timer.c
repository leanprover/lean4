// Lean compiler output
// Module: Std.Internal.Async.Timer
// Imports: public import Std.Time public import Std.Internal.UV.Timer public import Std.Internal.Async.Select
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
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Sleep_mk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Sleep_mk___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Sleep_mk___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Sleep_mk___closed__0_value;
lean_object* l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_uv_timer_mk(uint64_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___boxed(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IO_Async_Sleep_wait___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Internal_IO_Async_Sleep_wait___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Sleep_wait___closed__0_value;
static const lean_closure_object l_Std_Internal_IO_Async_Sleep_wait___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Sleep_wait___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Sleep_wait___closed__0_value)} };
static const lean_object* l_Std_Internal_IO_Async_Sleep_wait___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Sleep_wait___closed__1_value;
lean_object* lean_uv_timer_next(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait___boxed(lean_object*, lean_object*);
lean_object* lean_uv_timer_reset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_reset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_reset___boxed(lean_object*, lean_object*);
lean_object* lean_uv_timer_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_stop___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0___closed__0_value;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__0_value)}};
static const lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_uv_timer_cancel(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Sleep_selector___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Sleep_selector___lam__2___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__3___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Sleep_selector___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__0_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__0_value)}};
static const lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__1_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__1_value)}};
static const lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2 = (const lean_object*)&l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Sleep_selector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Sleep_selector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Sleep_selector___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Sleep_selector___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_sleep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_sleep___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_sleep___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_sleep___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Internal_IO_Async_Selector_sleep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Internal_IO_Async_Selector_sleep___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Internal_IO_Async_Selector_sleep___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Selector_sleep___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0_value;
static const lean_string_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1_value;
static const lean_string_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2_value;
static const lean_string_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__3 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5_value;
static const lean_string_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__6 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__6_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7_value;
static const lean_string_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__8 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9_value;
static const lean_string_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13;
static const lean_string_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__14 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__14_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15_value_aux_0),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15_value_aux_1),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15_value_aux_2),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15_value;
static const lean_ctor_object l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9_value),((lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5_value)}};
static const lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__16 = (const lean_object*)&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__16_value;
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17;
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18;
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19;
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20;
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21;
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22;
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23;
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24;
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25;
static lean_once_cell_t l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___auto__1;
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_tick(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_tick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_reset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_reset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_stop___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_6 = x_9;
goto block_8;
}
block_8:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_1, 0);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
x_13 = x_1;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_15 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_mk___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_10; uint64_t x_11; uint8_t x_12; lean_object* x_13; 
x_3 = ((lean_object*)(l_Std_Internal_IO_Async_Sleep_mk___closed__0));
x_10 = l_Int_toNat(x_1);
x_11 = lean_uint64_of_nat(x_10);
lean_dec(x_10);
x_12 = 0;
x_13 = lean_uv_timer_mk(x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
x_15 = x_13;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
x_4 = x_17;
goto block_9;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
x_22 = lean_ctor_get(x_13, 0);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
x_23 = x_13;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
lean_ctor_set_tag(x_23, 0);
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
x_4 = x_25;
goto block_9;
}
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_mk___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_mk(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_mk_io_user_error(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_12; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_6 = x_2;
x_7 = x_12;
goto block_11;
}
else
{
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_8; 
if (x_7 == 0)
{
x_8 = x_6;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_5);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_next(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_16; 
x_4 = lean_ctor_get(x_3, 0);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
x_5 = x_3;
x_6 = x_16;
goto block_15;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = ((lean_object*)(l_Std_Internal_IO_Async_Sleep_wait___closed__1));
x_8 = lean_io_promise_result_opt(x_4);
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = lean_task_map(x_7, x_8, x_9, x_10);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_11);
x_12 = x_5;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_25; 
x_17 = lean_ctor_get(x_3, 0);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
x_18 = x_3;
x_19 = x_25;
goto block_24;
}
else
{
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_20; 
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
x_20 = x_18;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_17);
x_20 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_wait___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_wait(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_reset(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_6; 
x_6 = lean_uv_timer_reset(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_14; 
x_7 = lean_ctor_get(x_6, 0);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
x_8 = x_6;
x_9 = x_14;
goto block_13;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_10; 
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 1);
x_10 = x_8;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_10 = x_12;
goto block_11;
}
block_11:
{
x_3 = x_10;
goto block_5;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_6, 0);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
x_16 = x_6;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
x_3 = x_18;
goto block_5;
}
}
}
block_5:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_reset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_reset(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_stop(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_stop(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_stop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_stop(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_15; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_st_ref_take(x_4);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 1;
x_7 = x_16;
goto block_14;
}
else
{
uint8_t x_17; 
x_17 = 0;
x_7 = x_17;
goto block_14;
}
block_14:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 1;
x_9 = lean_box(x_8);
x_10 = lean_st_ref_set(x_4, x_9);
if (x_7 == 0)
{
lean_object* x_11; 
x_11 = lean_apply_1(x_2, lean_box(0));
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_2);
x_12 = ((lean_object*)(l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0___closed__0));
x_13 = lean_io_promise_resolve(x_12, x_5);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_6 = x_9;
goto block_8;
}
block_8:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
else
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Std_Internal_IO_Async_Sleep_selector___lam__0___closed__1));
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_selector___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_6; 
x_6 = lean_uv_timer_cancel(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_14; 
x_7 = lean_ctor_get(x_6, 0);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
x_8 = x_6;
x_9 = x_14;
goto block_13;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_10; 
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 1);
x_10 = x_8;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_10 = x_12;
goto block_11;
}
block_11:
{
x_3 = x_10;
goto block_5;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_6, 0);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
x_16 = x_6;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
x_3 = x_18;
goto block_5;
}
}
}
block_5:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_selector___lam__1(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__2(lean_object* x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Sleep_selector___lam__2(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = ((lean_object*)(l_Std_Internal_IO_Async_Sleep_selector___lam__3___closed__0));
x_6 = l_Std_Internal_IO_Async_Waiter_race___at___00Std_Internal_IO_Async_Sleep_selector_spec__0(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Sleep_selector___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_7 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_25; 
x_13 = lean_ctor_get(x_2, 0);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
x_14 = x_2;
x_15 = x_25;
goto block_24;
}
else
{
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_io_promise_result_opt(x_13);
lean_dec(x_13);
x_17 = lean_unsigned_to_nat(0u);
x_18 = 0;
x_19 = l_BaseIO_chainTask___redArg(x_16, x_1, x_17, x_18);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_19);
x_20 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_20 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Sleep_selector___lam__4(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_12; 
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__3___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__4___boxed), 3, 1);
lean_closure_set(x_5, 0, x_4);
x_12 = lean_uv_timer_next(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
x_14 = x_12;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 1);
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
x_6 = x_16;
goto block_11;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_22 = x_12;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 0);
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
x_6 = x_24;
goto block_11;
}
}
}
block_11:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = 0;
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_8, x_9, x_7, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Sleep_selector___lam__5(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_13; 
lean_dec_ref(x_1);
x_5 = lean_ctor_get(x_3, 0);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
x_6 = x_3;
x_7 = x_13;
goto block_12;
}
else
{
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_8; 
if (x_7 == 0)
{
x_8 = x_6;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_5);
x_8 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_35; 
x_14 = lean_ctor_get(x_3, 0);
x_35 = !lean_is_exclusive(x_3);
if (x_35 == 0)
{
x_15 = x_3;
x_16 = x_35;
goto block_34;
}
else
{
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_17; uint8_t x_23; 
x_23 = lean_unbox(x_14);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_uv_timer_cancel(x_2);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_25);
x_26 = x_15;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
x_17 = x_26;
goto block_22;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec_ref(x_24);
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_29);
x_30 = x_15;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
x_17 = x_30;
goto block_22;
}
}
}
else
{
lean_object* x_33; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Std_Internal_IO_Async_Sleep_selector___lam__6___closed__2));
return x_33;
}
block_22:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unbox(x_14);
lean_dec(x_14);
x_21 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_19, x_20, x_18, x_1);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Internal_IO_Async_Sleep_selector___lam__6(x_1, x_2, x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_7 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_26; 
x_13 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
x_14 = x_2;
x_15 = x_26;
goto block_25;
}
else
{
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = x_26;
goto block_25;
}
block_25:
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_IO_Promise_isResolved___redArg(x_13);
lean_dec(x_13);
x_17 = lean_box(x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_18 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = 0;
x_22 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_20, x_21, x_19, x_1);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Sleep_selector___lam__7(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_10; 
x_10 = lean_uv_timer_next(x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
x_12 = x_10;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 1);
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
x_4 = x_14;
goto block_9;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_19 = lean_ctor_get(x_10, 0);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
x_20 = x_10;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
lean_ctor_set_tag(x_20, 0);
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
x_4 = x_22;
goto block_9;
}
}
}
block_9:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = 0;
x_8 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_6, x_7, x_5, x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Sleep_selector___lam__8(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Sleep_selector(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Sleep_selector___closed__0));
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__5___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__6___boxed), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__7___boxed), 3, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_closure((void*)(l_Std_Internal_IO_Async_Sleep_selector___lam__8___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___lam__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_6 = x_9;
goto block_8;
}
block_8:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_41; 
x_12 = lean_ctor_get(x_1, 0);
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
x_13 = x_1;
x_14 = x_41;
goto block_40;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_15; 
x_15 = lean_uv_timer_next(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_28; 
lean_del_object(x_13);
x_16 = lean_ctor_get(x_15, 0);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
x_17 = x_15;
x_18 = x_28;
goto block_27;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_19 = ((lean_object*)(l_Std_Internal_IO_Async_Sleep_wait___closed__1));
x_20 = lean_io_promise_result_opt(x_16);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(0u);
x_22 = 0;
x_23 = lean_task_map(x_19, x_20, x_21, x_22);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 0, x_23);
x_24 = x_17;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_39; 
x_29 = lean_ctor_get(x_15, 0);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
x_30 = x_15;
x_31 = x_39;
goto block_38;
}
else
{
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_box(0);
x_31 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_32; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_29);
x_32 = x_13;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_29);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_31 == 0)
{
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_32);
x_33 = x_30;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_sleep___lam__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_12; uint64_t x_13; uint8_t x_14; lean_object* x_15; 
x_3 = ((lean_object*)(l_Std_Internal_IO_Async_sleep___closed__0));
x_4 = ((lean_object*)(l_Std_Internal_IO_Async_Sleep_mk___closed__0));
x_12 = l_Int_toNat(x_1);
x_13 = lean_uint64_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_uv_timer_mk(x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
x_17 = x_15;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
x_5 = x_19;
goto block_11;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_24 = lean_ctor_get(x_15, 0);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
x_25 = x_15;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
x_5 = x_27;
goto block_11;
}
}
}
block_11:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_7, x_8, x_6, x_4);
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_7, x_8, x_9, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_sleep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_sleep(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
x_6 = x_9;
goto block_8;
}
block_8:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_21; 
x_12 = lean_ctor_get(x_1, 0);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
x_13 = x_1;
x_14 = x_21;
goto block_20;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_Internal_IO_Async_Sleep_selector(x_12);
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_16 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Selector_sleep___lam__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_12; uint64_t x_13; uint8_t x_14; lean_object* x_15; 
x_3 = ((lean_object*)(l_Std_Internal_IO_Async_Selector_sleep___closed__0));
x_4 = ((lean_object*)(l_Std_Internal_IO_Async_Sleep_mk___closed__0));
x_12 = l_Int_toNat(x_1);
x_13 = lean_uint64_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
x_15 = lean_uv_timer_mk(x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
x_17 = x_15;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 1);
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
x_5 = x_19;
goto block_11;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_24 = lean_ctor_get(x_15, 0);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
x_25 = x_15;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
lean_ctor_set_tag(x_25, 0);
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
x_5 = x_27;
goto block_11;
}
}
}
block_11:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = 0;
x_9 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_7, x_8, x_6, x_4);
x_10 = l___private_Std_Internal_Async_Basic_0__Std_Internal_IO_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), x_7, x_8, x_9, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Selector_sleep___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Selector_sleep(x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__10));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__12);
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__16));
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__17);
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__15));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__18);
x_2 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__13);
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__19);
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__20);
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__21);
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__22);
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__23);
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__24);
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__5));
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__25);
x_2 = ((lean_object*)(l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Std_Internal_IO_Async_Interval_mk___auto__1(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26, &l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26_once, _init_l_Std_Internal_IO_Async_Interval_mk___auto__1___closed__26);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Int_toNat(x_1);
x_4 = lean_uint64_of_nat(x_3);
lean_dec(x_3);
x_5 = 1;
x_6 = lean_uv_timer_mk(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_14; 
x_7 = lean_ctor_get(x_6, 0);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
x_8 = x_6;
x_9 = x_14;
goto block_13;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_10; 
if (x_9 == 0)
{
x_10 = x_8;
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_10 = x_12;
goto block_11;
}
block_11:
{
return x_10;
}
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
x_15 = lean_ctor_get(x_6, 0);
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
x_16 = x_6;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Interval_mk___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint64_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = l_Int_toNat(x_1);
x_5 = lean_uint64_of_nat(x_4);
lean_dec(x_4);
x_6 = 1;
x_7 = lean_uv_timer_mk(x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_15; 
x_8 = lean_ctor_get(x_7, 0);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
x_9 = x_7;
x_10 = x_15;
goto block_14;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_11; 
if (x_10 == 0)
{
x_11 = x_9;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_8);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_ctor_get(x_7, 0);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
x_17 = x_7;
x_18 = x_23;
goto block_22;
}
else
{
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; 
if (x_18 == 0)
{
x_19 = x_17;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
x_19 = x_21;
goto block_20;
}
block_20:
{
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_mk___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_IO_Async_Interval_mk(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_tick(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_next(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_16; 
x_4 = lean_ctor_get(x_3, 0);
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
x_5 = x_3;
x_6 = x_16;
goto block_15;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = ((lean_object*)(l_Std_Internal_IO_Async_Sleep_wait___closed__1));
x_8 = lean_io_promise_result_opt(x_4);
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(0u);
x_10 = 0;
x_11 = lean_task_map(x_7, x_8, x_9, x_10);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_11);
x_12 = x_5;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_25; 
x_17 = lean_ctor_get(x_3, 0);
x_25 = !lean_is_exclusive(x_3);
if (x_25 == 0)
{
x_18 = x_3;
x_19 = x_25;
goto block_24;
}
else
{
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_20; 
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
x_20 = x_18;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_17);
x_20 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_tick___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Interval_tick(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_reset(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_reset(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_reset___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Interval_reset(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_stop(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = lean_uv_timer_stop(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_IO_Async_Interval_stop___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_IO_Async_Interval_stop(x_1);
lean_dec(x_1);
return x_3;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_Timer(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Async_Select(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Async_Timer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_Timer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Async_Select(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Async_Timer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Internal_IO_Async_Interval_mk___auto__1 = _init_l_Std_Internal_IO_Async_Interval_mk___auto__1();
lean_mark_persistent(l_Std_Internal_IO_Async_Interval_mk___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_Timer(uint8_t builtin);
lean_object* initialize_Std_Internal_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Async_Timer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_Timer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Async_Select(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Async_Timer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Async_Timer(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Async_Timer(builtin);
}
#ifdef __cplusplus
}
#endif

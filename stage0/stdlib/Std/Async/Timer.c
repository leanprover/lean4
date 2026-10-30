// Lean compiler output
// Module: Std.Async.Timer
// Imports: public import Std.Time public import Std.Internal.UV.Timer public import Std.Async.Select
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
lean_object* l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_uv_timer_cancel(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_uv_timer_next(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_uv_timer_reset(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_uv_timer_mk(uint64_t, uint8_t);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
lean_object* lean_uv_timer_stop(lean_object*);
static lean_once_cell_t l___private_Std_Async_Timer_0__Std_Async_timeoutOf___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Std_Async_Timer_0__Std_Async_timeoutOf___closed__0;
LEAN_EXPORT uint64_t l___private_Std_Async_Timer_0__Std_Async_timeoutOf(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Async_Timer_0__Std_Async_timeoutOf___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Sleep_mk___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Sleep_mk___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Sleep_mk___closed__0 = (const lean_object*)&l_Std_Async_Sleep_mk___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Sleep_wait___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "the promise linked to the Async was dropped"};
static const lean_object* l_Std_Async_Sleep_wait___closed__0 = (const lean_object*)&l_Std_Async_Sleep_wait___closed__0_value;
static const lean_closure_object l_Std_Async_Sleep_wait___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Sleep_wait___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Async_Sleep_wait___closed__0_value)} };
static const lean_object* l_Std_Async_Sleep_wait___closed__1 = (const lean_object*)&l_Std_Async_Sleep_wait___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_reset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_reset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_stop___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0 = (const lean_object*)&l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Sleep_selector___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Sleep_selector___lam__0___closed__0 = (const lean_object*)&l_Std_Async_Sleep_selector___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Async_Sleep_selector___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Sleep_selector___lam__0___closed__0_value)}};
static const lean_object* l_Std_Async_Sleep_selector___lam__0___closed__1 = (const lean_object*)&l_Std_Async_Sleep_selector___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Sleep_selector___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Sleep_selector___lam__2___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_Async_Sleep_selector___lam__3___closed__0 = (const lean_object*)&l_Std_Async_Sleep_selector___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__5___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Async_Sleep_selector___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Async_Sleep_selector___lam__6___closed__0 = (const lean_object*)&l_Std_Async_Sleep_selector___lam__6___closed__0_value;
static const lean_ctor_object l_Std_Async_Sleep_selector___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Sleep_selector___lam__6___closed__0_value)}};
static const lean_object* l_Std_Async_Sleep_selector___lam__6___closed__1 = (const lean_object*)&l_Std_Async_Sleep_selector___lam__6___closed__1_value;
static const lean_ctor_object l_Std_Async_Sleep_selector___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Async_Sleep_selector___lam__6___closed__1_value)}};
static const lean_object* l_Std_Async_Sleep_selector___lam__6___closed__2 = (const lean_object*)&l_Std_Async_Sleep_selector___lam__6___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Sleep_selector___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Sleep_selector___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Sleep_selector___closed__0 = (const lean_object*)&l_Std_Async_Sleep_selector___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_sleep___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_sleep___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_sleep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_sleep___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_sleep___closed__0 = (const lean_object*)&l_Std_Async_sleep___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_sleep(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_sleep___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Async_Selector_sleep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Async_Selector_sleep___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Async_Selector_sleep___closed__0 = (const lean_object*)&l_Std_Async_Selector_sleep___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Async_Interval_mk___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__0 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__0_value;
static const lean_string_object l_Std_Async_Interval_mk___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__1 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__1_value;
static const lean_string_object l_Std_Async_Interval_mk___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__2 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__2_value;
static const lean_string_object l_Std_Async_Interval_mk___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__3 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__3_value;
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__4 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__4_value;
static const lean_array_object l_Std_Async_Interval_mk___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__5 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__5_value;
static const lean_string_object l_Std_Async_Interval_mk___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__6 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__6_value;
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__7 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__7_value;
static const lean_string_object l_Std_Async_Interval_mk___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__8 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__8_value;
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__9 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__9_value;
static const lean_string_object l_Std_Async_Interval_mk___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__10 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__10_value;
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(53, 158, 1, 232, 101, 200, 191, 197)}};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__11 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__11_value;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__12;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__13;
static const lean_string_object l_Std_Async_Interval_mk___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__14 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__14_value;
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_0),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_1),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__15_value_aux_2),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__15 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__15_value;
static const lean_ctor_object l_Std_Async_Interval_mk___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__9_value),((lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__5_value)}};
static const lean_object* l_Std_Async_Interval_mk___auto__1___closed__16 = (const lean_object*)&l_Std_Async_Interval_mk___auto__1___closed__16_value;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__17;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__18;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__19;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__20;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__21;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__22;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__23;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__24;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__25;
static lean_once_cell_t l_Std_Async_Interval_mk___auto__1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Async_Interval_mk___auto__1___closed__26;
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___auto__1;
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Interval_tick(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Interval_tick___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Interval_reset(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Interval_reset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Interval_stop(lean_object*);
LEAN_EXPORT lean_object* l_Std_Async_Interval_stop___boxed(lean_object*, lean_object*);
static lean_object* _init_l___private_Std_Async_Timer_0__Std_Async_timeoutOf___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_cstr_to_nat("18446744073709551616");
return v___x_1_;
}
}
LEAN_EXPORT uint64_t l___private_Std_Async_Timer_0__Std_Async_timeoutOf(lean_object* v_duration_2_){
_start:
{
lean_object* v_ms_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v_ms_3_ = l_Int_toNat(v_duration_2_);
v___x_4_ = lean_obj_once(&l___private_Std_Async_Timer_0__Std_Async_timeoutOf___closed__0, &l___private_Std_Async_Timer_0__Std_Async_timeoutOf___closed__0_once, _init_l___private_Std_Async_Timer_0__Std_Async_timeoutOf___closed__0);
v___x_5_ = lean_nat_dec_lt(v_ms_3_, v___x_4_);
if (v___x_5_ == 0)
{
uint64_t v___x_6_; 
lean_dec(v_ms_3_);
v___x_6_ = 18446744073709551615ULL;
return v___x_6_;
}
else
{
uint64_t v___x_7_; 
v___x_7_ = lean_uint64_of_nat(v_ms_3_);
lean_dec(v_ms_3_);
return v___x_7_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Async_Timer_0__Std_Async_timeoutOf___boxed(lean_object* v_duration_8_){
_start:
{
uint64_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_8_);
lean_dec(v_duration_8_);
v_r_10_ = lean_box_uint64(v_res_9_);
return v_r_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___lam__0(lean_object* v_x_11_){
_start:
{
if (lean_obj_tag(v_x_11_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_21_; 
v_a_13_ = lean_ctor_get(v_x_11_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_21_ == 0)
{
v___x_15_ = v_x_11_;
v_isShared_16_ = v_isSharedCheck_21_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_dec(v_x_11_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_21_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_16_ == 0)
{
v___x_18_ = v___x_15_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_a_13_);
v___x_18_ = v_reuseFailAlloc_20_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_19_; 
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
return v___x_19_;
}
}
}
else
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_30_; 
v_a_22_ = lean_ctor_get(v_x_11_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v_x_11_);
if (v_isSharedCheck_30_ == 0)
{
v___x_24_ = v_x_11_;
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v_x_11_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_30_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_22_);
v___x_27_ = v_reuseFailAlloc_29_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
lean_object* v___x_28_; 
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___lam__0___boxed(lean_object* v_x_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_Async_Sleep_mk___lam__0(v_x_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk(lean_object* v_duration_35_){
_start:
{
lean_object* v___f_37_; uint64_t v___x_38_; uint8_t v___x_39_; lean_object* v___x_40_; lean_object* v_val_42_; lean_object* v___x_45_; 
v___f_37_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_38_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_35_);
v___x_39_ = 0;
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_uv_timer_mk(v___x_38_, v___x_39_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 1);
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
v_val_42_ = v___x_51_;
goto v___jp_41_;
}
}
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
v_a_54_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_45_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_45_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set_tag(v___x_56_, 0);
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
v_val_42_ = v___x_59_;
goto v___jp_41_;
}
}
}
v___jp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_43_, 0, v_val_42_);
v___x_44_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_40_, v___x_39_, v___x_43_, v___f_37_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___boxed(lean_object* v_duration_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_Async_Sleep_mk(v_duration_62_);
lean_dec(v_duration_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait___lam__0(lean_object* v___x_65_, lean_object* v_x_66_){
_start:
{
if (lean_obj_tag(v_x_66_) == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_mk_io_user_error(v___x_65_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
else
{
lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
lean_dec_ref(v___x_65_);
v_val_69_ = lean_ctor_get(v_x_66_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v_x_66_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_dec(v_x_66_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_val_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait(lean_object* v_s_80_){
_start:
{
lean_object* v___f_82_; lean_object* v___x_83_; 
v___f_82_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_83_ = lean_uv_timer_next(v_s_80_);
if (lean_obj_tag(v___x_83_) == 0)
{
lean_object* v_a_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_95_; 
v_a_84_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_95_ == 0)
{
v___x_86_ = v___x_83_;
v_isShared_87_ = v_isSharedCheck_95_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_a_84_);
lean_dec(v___x_83_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_95_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_88_ = lean_io_promise_result_opt(v_a_84_);
lean_dec(v_a_84_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = 0;
v___x_91_ = lean_task_map(v___f_82_, v___x_88_, v___x_89_, v___x_90_);
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 1);
lean_ctor_set(v___x_86_, 0, v___x_91_);
v___x_93_ = v___x_86_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_104_; 
v_a_96_ = lean_ctor_get(v___x_83_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_104_ == 0)
{
v___x_98_ = v___x_83_;
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_83_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_104_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set_tag(v___x_98_, 0);
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_103_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; 
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait___boxed(lean_object* v_s_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_Async_Sleep_wait(v_s_105_);
lean_dec(v_s_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_reset(lean_object* v_s_108_){
_start:
{
lean_object* v_val_111_; lean_object* v___x_113_; 
v___x_113_ = lean_uv_timer_reset(v_s_108_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 1);
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v_val_111_ = v___x_119_;
goto v___jp_110_;
}
}
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_a_122_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_113_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_113_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 0);
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v_val_111_ = v___x_127_;
goto v___jp_110_;
}
}
}
v___jp_110_:
{
lean_object* v___x_112_; 
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v_val_111_);
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_reset___boxed(lean_object* v_s_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_Async_Sleep_reset(v_s_130_);
lean_dec(v_s_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_stop(lean_object* v_s_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lean_uv_timer_stop(v_s_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_stop___boxed(lean_object* v_s_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_Async_Sleep_stop(v_s_136_);
lean_dec(v_s_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(lean_object* v_w_141_, lean_object* v_lose_142_){
_start:
{
lean_object* v_finished_144_; lean_object* v_promise_145_; lean_object* v___x_146_; uint8_t v___y_148_; uint8_t v___x_155_; 
v_finished_144_ = lean_ctor_get(v_w_141_, 0);
v_promise_145_ = lean_ctor_get(v_w_141_, 1);
v___x_146_ = lean_st_ref_take(v_finished_144_);
v___x_155_ = lean_unbox(v___x_146_);
lean_dec(v___x_146_);
if (v___x_155_ == 0)
{
uint8_t v___x_156_; 
v___x_156_ = 1;
v___y_148_ = v___x_156_;
goto v___jp_147_;
}
else
{
uint8_t v___x_157_; 
v___x_157_ = 0;
v___y_148_ = v___x_157_;
goto v___jp_147_;
}
v___jp_147_:
{
uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = 1;
v___x_150_ = lean_box(v___x_149_);
v___x_151_ = lean_st_ref_put(v_finished_144_, v___x_150_);
if (v___y_148_ == 0)
{
lean_object* v___x_152_; 
v___x_152_ = lean_apply_1(v_lose_142_, lean_box(0));
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref(v_lose_142_);
v___x_153_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0));
v___x_154_ = lean_io_promise_resolve(v___x_153_, v_promise_145_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___boxed(lean_object* v_w_158_, lean_object* v_lose_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(v_w_158_, v_lose_159_);
lean_dec_ref(v_w_158_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__0(lean_object* v_x_166_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_176_; 
v_a_168_ = lean_ctor_get(v_x_166_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_166_);
if (v_isSharedCheck_176_ == 0)
{
v___x_170_ = v_x_166_;
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v_x_166_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_176_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_175_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; 
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
}
else
{
lean_object* v___x_177_; 
lean_dec_ref_known(v_x_166_, 1);
v___x_177_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__0___closed__1));
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__0___boxed(lean_object* v_x_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_Async_Sleep_selector___lam__0(v_x_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__1(lean_object* v_s_181_){
_start:
{
lean_object* v_val_184_; lean_object* v___x_186_; 
v___x_186_ = lean_uv_timer_cancel(v_s_181_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 1);
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
v_val_184_ = v___x_192_;
goto v___jp_183_;
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_a_195_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_186_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_186_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 0);
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
v_val_184_ = v___x_200_;
goto v___jp_183_;
}
}
}
v___jp_183_:
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_185_, 0, v_val_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__1___boxed(lean_object* v_s_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_Async_Sleep_selector___lam__1(v_s_203_);
lean_dec(v_s_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__2(lean_object* v___x_206_){
_start:
{
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__2___boxed(lean_object* v___x_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Async_Sleep_selector___lam__2(v___x_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__3(lean_object* v_waiter_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v___f_217_; lean_object* v___x_218_; 
v___f_217_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__3___closed__0));
v___x_218_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(v_waiter_213_, v___f_217_);
return v___x_218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__3___boxed(lean_object* v_waiter_219_, lean_object* v_x_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_Async_Sleep_selector___lam__3(v_waiter_219_, v_x_220_);
lean_dec(v_x_220_);
lean_dec_ref(v_waiter_219_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__4(lean_object* v___f_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v___f_223_);
v_a_226_ = lean_ctor_get(v_x_224_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v_x_224_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v_x_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_233_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
return v___x_232_;
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_247_; 
v_a_235_ = lean_ctor_get(v_x_224_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_x_224_);
if (v_isSharedCheck_247_ == 0)
{
v___x_237_ = v_x_224_;
v_isShared_238_ = v_isSharedCheck_247_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v_x_224_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_247_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_239_ = lean_io_promise_result_opt(v_a_235_);
lean_dec(v_a_235_);
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = 0;
v___x_242_ = l_BaseIO_chainTask___redArg(v___x_239_, v___f_223_, v___x_240_, v___x_241_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_242_);
v___x_244_ = v___x_237_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_246_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; 
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__4___boxed(lean_object* v___f_248_, lean_object* v_x_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_Async_Sleep_selector___lam__4(v___f_248_, v_x_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__5(lean_object* v_s_252_, lean_object* v_waiter_253_){
_start:
{
lean_object* v___f_255_; lean_object* v___f_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v_val_260_; lean_object* v___x_263_; 
v___f_255_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_255_, 0, v_waiter_253_);
v___f_256_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_256_, 0, v___f_255_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = 0;
v___x_263_ = lean_uv_timer_next(v_s_252_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_263_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_263_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 1);
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
v_val_260_ = v___x_269_;
goto v___jp_259_;
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
v_a_272_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_263_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_263_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
lean_ctor_set_tag(v___x_274_, 0);
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
v_val_260_ = v___x_277_;
goto v___jp_259_;
}
}
}
v___jp_259_:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v_val_260_);
v___x_262_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_257_, v___x_258_, v___x_261_, v___f_256_);
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__5___boxed(lean_object* v_s_280_, lean_object* v_waiter_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_Async_Sleep_selector___lam__5(v_s_280_, v_waiter_281_);
lean_dec(v_s_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__6(lean_object* v___f_290_, lean_object* v_s_291_, lean_object* v_x_292_){
_start:
{
if (lean_obj_tag(v_x_292_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_302_; 
lean_dec_ref(v___f_290_);
v_a_294_ = lean_ctor_get(v_x_292_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_x_292_);
if (v_isSharedCheck_302_ == 0)
{
v___x_296_ = v_x_292_;
v_isShared_297_ = v_isSharedCheck_302_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v_x_292_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_302_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_294_);
v___x_299_ = v_reuseFailAlloc_301_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_324_; 
v_a_303_ = lean_ctor_get(v_x_292_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v_x_292_);
if (v_isSharedCheck_324_ == 0)
{
v___x_305_ = v_x_292_;
v_isShared_306_ = v_isSharedCheck_324_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v_x_292_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_324_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
uint8_t v___x_307_; 
v___x_307_ = lean_unbox(v_a_303_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v_val_310_; lean_object* v___x_314_; 
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_uv_timer_cancel(v_s_291_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_314_, 1);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v_a_315_);
v___x_317_ = v___x_305_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
v_val_310_ = v___x_317_;
goto v___jp_309_;
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; 
v_a_319_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_314_, 1);
if (v_isShared_306_ == 0)
{
lean_ctor_set_tag(v___x_305_, 0);
lean_ctor_set(v___x_305_, 0, v_a_319_);
v___x_321_ = v___x_305_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
v_val_310_ = v___x_321_;
goto v___jp_309_;
}
}
v___jp_309_:
{
lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v_val_310_);
v___x_312_ = lean_unbox(v_a_303_);
lean_dec(v_a_303_);
v___x_313_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_308_, v___x_312_, v___x_311_, v___f_290_);
return v___x_313_;
}
}
else
{
lean_object* v___x_323_; 
lean_del_object(v___x_305_);
lean_dec(v_a_303_);
lean_dec_ref(v___f_290_);
v___x_323_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__6___closed__2));
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__6___boxed(lean_object* v___f_325_, lean_object* v_s_326_, lean_object* v_x_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Std_Async_Sleep_selector___lam__6(v___f_325_, v_s_326_, v_x_327_);
lean_dec(v_s_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__7(lean_object* v___f_330_, lean_object* v_x_331_){
_start:
{
if (lean_obj_tag(v_x_331_) == 0)
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_341_; 
lean_dec_ref(v___f_330_);
v_a_333_ = lean_ctor_get(v_x_331_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v_x_331_);
if (v_isSharedCheck_341_ == 0)
{
v___x_335_ = v_x_331_;
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v_x_331_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_341_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_340_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_355_; 
v_a_342_ = lean_ctor_get(v_x_331_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_331_);
if (v_isSharedCheck_355_ == 0)
{
v___x_344_ = v_x_331_;
v_isShared_345_ = v_isSharedCheck_355_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v_x_331_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_355_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; uint8_t v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = 0;
v___x_348_ = l_IO_Promise_isResolved___redArg(v_a_342_);
lean_dec(v_a_342_);
v___x_349_ = lean_box(v___x_348_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_349_);
v___x_351_ = v___x_344_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_349_);
v___x_351_ = v_reuseFailAlloc_354_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
v___x_353_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_346_, v___x_347_, v___x_352_, v___f_330_);
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__7___boxed(lean_object* v___f_356_, lean_object* v_x_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_Async_Sleep_selector___lam__7(v___f_356_, v_x_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__8(lean_object* v___f_360_, lean_object* v_s_361_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v_val_366_; lean_object* v___x_369_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = 0;
v___x_369_ = lean_uv_timer_next(v_s_361_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 1);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
v_val_366_ = v___x_375_;
goto v___jp_365_;
}
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
v_a_378_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_369_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_369_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 0);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
v_val_366_ = v___x_383_;
goto v___jp_365_;
}
}
}
v___jp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v_val_366_);
v___x_368_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_363_, v___x_364_, v___x_367_, v___f_360_);
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__8___boxed(lean_object* v___f_386_, lean_object* v_s_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_Async_Sleep_selector___lam__8(v___f_386_, v_s_387_);
lean_dec(v_s_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector(lean_object* v_s_391_){
_start:
{
lean_object* v___f_392_; lean_object* v___f_393_; lean_object* v___f_394_; lean_object* v___f_395_; lean_object* v___f_396_; lean_object* v___f_397_; lean_object* v___x_398_; 
v___f_392_ = ((lean_object*)(l_Std_Async_Sleep_selector___closed__0));
lean_inc_n(v_s_391_, 3);
v___f_393_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__1___boxed), 2, 1);
lean_closure_set(v___f_393_, 0, v_s_391_);
v___f_394_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__5___boxed), 3, 1);
lean_closure_set(v___f_394_, 0, v_s_391_);
v___f_395_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_395_, 0, v___f_392_);
lean_closure_set(v___f_395_, 1, v_s_391_);
v___f_396_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_396_, 0, v___f_395_);
v___f_397_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__8___boxed), 3, 2);
lean_closure_set(v___f_397_, 0, v___f_396_);
lean_closure_set(v___f_397_, 1, v_s_391_);
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v___f_397_);
lean_ctor_set(v___x_398_, 1, v___f_394_);
lean_ctor_set(v___x_398_, 2, v___f_393_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___lam__1(lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_399_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_a_401_ = lean_ctor_get(v_x_399_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_x_399_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v_x_399_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v_x_399_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_408_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_439_; 
v_a_410_ = lean_ctor_get(v_x_399_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_x_399_);
if (v_isSharedCheck_439_ == 0)
{
v___x_412_ = v_x_399_;
v_isShared_413_ = v_isSharedCheck_439_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v_x_399_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_439_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___f_414_; lean_object* v___x_415_; 
v___f_414_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_415_ = lean_uv_timer_next(v_a_410_);
lean_dec(v_a_410_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_427_; 
lean_del_object(v___x_412_);
v_a_416_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_427_ == 0)
{
v___x_418_ = v___x_415_;
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_415_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_427_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_420_ = lean_io_promise_result_opt(v_a_416_);
lean_dec(v_a_416_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = 0;
v___x_423_ = lean_task_map(v___f_414_, v___x_420_, v___x_421_, v___x_422_);
if (v_isShared_419_ == 0)
{
lean_ctor_set_tag(v___x_418_, 1);
lean_ctor_set(v___x_418_, 0, v___x_423_);
v___x_425_ = v___x_418_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_438_; 
v_a_428_ = lean_ctor_get(v___x_415_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_438_ == 0)
{
v___x_430_ = v___x_415_;
v_isShared_431_ = v_isSharedCheck_438_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_415_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_438_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set_tag(v___x_412_, 0);
lean_ctor_set(v___x_412_, 0, v_a_428_);
v___x_433_ = v___x_412_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_437_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 0);
lean_ctor_set(v___x_430_, 0, v___x_433_);
v___x_435_ = v___x_430_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___lam__1___boxed(lean_object* v_x_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_Async_sleep___lam__1(v_x_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep(lean_object* v_duration_444_){
_start:
{
lean_object* v___f_446_; lean_object* v___f_447_; lean_object* v___x_448_; uint8_t v___x_449_; lean_object* v_val_451_; uint64_t v___x_455_; lean_object* v___x_456_; 
v___f_446_ = ((lean_object*)(l_Std_Async_sleep___closed__0));
v___f_447_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = 0;
v___x_455_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_444_);
v___x_456_ = lean_uv_timer_mk(v___x_455_, v___x_449_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 1);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
v_val_451_ = v___x_462_;
goto v___jp_450_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_a_465_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_456_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_456_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
lean_ctor_set_tag(v___x_467_, 0);
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
v_val_451_ = v___x_470_;
goto v___jp_450_;
}
}
}
v___jp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v_val_451_);
v___x_453_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_448_, v___x_449_, v___x_452_, v___f_447_);
v___x_454_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_448_, v___x_449_, v___x_453_, v___f_446_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___boxed(lean_object* v_duration_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_Async_sleep(v_duration_473_);
lean_dec(v_duration_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___lam__0(lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_486_; 
v_a_478_ = lean_ctor_get(v_x_476_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v_x_476_);
if (v_isSharedCheck_486_ == 0)
{
v___x_480_ = v_x_476_;
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v_x_476_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_486_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_485_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; 
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_496_; 
v_a_487_ = lean_ctor_get(v_x_476_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_x_476_);
if (v_isSharedCheck_496_ == 0)
{
v___x_489_ = v_x_476_;
v_isShared_490_ = v_isSharedCheck_496_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v_x_476_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_496_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = l_Std_Async_Sleep_selector(v_a_487_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_491_);
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_491_);
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
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___lam__0___boxed(lean_object* v_x_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_Async_Selector_sleep___lam__0(v_x_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep(lean_object* v_duration_501_){
_start:
{
lean_object* v___f_503_; lean_object* v___f_504_; lean_object* v___x_505_; uint8_t v___x_506_; lean_object* v_val_508_; uint64_t v___x_512_; lean_object* v___x_513_; 
v___f_503_ = ((lean_object*)(l_Std_Async_Selector_sleep___closed__0));
v___f_504_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = 0;
v___x_512_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_501_);
v___x_513_ = lean_uv_timer_mk(v___x_512_, v___x_506_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set_tag(v___x_516_, 1);
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
v_val_508_ = v___x_519_;
goto v___jp_507_;
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
v_a_522_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_513_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_513_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set_tag(v___x_524_, 0);
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
v_val_508_ = v___x_527_;
goto v___jp_507_;
}
}
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v_val_508_);
v___x_510_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_505_, v___x_506_, v___x_509_, v___f_504_);
v___x_511_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_505_, v___x_506_, v___x_510_, v___f_503_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___boxed(lean_object* v_duration_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_Async_Selector_sleep(v_duration_530_);
lean_dec(v_duration_530_);
return v_res_532_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__12(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__10));
v___x_560_ = l_Lean_mkAtom(v___x_559_);
return v___x_560_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__13(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__12, &l_Std_Async_Interval_mk___auto__1___closed__12_once, _init_l_Std_Async_Interval_mk___auto__1___closed__12);
v___x_562_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_563_ = lean_array_push(v___x_562_, v___x_561_);
return v___x_563_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__17(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__16));
v___x_575_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_576_ = lean_array_push(v___x_575_, v___x_574_);
return v___x_576_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__18(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__17, &l_Std_Async_Interval_mk___auto__1___closed__17_once, _init_l_Std_Async_Interval_mk___auto__1___closed__17);
v___x_578_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__15));
v___x_579_ = lean_box(2);
v___x_580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_577_);
return v___x_580_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__19(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__18, &l_Std_Async_Interval_mk___auto__1___closed__18_once, _init_l_Std_Async_Interval_mk___auto__1___closed__18);
v___x_582_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__13, &l_Std_Async_Interval_mk___auto__1___closed__13_once, _init_l_Std_Async_Interval_mk___auto__1___closed__13);
v___x_583_ = lean_array_push(v___x_582_, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__20(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_584_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__19, &l_Std_Async_Interval_mk___auto__1___closed__19_once, _init_l_Std_Async_Interval_mk___auto__1___closed__19);
v___x_585_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__11));
v___x_586_ = lean_box(2);
v___x_587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
lean_ctor_set(v___x_587_, 2, v___x_584_);
return v___x_587_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__21(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__20, &l_Std_Async_Interval_mk___auto__1___closed__20_once, _init_l_Std_Async_Interval_mk___auto__1___closed__20);
v___x_589_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_590_ = lean_array_push(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__22(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__21, &l_Std_Async_Interval_mk___auto__1___closed__21_once, _init_l_Std_Async_Interval_mk___auto__1___closed__21);
v___x_592_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__9));
v___x_593_ = lean_box(2);
v___x_594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
lean_ctor_set(v___x_594_, 2, v___x_591_);
return v___x_594_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__23(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__22, &l_Std_Async_Interval_mk___auto__1___closed__22_once, _init_l_Std_Async_Interval_mk___auto__1___closed__22);
v___x_596_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_597_ = lean_array_push(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__24(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_598_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__23, &l_Std_Async_Interval_mk___auto__1___closed__23_once, _init_l_Std_Async_Interval_mk___auto__1___closed__23);
v___x_599_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__7));
v___x_600_ = lean_box(2);
v___x_601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_599_);
lean_ctor_set(v___x_601_, 2, v___x_598_);
return v___x_601_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__25(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__24, &l_Std_Async_Interval_mk___auto__1___closed__24_once, _init_l_Std_Async_Interval_mk___auto__1___closed__24);
v___x_603_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_604_ = lean_array_push(v___x_603_, v___x_602_);
return v___x_604_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__26(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_605_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__25, &l_Std_Async_Interval_mk___auto__1___closed__25_once, _init_l_Std_Async_Interval_mk___auto__1___closed__25);
v___x_606_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__4));
v___x_607_ = lean_box(2);
v___x_608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v___x_606_);
lean_ctor_set(v___x_608_, 2, v___x_605_);
return v___x_608_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1(void){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__26, &l_Std_Async_Interval_mk___auto__1___closed__26_once, _init_l_Std_Async_Interval_mk___auto__1___closed__26);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___redArg(lean_object* v_duration_610_){
_start:
{
uint64_t v___x_612_; uint8_t v___x_613_; lean_object* v___x_614_; 
v___x_612_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_610_);
v___x_613_ = 1;
v___x_614_ = lean_uv_timer_mk(v___x_612_, v___x_613_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
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
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
v_a_623_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_614_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_614_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___redArg___boxed(lean_object* v_duration_631_, lean_object* v_a_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_Std_Async_Interval_mk___redArg(v_duration_631_);
lean_dec(v_duration_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk(lean_object* v_duration_634_, lean_object* v_x_635_){
_start:
{
uint64_t v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; 
v___x_637_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_634_);
v___x_638_ = 1;
v___x_639_ = lean_uv_timer_mk(v___x_637_, v___x_638_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_a_648_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_639_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_639_);
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
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___boxed(lean_object* v_duration_656_, lean_object* v_x_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_Async_Interval_mk(v_duration_656_, v_x_657_);
lean_dec(v_duration_656_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_tick(lean_object* v_i_660_){
_start:
{
lean_object* v___f_662_; lean_object* v___x_663_; 
v___f_662_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_663_ = lean_uv_timer_next(v_i_660_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_675_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_675_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_675_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_675_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_668_ = lean_io_promise_result_opt(v_a_664_);
lean_dec(v_a_664_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = 0;
v___x_671_ = lean_task_map(v___f_662_, v___x_668_, v___x_669_, v___x_670_);
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 1);
lean_ctor_set(v___x_666_, 0, v___x_671_);
v___x_673_ = v___x_666_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_684_; 
v_a_676_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_684_ == 0)
{
v___x_678_ = v___x_663_;
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_663_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_684_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set_tag(v___x_678_, 0);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_683_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; 
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_tick___boxed(lean_object* v_i_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_Async_Interval_tick(v_i_685_);
lean_dec(v_i_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_reset(lean_object* v_i_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = lean_uv_timer_reset(v_i_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_reset___boxed(lean_object* v_i_691_, lean_object* v_a_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_Async_Interval_reset(v_i_691_);
lean_dec(v_i_691_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_stop(lean_object* v_i_694_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = lean_uv_timer_stop(v_i_694_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_stop___boxed(lean_object* v_i_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Std_Async_Interval_stop(v_i_697_);
lean_dec(v_i_697_);
return v_res_699_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_Timer(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Timer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_UV_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Async_Timer(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_Async_Interval_mk___auto__1 = _init_l_Std_Async_Interval_mk___auto__1();
lean_mark_persistent(l_Std_Async_Interval_mk___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time(uint8_t builtin);
lean_object* initialize_Std_Internal_UV_Timer(uint8_t builtin);
lean_object* initialize_Std_Async_Select(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Async_Timer(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_UV_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Async_Select(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Async_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Async_Timer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Async_Timer(builtin);
}
#ifdef __cplusplus
}
#endif

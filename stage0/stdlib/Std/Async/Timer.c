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
uint64_t l___private_Std_Async_Timer_0__Std_Async_timeoutOf(lean_object* v_duration_2_){
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
LEAN_EXPORT void l___private_Std_Async_Timer_0__Std_Async_timeoutOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_duration_2_ = stack[0].m_obj;
uint64_t v_res_8_;
v_res_8_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_2_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l___private_Std_Async_Timer_0__Std_Async_timeoutOf___boxed(lean_object* v_duration_9_){
_start:
{
uint64_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_9_);
lean_dec(v_duration_9_);
v_r_11_ = lean_box_uint64(v_res_10_);
return v_r_11_;
}
}
lean_object* l_Std_Async_Sleep_mk___lam__0(lean_object* v_x_12_){
_start:
{
if (lean_obj_tag(v_x_12_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_22_; 
v_a_14_ = lean_ctor_get(v_x_12_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v_x_12_);
if (v_isSharedCheck_22_ == 0)
{
v___x_16_ = v_x_12_;
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v_x_12_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_a_14_);
v___x_19_ = v_reuseFailAlloc_21_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
lean_object* v___x_20_; 
v___x_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
return v___x_20_;
}
}
}
else
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_31_; 
v_a_23_ = lean_ctor_get(v_x_12_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v_x_12_);
if (v_isSharedCheck_31_ == 0)
{
v___x_25_ = v_x_12_;
v_isShared_26_ = v_isSharedCheck_31_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v_x_12_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_31_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_30_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; 
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_mk___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_12_ = stack[0].m_obj;
lean_object* v_res_32_;
v_res_32_ = l_Std_Async_Sleep_mk___lam__0(v_x_12_);
stack->m_obj
 = v_res_32_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___lam__0___boxed(lean_object* v_x_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_Async_Sleep_mk___lam__0(v_x_33_);
return v_res_35_;
}
}
lean_object* l_Std_Async_Sleep_mk(lean_object* v_duration_37_){
_start:
{
lean_object* v___f_39_; uint64_t v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v_val_44_; lean_object* v___x_47_; 
v___f_39_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_40_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_37_);
v___x_41_ = 0;
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_uv_timer_mk(v___x_40_, v___x_41_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_47_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
lean_ctor_set_tag(v___x_50_, 1);
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
v_val_44_ = v___x_53_;
goto v___jp_43_;
}
}
}
else
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
v_a_56_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_47_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_47_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
lean_ctor_set_tag(v___x_58_, 0);
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
v_val_44_ = v___x_61_;
goto v___jp_43_;
}
}
}
v___jp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_45_, 0, v_val_44_);
v___x_46_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_42_, v___x_41_, v___x_45_, v___f_39_);
return v___x_46_;
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_duration_37_ = stack[0].m_obj;
lean_object* v_res_64_;
v_res_64_ = l_Std_Async_Sleep_mk(v_duration_37_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___boxed(lean_object* v_duration_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_Async_Sleep_mk(v_duration_65_);
lean_dec(v_duration_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait___lam__0(lean_object* v___x_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_mk_io_user_error(v___x_68_);
v___x_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
return v___x_71_;
}
else
{
lean_object* v_val_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
lean_dec_ref(v___x_68_);
v_val_72_ = lean_ctor_get(v_x_69_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_69_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v_x_69_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_val_72_);
lean_dec(v_x_69_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_val_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
lean_object* l_Std_Async_Sleep_wait(lean_object* v_s_83_){
_start:
{
lean_object* v___f_85_; lean_object* v___x_86_; 
v___f_85_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_86_ = lean_uv_timer_next(v_s_83_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_98_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_98_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_98_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_98_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_91_ = lean_io_promise_result_opt(v_a_87_);
lean_dec(v_a_87_);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = 0;
v___x_94_ = lean_task_map(v___f_85_, v___x_91_, v___x_92_, v___x_93_);
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 1);
lean_ctor_set(v___x_89_, 0, v___x_94_);
v___x_96_ = v___x_89_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
else
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_107_; 
v_a_99_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_107_ == 0)
{
v___x_101_ = v___x_86_;
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_86_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_107_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set_tag(v___x_101_, 0);
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_106_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_105_; 
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_83_ = stack[0].m_obj;
lean_object* v_res_108_;
v_res_108_ = l_Std_Async_Sleep_wait(v_s_83_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait___boxed(lean_object* v_s_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Std_Async_Sleep_wait(v_s_109_);
lean_dec(v_s_109_);
return v_res_111_;
}
}
lean_object* l_Std_Async_Sleep_reset(lean_object* v_s_112_){
_start:
{
lean_object* v_val_115_; lean_object* v___x_117_; 
v___x_117_ = lean_uv_timer_reset(v_s_112_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_117_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
lean_ctor_set_tag(v___x_120_, 1);
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
v_val_115_ = v___x_123_;
goto v___jp_114_;
}
}
}
else
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
v_a_126_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___x_117_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_117_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set_tag(v___x_128_, 0);
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
v_val_115_ = v___x_131_;
goto v___jp_114_;
}
}
}
v___jp_114_:
{
lean_object* v___x_116_; 
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v_val_115_);
return v___x_116_;
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_reset_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_112_ = stack[0].m_obj;
lean_object* v_res_134_;
v_res_134_ = l_Std_Async_Sleep_reset(v_s_112_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_reset___boxed(lean_object* v_s_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Std_Async_Sleep_reset(v_s_135_);
lean_dec(v_s_135_);
return v_res_137_;
}
}
lean_object* l_Std_Async_Sleep_stop(lean_object* v_s_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_uv_timer_stop(v_s_138_);
return v___x_140_;
}
}
LEAN_EXPORT void l_Std_Async_Sleep_stop_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_138_ = stack[0].m_obj;
lean_object* v_res_141_;
v_res_141_ = l_Std_Async_Sleep_stop(v_s_138_);
stack->m_obj
 = v_res_141_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_stop___boxed(lean_object* v_s_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_Async_Sleep_stop(v_s_142_);
lean_dec(v_s_142_);
return v_res_144_;
}
}
lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(lean_object* v_w_147_, lean_object* v_lose_148_){
_start:
{
lean_object* v_finished_150_; lean_object* v_promise_151_; lean_object* v___x_152_; uint8_t v___y_154_; uint8_t v___x_161_; 
v_finished_150_ = lean_ctor_get(v_w_147_, 0);
v_promise_151_ = lean_ctor_get(v_w_147_, 1);
v___x_152_ = lean_st_ref_take(v_finished_150_);
v___x_161_ = lean_unbox(v___x_152_);
lean_dec(v___x_152_);
if (v___x_161_ == 0)
{
uint8_t v___x_162_; 
v___x_162_ = 1;
v___y_154_ = v___x_162_;
goto v___jp_153_;
}
else
{
uint8_t v___x_163_; 
v___x_163_ = 0;
v___y_154_ = v___x_163_;
goto v___jp_153_;
}
v___jp_153_:
{
uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = 1;
v___x_156_ = lean_box(v___x_155_);
v___x_157_ = lean_st_ref_put(v_finished_150_, v___x_156_);
if (v___y_154_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_apply_1(v_lose_148_, lean_box(0));
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec_ref(v_lose_148_);
v___x_159_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0));
v___x_160_ = lean_io_promise_resolve(v___x_159_, v_promise_151_);
return v___x_160_;
}
}
}
}
LEAN_EXPORT void l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_w_147_ = stack[0].m_obj;
lean_object* v_lose_148_ = stack[1].m_obj;
lean_object* v_res_164_;
v_res_164_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(v_w_147_, v_lose_148_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___boxed(lean_object* v_w_165_, lean_object* v_lose_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(v_w_165_, v_lose_166_);
lean_dec_ref(v_w_165_);
return v_res_168_;
}
}
lean_object* l_Std_Async_Sleep_selector___lam__0(lean_object* v_x_173_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_a_175_ = lean_ctor_get(v_x_173_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v_x_173_);
if (v_isSharedCheck_183_ == 0)
{
v___x_177_ = v_x_173_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v_x_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_182_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
}
else
{
lean_object* v___x_184_; 
lean_dec_ref_known(v_x_173_, 1);
v___x_184_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__0___closed__1));
return v___x_184_;
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_selector___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_173_ = stack[0].m_obj;
lean_object* v_res_185_;
v_res_185_ = l_Std_Async_Sleep_selector___lam__0(v_x_173_);
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__0___boxed(lean_object* v_x_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_Async_Sleep_selector___lam__0(v_x_186_);
return v_res_188_;
}
}
lean_object* l_Std_Async_Sleep_selector___lam__1(lean_object* v_s_189_){
_start:
{
lean_object* v_val_192_; lean_object* v___x_194_; 
v___x_194_ = lean_uv_timer_cancel(v_s_189_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 1);
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
v_val_192_ = v___x_200_;
goto v___jp_191_;
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_194_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_194_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 0);
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
v_val_192_ = v___x_208_;
goto v___jp_191_;
}
}
}
v___jp_191_:
{
lean_object* v___x_193_; 
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v_val_192_);
return v___x_193_;
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_selector___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_189_ = stack[0].m_obj;
lean_object* v_res_211_;
v_res_211_ = l_Std_Async_Sleep_selector___lam__1(v_s_189_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__1___boxed(lean_object* v_s_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Async_Sleep_selector___lam__1(v_s_212_);
lean_dec(v_s_212_);
return v_res_214_;
}
}
lean_object* l_Std_Async_Sleep_selector___lam__2(lean_object* v___x_215_){
_start:
{
return v___x_215_;
}
}
LEAN_EXPORT void l_Std_Async_Sleep_selector___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_215_ = stack[0].m_obj;
lean_object* v_res_217_;
v_res_217_ = l_Std_Async_Sleep_selector___lam__2(v___x_215_);
stack->m_obj
 = v_res_217_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__2___boxed(lean_object* v___x_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Async_Sleep_selector___lam__2(v___x_218_);
return v_res_220_;
}
}
lean_object* l_Std_Async_Sleep_selector___lam__3(lean_object* v_waiter_223_, lean_object* v_x_224_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_object* v___x_226_; 
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
lean_object* v___f_227_; lean_object* v___x_228_; 
v___f_227_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__3___closed__0));
v___x_228_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(v_waiter_223_, v___f_227_);
return v___x_228_;
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_selector___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_waiter_223_ = stack[0].m_obj;
lean_object* v_x_224_ = stack[1].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Std_Async_Sleep_selector___lam__3(v_waiter_223_, v_x_224_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__3___boxed(lean_object* v_waiter_230_, lean_object* v_x_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Std_Async_Sleep_selector___lam__3(v_waiter_230_, v_x_231_);
lean_dec(v_x_231_);
lean_dec_ref(v_waiter_230_);
return v_res_233_;
}
}
lean_object* l_Std_Async_Sleep_selector___lam__4(lean_object* v___f_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_245_; 
lean_dec_ref(v___f_234_);
v_a_237_ = lean_ctor_get(v_x_235_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_x_235_);
if (v_isSharedCheck_245_ == 0)
{
v___x_239_ = v_x_235_;
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v_x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_245_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; 
v___x_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
}
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_258_; 
v_a_246_ = lean_ctor_get(v_x_235_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v_x_235_);
if (v_isSharedCheck_258_ == 0)
{
v___x_248_ = v_x_235_;
v_isShared_249_ = v_isSharedCheck_258_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v_x_235_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_258_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_250_ = lean_io_promise_result_opt(v_a_246_);
lean_dec(v_a_246_);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = 0;
v___x_253_ = l_BaseIO_chainTask___redArg(v___x_250_, v___f_234_, v___x_251_, v___x_252_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_253_);
v___x_255_ = v___x_248_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_257_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_256_; 
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
return v___x_256_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_selector___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_234_ = stack[0].m_obj;
lean_object* v_x_235_ = stack[1].m_obj;
lean_object* v_res_259_;
v_res_259_ = l_Std_Async_Sleep_selector___lam__4(v___f_234_, v_x_235_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__4___boxed(lean_object* v___f_260_, lean_object* v_x_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Std_Async_Sleep_selector___lam__4(v___f_260_, v_x_261_);
return v_res_263_;
}
}
lean_object* l_Std_Async_Sleep_selector___lam__5(lean_object* v_s_264_, lean_object* v_waiter_265_){
_start:
{
lean_object* v___f_267_; lean_object* v___f_268_; lean_object* v___x_269_; uint8_t v___x_270_; lean_object* v_val_272_; lean_object* v___x_275_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_267_, 0, v_waiter_265_);
v___f_268_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_268_, 0, v___f_267_);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = 0;
v___x_275_ = lean_uv_timer_next(v_s_264_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
lean_ctor_set_tag(v___x_278_, 1);
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
v_val_272_ = v___x_281_;
goto v___jp_271_;
}
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
v_a_284_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_275_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_275_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set_tag(v___x_286_, 0);
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
v_val_272_ = v___x_289_;
goto v___jp_271_;
}
}
}
v___jp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v_val_272_);
v___x_274_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_269_, v___x_270_, v___x_273_, v___f_268_);
return v___x_274_;
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_selector___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_264_ = stack[0].m_obj;
lean_object* v_waiter_265_ = stack[1].m_obj;
lean_object* v_res_292_;
v_res_292_ = l_Std_Async_Sleep_selector___lam__5(v_s_264_, v_waiter_265_);
stack->m_obj
 = v_res_292_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__5___boxed(lean_object* v_s_293_, lean_object* v_waiter_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Async_Sleep_selector___lam__5(v_s_293_, v_waiter_294_);
lean_dec(v_s_293_);
return v_res_296_;
}
}
lean_object* l_Std_Async_Sleep_selector___lam__6(lean_object* v___f_303_, lean_object* v_s_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v___f_303_);
v_a_307_ = lean_ctor_get(v_x_305_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_x_305_);
if (v_isSharedCheck_315_ == 0)
{
v___x_309_ = v_x_305_;
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v_x_305_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_315_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_307_);
v___x_312_ = v_reuseFailAlloc_314_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; 
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_337_; 
v_a_316_ = lean_ctor_get(v_x_305_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_305_);
if (v_isSharedCheck_337_ == 0)
{
v___x_318_ = v_x_305_;
v_isShared_319_ = v_isSharedCheck_337_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v_x_305_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_337_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; 
v___x_320_ = lean_unbox(v_a_316_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v_val_323_; lean_object* v___x_327_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_uv_timer_cancel(v_s_304_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_330_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v_a_328_);
v___x_330_ = v___x_318_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
v_val_323_ = v___x_330_;
goto v___jp_322_;
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; 
v_a_332_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_327_, 1);
if (v_isShared_319_ == 0)
{
lean_ctor_set_tag(v___x_318_, 0);
lean_ctor_set(v___x_318_, 0, v_a_332_);
v___x_334_ = v___x_318_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
v_val_323_ = v___x_334_;
goto v___jp_322_;
}
}
v___jp_322_:
{
lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v_val_323_);
v___x_325_ = lean_unbox(v_a_316_);
lean_dec(v_a_316_);
v___x_326_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_321_, v___x_325_, v___x_324_, v___f_303_);
return v___x_326_;
}
}
else
{
lean_object* v___x_336_; 
lean_del_object(v___x_318_);
lean_dec(v_a_316_);
lean_dec_ref(v___f_303_);
v___x_336_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__6___closed__2));
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_selector___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_303_ = stack[0].m_obj;
lean_object* v_s_304_ = stack[1].m_obj;
lean_object* v_x_305_ = stack[2].m_obj;
lean_object* v_res_338_;
v_res_338_ = l_Std_Async_Sleep_selector___lam__6(v___f_303_, v_s_304_, v_x_305_);
stack->m_obj
 = v_res_338_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__6___boxed(lean_object* v___f_339_, lean_object* v_s_340_, lean_object* v_x_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_Async_Sleep_selector___lam__6(v___f_339_, v_s_340_, v_x_341_);
lean_dec(v_s_340_);
return v_res_343_;
}
}
lean_object* l_Std_Async_Sleep_selector___lam__7(lean_object* v___f_344_, lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_355_; 
lean_dec_ref(v___f_344_);
v_a_347_ = lean_ctor_get(v_x_345_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_345_);
if (v_isSharedCheck_355_ == 0)
{
v___x_349_ = v_x_345_;
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v_x_345_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_354_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; 
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_369_; 
v_a_356_ = lean_ctor_get(v_x_345_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v_x_345_);
if (v_isSharedCheck_369_ == 0)
{
v___x_358_ = v_x_345_;
v_isShared_359_ = v_isSharedCheck_369_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v_x_345_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_369_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; uint8_t v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = 0;
v___x_362_ = l_IO_Promise_isResolved___redArg(v_a_356_);
lean_dec(v_a_356_);
v___x_363_ = lean_box(v___x_362_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_363_);
v___x_365_ = v___x_358_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_368_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
v___x_367_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_360_, v___x_361_, v___x_366_, v___f_344_);
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_selector___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_344_ = stack[0].m_obj;
lean_object* v_x_345_ = stack[1].m_obj;
lean_object* v_res_370_;
v_res_370_ = l_Std_Async_Sleep_selector___lam__7(v___f_344_, v_x_345_);
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__7___boxed(lean_object* v___f_371_, lean_object* v_x_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Std_Async_Sleep_selector___lam__7(v___f_371_, v_x_372_);
return v_res_374_;
}
}
lean_object* l_Std_Async_Sleep_selector___lam__8(lean_object* v___f_375_, lean_object* v_s_376_){
_start:
{
lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v_val_381_; lean_object* v___x_384_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = 0;
v___x_384_ = lean_uv_timer_next(v_s_376_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set_tag(v___x_387_, 1);
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
v_val_381_ = v___x_390_;
goto v___jp_380_;
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_a_393_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_384_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_384_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 0);
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
v_val_381_ = v___x_398_;
goto v___jp_380_;
}
}
}
v___jp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_382_, 0, v_val_381_);
v___x_383_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_378_, v___x_379_, v___x_382_, v___f_375_);
return v___x_383_;
}
}
}
LEAN_EXPORT void l_Std_Async_Sleep_selector___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_375_ = stack[0].m_obj;
lean_object* v_s_376_ = stack[1].m_obj;
lean_object* v_res_401_;
v_res_401_ = l_Std_Async_Sleep_selector___lam__8(v___f_375_, v_s_376_);
stack->m_obj
 = v_res_401_;
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__8___boxed(lean_object* v___f_402_, lean_object* v_s_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Async_Sleep_selector___lam__8(v___f_402_, v_s_403_);
lean_dec(v_s_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector(lean_object* v_s_407_){
_start:
{
lean_object* v___f_408_; lean_object* v___f_409_; lean_object* v___f_410_; lean_object* v___f_411_; lean_object* v___f_412_; lean_object* v___f_413_; lean_object* v___x_414_; 
v___f_408_ = ((lean_object*)(l_Std_Async_Sleep_selector___closed__0));
lean_inc_n(v_s_407_, 3);
v___f_409_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__1___boxed), 2, 1);
lean_closure_set(v___f_409_, 0, v_s_407_);
v___f_410_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__5___boxed), 3, 1);
lean_closure_set(v___f_410_, 0, v_s_407_);
v___f_411_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_411_, 0, v___f_408_);
lean_closure_set(v___f_411_, 1, v_s_407_);
v___f_412_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_412_, 0, v___f_411_);
v___f_413_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__8___boxed), 3, 2);
lean_closure_set(v___f_413_, 0, v___f_412_);
lean_closure_set(v___f_413_, 1, v_s_407_);
v___x_414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_414_, 0, v___f_413_);
lean_ctor_set(v___x_414_, 1, v___f_410_);
lean_ctor_set(v___x_414_, 2, v___f_409_);
return v___x_414_;
}
}
lean_object* l_Std_Async_sleep___lam__1(lean_object* v_x_415_){
_start:
{
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_425_; 
v_a_417_ = lean_ctor_get(v_x_415_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_425_ == 0)
{
v___x_419_ = v_x_415_;
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v_x_415_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_424_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
lean_object* v___x_423_; 
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_455_; 
v_a_426_ = lean_ctor_get(v_x_415_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v_x_415_);
if (v_isSharedCheck_455_ == 0)
{
v___x_428_ = v_x_415_;
v_isShared_429_ = v_isSharedCheck_455_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v_x_415_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_455_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___f_430_; lean_object* v___x_431_; 
v___f_430_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_431_ = lean_uv_timer_next(v_a_426_);
lean_dec(v_a_426_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_443_; 
lean_del_object(v___x_428_);
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_443_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_436_ = lean_io_promise_result_opt(v_a_432_);
lean_dec(v_a_432_);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = 0;
v___x_439_ = lean_task_map(v___f_430_, v___x_436_, v___x_437_, v___x_438_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 1);
lean_ctor_set(v___x_434_, 0, v___x_439_);
v___x_441_ = v___x_434_;
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
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_454_; 
v_a_444_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_454_ == 0)
{
v___x_446_ = v___x_431_;
v_isShared_447_ = v_isSharedCheck_454_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_431_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_454_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 0);
lean_ctor_set(v___x_428_, 0, v_a_444_);
v___x_449_ = v___x_428_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_453_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_451_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 0);
lean_ctor_set(v___x_446_, 0, v___x_449_);
v___x_451_ = v___x_446_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_sleep___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_415_ = stack[0].m_obj;
lean_object* v_res_456_;
v_res_456_ = l_Std_Async_sleep___lam__1(v_x_415_);
stack->m_obj
 = v_res_456_;
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___lam__1___boxed(lean_object* v_x_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_Async_sleep___lam__1(v_x_457_);
return v_res_459_;
}
}
lean_object* l_Std_Async_sleep(lean_object* v_duration_461_){
_start:
{
lean_object* v___f_463_; lean_object* v___f_464_; lean_object* v___x_465_; uint8_t v___x_466_; lean_object* v_val_468_; uint64_t v___x_472_; lean_object* v___x_473_; 
v___f_463_ = ((lean_object*)(l_Std_Async_sleep___closed__0));
v___f_464_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = 0;
v___x_472_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_461_);
v___x_473_ = lean_uv_timer_mk(v___x_472_, v___x_466_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set_tag(v___x_476_, 1);
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
v_val_468_ = v___x_479_;
goto v___jp_467_;
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_a_482_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_473_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_473_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
lean_ctor_set_tag(v___x_484_, 0);
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
v_val_468_ = v___x_487_;
goto v___jp_467_;
}
}
}
v___jp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_val_468_);
v___x_470_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_465_, v___x_466_, v___x_469_, v___f_464_);
v___x_471_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_465_, v___x_466_, v___x_470_, v___f_463_);
return v___x_471_;
}
}
}
LEAN_EXPORT void l_Std_Async_sleep_0interp(lean_interpreter_value* stack)
{
lean_object* v_duration_461_ = stack[0].m_obj;
lean_object* v_res_490_;
v_res_490_ = l_Std_Async_sleep(v_duration_461_);
stack->m_obj
 = v_res_490_;
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___boxed(lean_object* v_duration_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_Async_sleep(v_duration_491_);
lean_dec(v_duration_491_);
return v_res_493_;
}
}
lean_object* l_Std_Async_Selector_sleep___lam__0(lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_494_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
v_a_496_ = lean_ctor_get(v_x_494_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v_x_494_);
if (v_isSharedCheck_504_ == 0)
{
v___x_498_ = v_x_494_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v_x_494_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_496_);
v___x_501_ = v_reuseFailAlloc_503_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_502_; 
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_514_; 
v_a_505_ = lean_ctor_get(v_x_494_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_x_494_);
if (v_isSharedCheck_514_ == 0)
{
v___x_507_ = v_x_494_;
v_isShared_508_ = v_isSharedCheck_514_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v_x_494_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_514_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = l_Std_Async_Sleep_selector(v_a_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_509_);
v___x_511_ = v___x_507_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_513_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_512_; 
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Selector_sleep___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_494_ = stack[0].m_obj;
lean_object* v_res_515_;
v_res_515_ = l_Std_Async_Selector_sleep___lam__0(v_x_494_);
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___lam__0___boxed(lean_object* v_x_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Std_Async_Selector_sleep___lam__0(v_x_516_);
return v_res_518_;
}
}
lean_object* l_Std_Async_Selector_sleep(lean_object* v_duration_520_){
_start:
{
lean_object* v___f_522_; lean_object* v___f_523_; lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v_val_527_; uint64_t v___x_531_; lean_object* v___x_532_; 
v___f_522_ = ((lean_object*)(l_Std_Async_Selector_sleep___closed__0));
v___f_523_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = 0;
v___x_531_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_520_);
v___x_532_ = lean_uv_timer_mk(v___x_531_, v___x_525_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 1);
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
v_val_527_ = v___x_538_;
goto v___jp_526_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
v_a_541_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_532_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_532_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 0);
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
v_val_527_ = v___x_546_;
goto v___jp_526_;
}
}
}
v___jp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v_val_527_);
v___x_529_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_524_, v___x_525_, v___x_528_, v___f_523_);
v___x_530_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_524_, v___x_525_, v___x_529_, v___f_522_);
return v___x_530_;
}
}
}
LEAN_EXPORT void l_Std_Async_Selector_sleep_0interp(lean_interpreter_value* stack)
{
lean_object* v_duration_520_ = stack[0].m_obj;
lean_object* v_res_549_;
v_res_549_ = l_Std_Async_Selector_sleep(v_duration_520_);
stack->m_obj
 = v_res_549_;
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___boxed(lean_object* v_duration_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Async_Selector_sleep(v_duration_550_);
lean_dec(v_duration_550_);
return v_res_552_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__12(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__10));
v___x_580_ = l_Lean_mkAtom(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__13(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__12, &l_Std_Async_Interval_mk___auto__1___closed__12_once, _init_l_Std_Async_Interval_mk___auto__1___closed__12);
v___x_582_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_583_ = lean_array_push(v___x_582_, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__17(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__16));
v___x_595_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_596_ = lean_array_push(v___x_595_, v___x_594_);
return v___x_596_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__18(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__17, &l_Std_Async_Interval_mk___auto__1___closed__17_once, _init_l_Std_Async_Interval_mk___auto__1___closed__17);
v___x_598_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__15));
v___x_599_ = lean_box(2);
v___x_600_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___x_598_);
lean_ctor_set(v___x_600_, 2, v___x_597_);
return v___x_600_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__19(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__18, &l_Std_Async_Interval_mk___auto__1___closed__18_once, _init_l_Std_Async_Interval_mk___auto__1___closed__18);
v___x_602_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__13, &l_Std_Async_Interval_mk___auto__1___closed__13_once, _init_l_Std_Async_Interval_mk___auto__1___closed__13);
v___x_603_ = lean_array_push(v___x_602_, v___x_601_);
return v___x_603_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__20(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_604_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__19, &l_Std_Async_Interval_mk___auto__1___closed__19_once, _init_l_Std_Async_Interval_mk___auto__1___closed__19);
v___x_605_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__11));
v___x_606_ = lean_box(2);
v___x_607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
lean_ctor_set(v___x_607_, 2, v___x_604_);
return v___x_607_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__21(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__20, &l_Std_Async_Interval_mk___auto__1___closed__20_once, _init_l_Std_Async_Interval_mk___auto__1___closed__20);
v___x_609_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_610_ = lean_array_push(v___x_609_, v___x_608_);
return v___x_610_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__22(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_611_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__21, &l_Std_Async_Interval_mk___auto__1___closed__21_once, _init_l_Std_Async_Interval_mk___auto__1___closed__21);
v___x_612_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__9));
v___x_613_ = lean_box(2);
v___x_614_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
lean_ctor_set(v___x_614_, 2, v___x_611_);
return v___x_614_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__23(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__22, &l_Std_Async_Interval_mk___auto__1___closed__22_once, _init_l_Std_Async_Interval_mk___auto__1___closed__22);
v___x_616_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_617_ = lean_array_push(v___x_616_, v___x_615_);
return v___x_617_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__24(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_618_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__23, &l_Std_Async_Interval_mk___auto__1___closed__23_once, _init_l_Std_Async_Interval_mk___auto__1___closed__23);
v___x_619_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__7));
v___x_620_ = lean_box(2);
v___x_621_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
lean_ctor_set(v___x_621_, 2, v___x_618_);
return v___x_621_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__25(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__24, &l_Std_Async_Interval_mk___auto__1___closed__24_once, _init_l_Std_Async_Interval_mk___auto__1___closed__24);
v___x_623_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_624_ = lean_array_push(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__26(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_625_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__25, &l_Std_Async_Interval_mk___auto__1___closed__25_once, _init_l_Std_Async_Interval_mk___auto__1___closed__25);
v___x_626_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__4));
v___x_627_ = lean_box(2);
v___x_628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
lean_ctor_set(v___x_628_, 2, v___x_625_);
return v___x_628_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1(void){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__26, &l_Std_Async_Interval_mk___auto__1___closed__26_once, _init_l_Std_Async_Interval_mk___auto__1___closed__26);
return v___x_629_;
}
}
lean_object* l_Std_Async_Interval_mk___redArg(lean_object* v_duration_630_){
_start:
{
uint64_t v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_630_);
v___x_633_ = 1;
v___x_634_ = lean_uv_timer_mk(v___x_632_, v___x_633_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
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
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_a_643_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_634_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_634_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Interval_mk___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_duration_630_ = stack[0].m_obj;
lean_object* v_res_651_;
v_res_651_ = l_Std_Async_Interval_mk___redArg(v_duration_630_);
stack->m_obj
 = v_res_651_;
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___redArg___boxed(lean_object* v_duration_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Async_Interval_mk___redArg(v_duration_652_);
lean_dec(v_duration_652_);
return v_res_654_;
}
}
lean_object* l_Std_Async_Interval_mk(lean_object* v_duration_655_, lean_object* v_x_656_){
_start:
{
uint64_t v___x_658_; uint8_t v___x_659_; lean_object* v___x_660_; 
v___x_658_ = l___private_Std_Async_Timer_0__Std_Async_timeoutOf(v_duration_655_);
v___x_659_ = 1;
v___x_660_ = lean_uv_timer_mk(v___x_658_, v___x_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
v_a_669_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_660_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_660_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
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
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Interval_mk_0interp(lean_interpreter_value* stack)
{
lean_object* v_duration_655_ = stack[0].m_obj;
lean_object* v_res_677_;
v_res_677_ = l_Std_Async_Interval_mk(v_duration_655_, lean_box(0));
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___boxed(lean_object* v_duration_678_, lean_object* v_x_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_Async_Interval_mk(v_duration_678_, v_x_679_);
lean_dec(v_duration_678_);
return v_res_681_;
}
}
lean_object* l_Std_Async_Interval_tick(lean_object* v_i_682_){
_start:
{
lean_object* v___f_684_; lean_object* v___x_685_; 
v___f_684_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_685_ = lean_uv_timer_next(v_i_682_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_697_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_697_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_697_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_697_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v___x_690_ = lean_io_promise_result_opt(v_a_686_);
lean_dec(v_a_686_);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = 0;
v___x_693_ = lean_task_map(v___f_684_, v___x_690_, v___x_691_, v___x_692_);
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 1);
lean_ctor_set(v___x_688_, 0, v___x_693_);
v___x_695_ = v___x_688_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_706_; 
v_a_698_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_706_ == 0)
{
v___x_700_ = v___x_685_;
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_685_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 0);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_705_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; 
v___x_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
return v___x_704_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Async_Interval_tick_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_682_ = stack[0].m_obj;
lean_object* v_res_707_;
v_res_707_ = l_Std_Async_Interval_tick(v_i_682_);
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_tick___boxed(lean_object* v_i_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_Async_Interval_tick(v_i_708_);
lean_dec(v_i_708_);
return v_res_710_;
}
}
lean_object* l_Std_Async_Interval_reset(lean_object* v_i_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_uv_timer_reset(v_i_711_);
return v___x_713_;
}
}
LEAN_EXPORT void l_Std_Async_Interval_reset_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_711_ = stack[0].m_obj;
lean_object* v_res_714_;
v_res_714_ = l_Std_Async_Interval_reset(v_i_711_);
stack->m_obj
 = v_res_714_;
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_reset___boxed(lean_object* v_i_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Std_Async_Interval_reset(v_i_715_);
lean_dec(v_i_715_);
return v_res_717_;
}
}
lean_object* l_Std_Async_Interval_stop(lean_object* v_i_718_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = lean_uv_timer_stop(v_i_718_);
return v___x_720_;
}
}
LEAN_EXPORT void l_Std_Async_Interval_stop_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_718_ = stack[0].m_obj;
lean_object* v_res_721_;
v_res_721_ = l_Std_Async_Interval_stop(v_i_718_);
stack->m_obj
 = v_res_721_;
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_stop___boxed(lean_object* v_i_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Std_Async_Interval_stop(v_i_722_);
lean_dec(v_i_722_);
return v_res_724_;
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

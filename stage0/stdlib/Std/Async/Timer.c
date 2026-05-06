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
lean_object* lean_uv_timer_next(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_promise_result_opt(lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_uv_timer_reset(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_io_promise_resolve(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_uv_timer_mk(uint64_t, uint8_t);
lean_object* l_BaseIO_chainTask___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_IO_Promise_isResolved___redArg(lean_object*);
lean_object* lean_uv_timer_stop(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___lam__0(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v_a_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_a_3_ = lean_ctor_get(v_x_1_, 0);
v_isSharedCheck_11_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_x_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_a_3_);
lean_dec(v_x_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_8_; 
if (v_isShared_6_ == 0)
{
v___x_8_ = v___x_5_;
goto v_reusejp_7_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v_a_3_);
v___x_8_ = v_reuseFailAlloc_10_;
goto v_reusejp_7_;
}
v_reusejp_7_:
{
lean_object* v___x_9_; 
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
}
else
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_20_; 
v_a_12_ = lean_ctor_get(v_x_1_, 0);
v_isSharedCheck_20_ = !lean_is_exclusive(v_x_1_);
if (v_isSharedCheck_20_ == 0)
{
v___x_14_ = v_x_1_;
v_isShared_15_ = v_isSharedCheck_20_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v_x_1_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_20_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_19_; 
v_reuseFailAlloc_19_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_19_, 0, v_a_12_);
v___x_17_ = v_reuseFailAlloc_19_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
lean_object* v___x_18_; 
v___x_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
return v___x_18_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___lam__0___boxed(lean_object* v_x_21_, lean_object* v___y_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Std_Async_Sleep_mk___lam__0(v_x_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk(lean_object* v_duration_25_){
_start:
{
lean_object* v___f_27_; lean_object* v_val_29_; lean_object* v___x_34_; uint64_t v___x_35_; uint8_t v___x_36_; lean_object* v___x_37_; 
v___f_27_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_34_ = l_Int_toNat(v_duration_25_);
v___x_35_ = lean_uint64_of_nat(v___x_34_);
lean_dec(v___x_34_);
v___x_36_ = 0;
v___x_37_ = lean_uv_timer_mk(v___x_35_, v___x_36_);
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_37_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_37_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set_tag(v___x_40_, 1);
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
v_val_29_ = v___x_43_;
goto v___jp_28_;
}
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_37_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_37_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 0);
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
v_val_29_ = v___x_51_;
goto v___jp_28_;
}
}
}
v___jp_28_:
{
lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; lean_object* v___x_33_; 
v___x_30_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_30_, 0, v_val_29_);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = 0;
v___x_33_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_31_, v___x_32_, v___x_30_, v___f_27_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___boxed(lean_object* v_duration_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Std_Async_Sleep_mk(v_duration_54_);
lean_dec(v_duration_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait___lam__0(lean_object* v___x_57_, lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_mk_io_user_error(v___x_57_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
else
{
lean_object* v_val_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
lean_dec_ref(v___x_57_);
v_val_61_ = lean_ctor_get(v_x_58_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v_x_58_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_val_61_);
lean_dec(v_x_58_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_val_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait(lean_object* v_s_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_uv_timer_next(v_s_72_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_87_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_87_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_87_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_87_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___f_79_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_80_ = lean_io_promise_result_opt(v_a_75_);
lean_dec(v_a_75_);
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = 0;
v___x_83_ = lean_task_map(v___f_79_, v___x_80_, v___x_81_, v___x_82_);
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 1);
lean_ctor_set(v___x_77_, 0, v___x_83_);
v___x_85_ = v___x_77_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
else
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_a_88_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v___x_74_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_74_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 0);
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_95_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait___boxed(lean_object* v_s_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_Async_Sleep_wait(v_s_97_);
lean_dec(v_s_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_reset(lean_object* v_s_100_){
_start:
{
lean_object* v_val_103_; lean_object* v___x_105_; 
v___x_105_ = lean_uv_timer_reset(v_s_100_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
lean_ctor_set_tag(v___x_108_, 1);
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
v_val_103_ = v___x_111_;
goto v___jp_102_;
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_105_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_105_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 0);
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v_val_103_ = v___x_119_;
goto v___jp_102_;
}
}
}
v___jp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v_val_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_reset___boxed(lean_object* v_s_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Std_Async_Sleep_reset(v_s_122_);
lean_dec(v_s_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_stop(lean_object* v_s_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_uv_timer_stop(v_s_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_stop___boxed(lean_object* v_s_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_Async_Sleep_stop(v_s_128_);
lean_dec(v_s_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(lean_object* v_w_133_, lean_object* v_lose_134_){
_start:
{
lean_object* v_finished_136_; lean_object* v_promise_137_; lean_object* v___x_138_; uint8_t v___y_140_; uint8_t v___x_147_; 
v_finished_136_ = lean_ctor_get(v_w_133_, 0);
v_promise_137_ = lean_ctor_get(v_w_133_, 1);
v___x_138_ = lean_st_ref_take(v_finished_136_);
v___x_147_ = lean_unbox(v___x_138_);
lean_dec(v___x_138_);
if (v___x_147_ == 0)
{
uint8_t v___x_148_; 
v___x_148_ = 1;
v___y_140_ = v___x_148_;
goto v___jp_139_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
v___y_140_ = v___x_149_;
goto v___jp_139_;
}
v___jp_139_:
{
uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_141_ = 1;
v___x_142_ = lean_box(v___x_141_);
v___x_143_ = lean_st_ref_set(v_finished_136_, v___x_142_);
if (v___y_140_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_apply_1(v_lose_134_, lean_box(0));
return v___x_144_;
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec_ref(v_lose_134_);
v___x_145_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0));
v___x_146_ = lean_io_promise_resolve(v___x_145_, v_promise_137_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___boxed(lean_object* v_w_150_, lean_object* v_lose_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(v_w_150_, v_lose_151_);
lean_dec_ref(v_w_150_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__0(lean_object* v_x_158_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_168_; 
v_a_160_ = lean_ctor_get(v_x_158_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_168_ == 0)
{
v___x_162_ = v_x_158_;
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v_x_158_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_165_; 
if (v_isShared_163_ == 0)
{
v___x_165_ = v___x_162_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_160_);
v___x_165_ = v_reuseFailAlloc_167_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; 
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
}
else
{
lean_object* v___x_169_; 
lean_dec_ref(v_x_158_);
v___x_169_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__0___closed__1));
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__0___boxed(lean_object* v_x_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_Async_Sleep_selector___lam__0(v_x_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__1(lean_object* v_s_173_){
_start:
{
lean_object* v_val_176_; lean_object* v___x_178_; 
v___x_178_ = lean_uv_timer_cancel(v_s_173_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 1);
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
v_val_176_ = v___x_184_;
goto v___jp_175_;
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_178_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_178_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 0);
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
v_val_176_ = v___x_192_;
goto v___jp_175_;
}
}
}
v___jp_175_:
{
lean_object* v___x_177_; 
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v_val_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__1___boxed(lean_object* v_s_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Std_Async_Sleep_selector___lam__1(v_s_195_);
lean_dec(v_s_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__2(lean_object* v___x_198_){
_start:
{
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__2___boxed(lean_object* v___x_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Async_Sleep_selector___lam__2(v___x_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__3(lean_object* v_waiter_205_, lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_206_) == 0)
{
lean_object* v___x_208_; 
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
lean_object* v___f_209_; lean_object* v___x_210_; 
v___f_209_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__3___closed__0));
v___x_210_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(v_waiter_205_, v___f_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__3___boxed(lean_object* v_waiter_211_, lean_object* v_x_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Async_Sleep_selector___lam__3(v_waiter_211_, v_x_212_);
lean_dec(v_x_212_);
lean_dec_ref(v_waiter_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__4(lean_object* v___f_215_, lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
lean_dec_ref(v___f_215_);
v_a_218_ = lean_ctor_get(v_x_216_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_216_);
if (v_isSharedCheck_226_ == 0)
{
v___x_220_ = v_x_216_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v_x_216_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_225_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_object* v___x_224_; 
v___x_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
return v___x_224_;
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_239_; 
v_a_227_ = lean_ctor_get(v_x_216_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_216_);
if (v_isSharedCheck_239_ == 0)
{
v___x_229_ = v_x_216_;
v_isShared_230_ = v_isSharedCheck_239_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v_x_216_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_239_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_231_ = lean_io_promise_result_opt(v_a_227_);
lean_dec(v_a_227_);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = 0;
v___x_234_ = l_BaseIO_chainTask___redArg(v___x_231_, v___f_215_, v___x_232_, v___x_233_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_234_);
v___x_236_ = v___x_229_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_238_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_237_; 
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__4___boxed(lean_object* v___f_240_, lean_object* v_x_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Std_Async_Sleep_selector___lam__4(v___f_240_, v_x_241_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__5(lean_object* v_s_244_, lean_object* v_waiter_245_){
_start:
{
lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v_val_250_; lean_object* v___x_255_; 
v___f_247_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_247_, 0, v_waiter_245_);
v___f_248_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_248_, 0, v___f_247_);
v___x_255_ = lean_uv_timer_next(v_s_244_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 1);
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
v_val_250_ = v___x_261_;
goto v___jp_249_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
v_a_264_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_255_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_255_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
lean_ctor_set_tag(v___x_266_, 0);
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
v_val_250_ = v___x_269_;
goto v___jp_249_;
}
}
}
v___jp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; 
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v_val_250_);
v___x_252_ = lean_unsigned_to_nat(0u);
v___x_253_ = 0;
v___x_254_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_252_, v___x_253_, v___x_251_, v___f_248_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__5___boxed(lean_object* v_s_272_, lean_object* v_waiter_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_Async_Sleep_selector___lam__5(v_s_272_, v_waiter_273_);
lean_dec(v_s_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__6(lean_object* v___f_282_, lean_object* v_s_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_294_; 
lean_dec_ref(v___f_282_);
v_a_286_ = lean_ctor_get(v_x_284_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_294_ == 0)
{
v___x_288_ = v_x_284_;
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v_x_284_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_294_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_293_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; 
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_316_; 
v_a_295_ = lean_ctor_get(v_x_284_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v_x_284_);
if (v_isSharedCheck_316_ == 0)
{
v___x_297_ = v_x_284_;
v_isShared_298_ = v_isSharedCheck_316_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v_x_284_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_316_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v_val_300_; uint8_t v___x_305_; 
v___x_305_ = lean_unbox(v_a_295_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
v___x_306_ = lean_uv_timer_cancel(v_s_283_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref(v___x_306_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v_a_307_);
v___x_309_ = v___x_297_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
v_val_300_ = v___x_309_;
goto v___jp_299_;
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; 
v_a_311_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_311_);
lean_dec_ref(v___x_306_);
if (v_isShared_298_ == 0)
{
lean_ctor_set_tag(v___x_297_, 0);
lean_ctor_set(v___x_297_, 0, v_a_311_);
v___x_313_ = v___x_297_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
v_val_300_ = v___x_313_;
goto v___jp_299_;
}
}
}
else
{
lean_object* v___x_315_; 
lean_del_object(v___x_297_);
lean_dec(v_a_295_);
lean_dec_ref(v___f_282_);
v___x_315_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__6___closed__2));
return v___x_315_;
}
v___jp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; 
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v_val_300_);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_unbox(v_a_295_);
lean_dec(v_a_295_);
v___x_304_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_302_, v___x_303_, v___x_301_, v___f_282_);
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__6___boxed(lean_object* v___f_317_, lean_object* v_s_318_, lean_object* v_x_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Std_Async_Sleep_selector___lam__6(v___f_317_, v_s_318_, v_x_319_);
lean_dec(v_s_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__7(lean_object* v___f_322_, lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v___f_322_);
v_a_325_ = lean_ctor_get(v_x_323_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_333_ == 0)
{
v___x_327_ = v_x_323_;
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v_x_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_332_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
}
else
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_347_; 
v_a_334_ = lean_ctor_get(v_x_323_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_347_ == 0)
{
v___x_336_ = v_x_323_;
v_isShared_337_ = v_isSharedCheck_347_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v_x_323_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_347_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_338_ = l_IO_Promise_isResolved___redArg(v_a_334_);
lean_dec(v_a_334_);
v___x_339_ = lean_box(v___x_338_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v___x_339_);
v___x_341_ = v___x_336_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_346_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; 
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = 0;
v___x_345_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_343_, v___x_344_, v___x_342_, v___f_322_);
return v___x_345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__7___boxed(lean_object* v___f_348_, lean_object* v_x_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Std_Async_Sleep_selector___lam__7(v___f_348_, v_x_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__8(lean_object* v___f_352_, lean_object* v_s_353_){
_start:
{
lean_object* v_val_356_; lean_object* v___x_361_; 
v___x_361_ = lean_uv_timer_next(v_s_353_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 1);
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
v_val_356_ = v___x_367_;
goto v___jp_355_;
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
v_a_370_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_361_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_361_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 0);
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
v_val_356_ = v___x_375_;
goto v___jp_355_;
}
}
}
v___jp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; 
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v_val_356_);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = 0;
v___x_360_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_358_, v___x_359_, v___x_357_, v___f_352_);
return v___x_360_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__8___boxed(lean_object* v___f_378_, lean_object* v_s_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_Async_Sleep_selector___lam__8(v___f_378_, v_s_379_);
lean_dec(v_s_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector(lean_object* v_s_383_){
_start:
{
lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___f_386_; lean_object* v___f_387_; lean_object* v___f_388_; lean_object* v___f_389_; lean_object* v___x_390_; 
v___f_384_ = ((lean_object*)(l_Std_Async_Sleep_selector___closed__0));
lean_inc_n(v_s_383_, 3);
v___f_385_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__1___boxed), 2, 1);
lean_closure_set(v___f_385_, 0, v_s_383_);
v___f_386_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__5___boxed), 3, 1);
lean_closure_set(v___f_386_, 0, v_s_383_);
v___f_387_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_387_, 0, v___f_384_);
lean_closure_set(v___f_387_, 1, v_s_383_);
v___f_388_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_388_, 0, v___f_387_);
v___f_389_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__8___boxed), 3, 2);
lean_closure_set(v___f_389_, 0, v___f_388_);
lean_closure_set(v___f_389_, 1, v_s_383_);
v___x_390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_390_, 0, v___f_389_);
lean_ctor_set(v___x_390_, 1, v___f_386_);
lean_ctor_set(v___x_390_, 2, v___f_385_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___lam__1(lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_a_393_ = lean_ctor_get(v_x_391_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_x_391_);
if (v_isSharedCheck_401_ == 0)
{
v___x_395_ = v_x_391_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v_x_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_400_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_431_; 
v_a_402_ = lean_ctor_get(v_x_391_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_391_);
if (v_isSharedCheck_431_ == 0)
{
v___x_404_ = v_x_391_;
v_isShared_405_ = v_isSharedCheck_431_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v_x_391_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_431_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_406_; 
v___x_406_ = lean_uv_timer_next(v_a_402_);
lean_dec(v_a_402_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_419_; 
lean_del_object(v___x_404_);
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_419_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___f_411_; lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___f_411_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_412_ = lean_io_promise_result_opt(v_a_407_);
lean_dec(v_a_407_);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = 0;
v___x_415_ = lean_task_map(v___f_411_, v___x_412_, v___x_413_, v___x_414_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 1);
lean_ctor_set(v___x_409_, 0, v___x_415_);
v___x_417_ = v___x_409_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_430_; 
v_a_420_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_430_ == 0)
{
v___x_422_ = v___x_406_;
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_406_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_430_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 0);
lean_ctor_set(v___x_404_, 0, v_a_420_);
v___x_425_ = v___x_404_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_429_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 0);
lean_ctor_set(v___x_422_, 0, v___x_425_);
v___x_427_ = v___x_422_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___lam__1___boxed(lean_object* v_x_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_Async_sleep___lam__1(v_x_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep(lean_object* v_duration_436_){
_start:
{
lean_object* v___f_438_; lean_object* v___f_439_; lean_object* v_val_441_; lean_object* v___x_447_; uint64_t v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; 
v___f_438_ = ((lean_object*)(l_Std_Async_sleep___closed__0));
v___f_439_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_447_ = l_Int_toNat(v_duration_436_);
v___x_448_ = lean_uint64_of_nat(v___x_447_);
lean_dec(v___x_447_);
v___x_449_ = 0;
v___x_450_ = lean_uv_timer_mk(v___x_448_, v___x_449_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set_tag(v___x_453_, 1);
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
v_val_441_ = v___x_456_;
goto v___jp_440_;
}
}
}
else
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_466_; 
v_a_459_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_466_ == 0)
{
v___x_461_ = v___x_450_;
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_450_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_466_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set_tag(v___x_461_, 0);
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
v_val_441_ = v___x_464_;
goto v___jp_440_;
}
}
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_442_, 0, v_val_441_);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = 0;
v___x_445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_443_, v___x_444_, v___x_442_, v___f_439_);
v___x_446_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_443_, v___x_444_, v___x_445_, v___f_438_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___boxed(lean_object* v_duration_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_Async_sleep(v_duration_467_);
lean_dec(v_duration_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___lam__0(lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_480_; 
v_a_472_ = lean_ctor_get(v_x_470_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_480_ == 0)
{
v___x_474_ = v_x_470_;
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v_x_470_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_480_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_472_);
v___x_477_ = v_reuseFailAlloc_479_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; 
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_490_; 
v_a_481_ = lean_ctor_get(v_x_470_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v_x_470_);
if (v_isSharedCheck_490_ == 0)
{
v___x_483_ = v_x_470_;
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v_x_470_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l_Std_Async_Sleep_selector(v_a_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_489_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; 
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___lam__0___boxed(lean_object* v_x_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_Async_Selector_sleep___lam__0(v_x_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep(lean_object* v_duration_495_){
_start:
{
lean_object* v___f_497_; lean_object* v___f_498_; lean_object* v_val_500_; lean_object* v___x_506_; uint64_t v___x_507_; uint8_t v___x_508_; lean_object* v___x_509_; 
v___f_497_ = ((lean_object*)(l_Std_Async_Selector_sleep___closed__0));
v___f_498_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_506_ = l_Int_toNat(v_duration_495_);
v___x_507_ = lean_uint64_of_nat(v___x_506_);
lean_dec(v___x_506_);
v___x_508_ = 0;
v___x_509_ = lean_uv_timer_mk(v___x_507_, v___x_508_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set_tag(v___x_512_, 1);
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
v_val_500_ = v___x_515_;
goto v___jp_499_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
v_a_518_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_509_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_509_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 0);
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
v_val_500_ = v___x_523_;
goto v___jp_499_;
}
}
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v_val_500_);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = 0;
v___x_504_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_502_, v___x_503_, v___x_501_, v___f_498_);
v___x_505_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_502_, v___x_503_, v___x_504_, v___f_497_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___boxed(lean_object* v_duration_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Async_Selector_sleep(v_duration_526_);
lean_dec(v_duration_526_);
return v_res_528_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__12(void){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__10));
v___x_556_ = l_Lean_mkAtom(v___x_555_);
return v___x_556_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__13(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__12, &l_Std_Async_Interval_mk___auto__1___closed__12_once, _init_l_Std_Async_Interval_mk___auto__1___closed__12);
v___x_558_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_559_ = lean_array_push(v___x_558_, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__17(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__16));
v___x_571_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_572_ = lean_array_push(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__18(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__17, &l_Std_Async_Interval_mk___auto__1___closed__17_once, _init_l_Std_Async_Interval_mk___auto__1___closed__17);
v___x_574_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__15));
v___x_575_ = lean_box(2);
v___x_576_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v___x_574_);
lean_ctor_set(v___x_576_, 2, v___x_573_);
return v___x_576_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__19(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__18, &l_Std_Async_Interval_mk___auto__1___closed__18_once, _init_l_Std_Async_Interval_mk___auto__1___closed__18);
v___x_578_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__13, &l_Std_Async_Interval_mk___auto__1___closed__13_once, _init_l_Std_Async_Interval_mk___auto__1___closed__13);
v___x_579_ = lean_array_push(v___x_578_, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__20(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_580_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__19, &l_Std_Async_Interval_mk___auto__1___closed__19_once, _init_l_Std_Async_Interval_mk___auto__1___closed__19);
v___x_581_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__11));
v___x_582_ = lean_box(2);
v___x_583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
lean_ctor_set(v___x_583_, 2, v___x_580_);
return v___x_583_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__21(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__20, &l_Std_Async_Interval_mk___auto__1___closed__20_once, _init_l_Std_Async_Interval_mk___auto__1___closed__20);
v___x_585_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_586_ = lean_array_push(v___x_585_, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__22(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__21, &l_Std_Async_Interval_mk___auto__1___closed__21_once, _init_l_Std_Async_Interval_mk___auto__1___closed__21);
v___x_588_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__9));
v___x_589_ = lean_box(2);
v___x_590_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
lean_ctor_set(v___x_590_, 2, v___x_587_);
return v___x_590_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__23(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__22, &l_Std_Async_Interval_mk___auto__1___closed__22_once, _init_l_Std_Async_Interval_mk___auto__1___closed__22);
v___x_592_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_593_ = lean_array_push(v___x_592_, v___x_591_);
return v___x_593_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__24(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_594_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__23, &l_Std_Async_Interval_mk___auto__1___closed__23_once, _init_l_Std_Async_Interval_mk___auto__1___closed__23);
v___x_595_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__7));
v___x_596_ = lean_box(2);
v___x_597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
lean_ctor_set(v___x_597_, 1, v___x_595_);
lean_ctor_set(v___x_597_, 2, v___x_594_);
return v___x_597_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__25(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__24, &l_Std_Async_Interval_mk___auto__1___closed__24_once, _init_l_Std_Async_Interval_mk___auto__1___closed__24);
v___x_599_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_600_ = lean_array_push(v___x_599_, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__26(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_601_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__25, &l_Std_Async_Interval_mk___auto__1___closed__25_once, _init_l_Std_Async_Interval_mk___auto__1___closed__25);
v___x_602_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__4));
v___x_603_ = lean_box(2);
v___x_604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_602_);
lean_ctor_set(v___x_604_, 2, v___x_601_);
return v___x_604_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1(void){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__26, &l_Std_Async_Interval_mk___auto__1___closed__26_once, _init_l_Std_Async_Interval_mk___auto__1___closed__26);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___redArg(lean_object* v_duration_606_){
_start:
{
lean_object* v___x_608_; uint64_t v___x_609_; uint8_t v___x_610_; lean_object* v___x_611_; 
v___x_608_ = l_Int_toNat(v_duration_606_);
v___x_609_ = lean_uint64_of_nat(v___x_608_);
lean_dec(v___x_608_);
v___x_610_ = 1;
v___x_611_ = lean_uv_timer_mk(v___x_609_, v___x_610_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_611_);
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
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_a_620_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_611_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_611_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___redArg___boxed(lean_object* v_duration_628_, lean_object* v_a_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_Async_Interval_mk___redArg(v_duration_628_);
lean_dec(v_duration_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk(lean_object* v_duration_631_, lean_object* v_x_632_){
_start:
{
lean_object* v___x_634_; uint64_t v___x_635_; uint8_t v___x_636_; lean_object* v___x_637_; 
v___x_634_ = l_Int_toNat(v_duration_631_);
v___x_635_ = lean_uint64_of_nat(v___x_634_);
lean_dec(v___x_634_);
v___x_636_ = 1;
v___x_637_ = lean_uv_timer_mk(v___x_635_, v___x_636_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_645_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_645_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_645_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_643_; 
if (v_isShared_641_ == 0)
{
v___x_643_ = v___x_640_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_a_638_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
v_a_646_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_637_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_637_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___boxed(lean_object* v_duration_654_, lean_object* v_x_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_Async_Interval_mk(v_duration_654_, v_x_655_);
lean_dec(v_duration_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_tick(lean_object* v_i_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = lean_uv_timer_next(v_i_658_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_673_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_673_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_673_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_673_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___f_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___f_665_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_666_ = lean_io_promise_result_opt(v_a_661_);
lean_dec(v_a_661_);
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = 0;
v___x_669_ = lean_task_map(v___f_665_, v___x_666_, v___x_667_, v___x_668_);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 1);
lean_ctor_set(v___x_663_, 0, v___x_669_);
v___x_671_ = v___x_663_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_682_; 
v_a_674_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_682_ == 0)
{
v___x_676_ = v___x_660_;
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_660_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_682_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 0);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_681_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; 
v___x_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_680_, 0, v___x_679_);
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_tick___boxed(lean_object* v_i_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Std_Async_Interval_tick(v_i_683_);
lean_dec(v_i_683_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_reset(lean_object* v_i_686_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_uv_timer_reset(v_i_686_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_reset___boxed(lean_object* v_i_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_Async_Interval_reset(v_i_689_);
lean_dec(v_i_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_stop(lean_object* v_i_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = lean_uv_timer_stop(v_i_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_stop___boxed(lean_object* v_i_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Std_Async_Interval_stop(v_i_695_);
lean_dec(v_i_695_);
return v_res_697_;
}
}
lean_object* runtime_initialize_Std_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_UV_Timer(uint8_t builtin);
lean_object* runtime_initialize_Std_Async_Select(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Async_Timer(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

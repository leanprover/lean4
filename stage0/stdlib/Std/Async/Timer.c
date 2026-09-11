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
lean_object* v___f_27_; lean_object* v___x_28_; uint64_t v___x_29_; uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v_val_33_; lean_object* v___x_36_; 
v___f_27_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_28_ = l_Int_toNat(v_duration_25_);
v___x_29_ = lean_uint64_of_nat(v___x_28_);
lean_dec(v___x_28_);
v___x_30_ = 0;
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_uv_timer_mk(v___x_29_, v___x_30_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_36_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_36_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
lean_ctor_set_tag(v___x_39_, 1);
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
v_val_33_ = v___x_42_;
goto v___jp_32_;
}
}
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_36_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_36_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set_tag(v___x_47_, 0);
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
v_val_33_ = v___x_50_;
goto v___jp_32_;
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v_val_33_);
v___x_35_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_31_, v___x_30_, v___x_34_, v___f_27_);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_mk___boxed(lean_object* v_duration_53_, lean_object* v_a_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_Async_Sleep_mk(v_duration_53_);
lean_dec(v_duration_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait___lam__0(lean_object* v___x_56_, lean_object* v_x_57_){
_start:
{
if (lean_obj_tag(v_x_57_) == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_mk_io_user_error(v___x_56_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
else
{
lean_object* v_val_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
lean_dec_ref(v___x_56_);
v_val_60_ = lean_ctor_get(v_x_57_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v_x_57_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_val_60_);
lean_dec(v_x_57_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_val_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait(lean_object* v_s_71_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; 
v___f_73_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_74_ = lean_uv_timer_next(v_s_71_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_86_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_86_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_86_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_86_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_79_ = lean_io_promise_result_opt(v_a_75_);
lean_dec(v_a_75_);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = 0;
v___x_82_ = lean_task_map(v___f_73_, v___x_79_, v___x_80_, v___x_81_);
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 1);
lean_ctor_set(v___x_77_, 0, v___x_82_);
v___x_84_ = v___x_77_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_82_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
v_a_87_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_95_ == 0)
{
v___x_89_ = v___x_74_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_74_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 0);
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_94_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_wait___boxed(lean_object* v_s_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Std_Async_Sleep_wait(v_s_96_);
lean_dec(v_s_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_reset(lean_object* v_s_99_){
_start:
{
lean_object* v_val_102_; lean_object* v___x_104_; 
v___x_104_ = lean_uv_timer_reset(v_s_99_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set_tag(v___x_107_, 1);
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
v_val_102_ = v___x_110_;
goto v___jp_101_;
}
}
}
else
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
v_a_113_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_104_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_104_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set_tag(v___x_115_, 0);
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
v_val_102_ = v___x_118_;
goto v___jp_101_;
}
}
}
v___jp_101_:
{
lean_object* v___x_103_; 
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v_val_102_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_reset___boxed(lean_object* v_s_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_Async_Sleep_reset(v_s_121_);
lean_dec(v_s_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_stop(lean_object* v_s_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_uv_timer_stop(v_s_124_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_stop___boxed(lean_object* v_s_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Std_Async_Sleep_stop(v_s_127_);
lean_dec(v_s_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(lean_object* v_w_132_, lean_object* v_lose_133_){
_start:
{
lean_object* v_finished_135_; lean_object* v_promise_136_; lean_object* v___x_137_; uint8_t v___y_139_; uint8_t v___x_146_; 
v_finished_135_ = lean_ctor_get(v_w_132_, 0);
v_promise_136_ = lean_ctor_get(v_w_132_, 1);
v___x_137_ = lean_st_ref_take(v_finished_135_);
v___x_146_ = lean_unbox(v___x_137_);
lean_dec(v___x_137_);
if (v___x_146_ == 0)
{
uint8_t v___x_147_; 
v___x_147_ = 1;
v___y_139_ = v___x_147_;
goto v___jp_138_;
}
else
{
uint8_t v___x_148_; 
v___x_148_ = 0;
v___y_139_ = v___x_148_;
goto v___jp_138_;
}
v___jp_138_:
{
uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = 1;
v___x_141_ = lean_box(v___x_140_);
v___x_142_ = lean_st_ref_put(v_finished_135_, v___x_141_);
if (v___y_139_ == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_apply_1(v_lose_133_, lean_box(0));
return v___x_143_;
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec_ref(v_lose_133_);
v___x_144_ = ((lean_object*)(l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___closed__0));
v___x_145_ = lean_io_promise_resolve(v___x_144_, v_promise_136_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0___boxed(lean_object* v_w_149_, lean_object* v_lose_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(v_w_149_, v_lose_150_);
lean_dec_ref(v_w_149_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__0(lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_157_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_167_; 
v_a_159_ = lean_ctor_get(v_x_157_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v_x_157_);
if (v_isSharedCheck_167_ == 0)
{
v___x_161_ = v_x_157_;
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v_x_157_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_166_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
}
else
{
lean_object* v___x_168_; 
lean_dec_ref_known(v_x_157_, 1);
v___x_168_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__0___closed__1));
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__0___boxed(lean_object* v_x_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_Async_Sleep_selector___lam__0(v_x_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__1(lean_object* v_s_172_){
_start:
{
lean_object* v_val_175_; lean_object* v___x_177_; 
v___x_177_ = lean_uv_timer_cancel(v_s_172_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 1);
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
v_val_175_ = v___x_183_;
goto v___jp_174_;
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v_a_186_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_177_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_177_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set_tag(v___x_188_, 0);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
v_val_175_ = v___x_191_;
goto v___jp_174_;
}
}
}
v___jp_174_:
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v_val_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__1___boxed(lean_object* v_s_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_Async_Sleep_selector___lam__1(v_s_194_);
lean_dec(v_s_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__2(lean_object* v___x_197_){
_start:
{
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__2___boxed(lean_object* v___x_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Std_Async_Sleep_selector___lam__2(v___x_199_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__3(lean_object* v_waiter_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
return v___x_207_;
}
else
{
lean_object* v___f_208_; lean_object* v___x_209_; 
v___f_208_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__3___closed__0));
v___x_209_ = l_Std_Async_Waiter_race___at___00Std_Async_Sleep_selector_spec__0(v_waiter_204_, v___f_208_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__3___boxed(lean_object* v_waiter_210_, lean_object* v_x_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Async_Sleep_selector___lam__3(v_waiter_210_, v_x_211_);
lean_dec(v_x_211_);
lean_dec_ref(v_waiter_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__4(lean_object* v___f_214_, lean_object* v_x_215_){
_start:
{
if (lean_obj_tag(v_x_215_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
lean_dec_ref(v___f_214_);
v_a_217_ = lean_ctor_get(v_x_215_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v_x_215_);
if (v_isSharedCheck_225_ == 0)
{
v___x_219_ = v_x_215_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v_x_215_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_224_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_238_; 
v_a_226_ = lean_ctor_get(v_x_215_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v_x_215_);
if (v_isSharedCheck_238_ == 0)
{
v___x_228_ = v_x_215_;
v_isShared_229_ = v_isSharedCheck_238_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v_x_215_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_238_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_230_ = lean_io_promise_result_opt(v_a_226_);
lean_dec(v_a_226_);
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = 0;
v___x_233_ = l_BaseIO_chainTask___redArg(v___x_230_, v___f_214_, v___x_231_, v___x_232_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_233_);
v___x_235_ = v___x_228_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_237_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; 
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__4___boxed(lean_object* v___f_239_, lean_object* v_x_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Async_Sleep_selector___lam__4(v___f_239_, v_x_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__5(lean_object* v_s_243_, lean_object* v_waiter_244_){
_start:
{
lean_object* v___f_246_; lean_object* v___f_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v_val_251_; lean_object* v___x_254_; 
v___f_246_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__3___boxed), 3, 1);
lean_closure_set(v___f_246_, 0, v_waiter_244_);
v___f_247_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__4___boxed), 3, 1);
lean_closure_set(v___f_247_, 0, v___f_246_);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = 0;
v___x_254_ = lean_uv_timer_next(v_s_243_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set_tag(v___x_257_, 1);
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
v_val_251_ = v___x_260_;
goto v___jp_250_;
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_254_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_254_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set_tag(v___x_265_, 0);
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
v_val_251_ = v___x_268_;
goto v___jp_250_;
}
}
}
v___jp_250_:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_252_, 0, v_val_251_);
v___x_253_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_248_, v___x_249_, v___x_252_, v___f_247_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__5___boxed(lean_object* v_s_271_, lean_object* v_waiter_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_Async_Sleep_selector___lam__5(v_s_271_, v_waiter_272_);
lean_dec(v_s_271_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__6(lean_object* v___f_281_, lean_object* v_s_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v___f_281_);
v_a_285_ = lean_ctor_get(v_x_283_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_293_ == 0)
{
v___x_287_ = v_x_283_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v_x_283_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_292_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
lean_object* v___x_291_; 
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_315_; 
v_a_294_ = lean_ctor_get(v_x_283_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_315_ == 0)
{
v___x_296_ = v_x_283_;
v_isShared_297_ = v_isSharedCheck_315_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v_x_283_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_315_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
uint8_t v___x_298_; 
v___x_298_ = lean_unbox(v_a_294_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v_val_301_; lean_object* v___x_305_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_uv_timer_cancel(v_s_282_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_305_, 1);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v_a_306_);
v___x_308_ = v___x_296_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
v_val_301_ = v___x_308_;
goto v___jp_300_;
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_312_; 
v_a_310_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_310_);
lean_dec_ref_known(v___x_305_, 1);
if (v_isShared_297_ == 0)
{
lean_ctor_set_tag(v___x_296_, 0);
lean_ctor_set(v___x_296_, 0, v_a_310_);
v___x_312_ = v___x_296_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_a_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
v_val_301_ = v___x_312_;
goto v___jp_300_;
}
}
v___jp_300_:
{
lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; 
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v_val_301_);
v___x_303_ = lean_unbox(v_a_294_);
lean_dec(v_a_294_);
v___x_304_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_299_, v___x_303_, v___x_302_, v___f_281_);
return v___x_304_;
}
}
else
{
lean_object* v___x_314_; 
lean_del_object(v___x_296_);
lean_dec(v_a_294_);
lean_dec_ref(v___f_281_);
v___x_314_ = ((lean_object*)(l_Std_Async_Sleep_selector___lam__6___closed__2));
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__6___boxed(lean_object* v___f_316_, lean_object* v_s_317_, lean_object* v_x_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_Async_Sleep_selector___lam__6(v___f_316_, v_s_317_, v_x_318_);
lean_dec(v_s_317_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__7(lean_object* v___f_321_, lean_object* v_x_322_){
_start:
{
if (lean_obj_tag(v_x_322_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_332_; 
lean_dec_ref(v___f_321_);
v_a_324_ = lean_ctor_get(v_x_322_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_322_);
if (v_isSharedCheck_332_ == 0)
{
v___x_326_ = v_x_322_;
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v_x_322_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_324_);
v___x_329_ = v_reuseFailAlloc_331_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_346_; 
v_a_333_ = lean_ctor_get(v_x_322_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v_x_322_);
if (v_isSharedCheck_346_ == 0)
{
v___x_335_ = v_x_322_;
v_isShared_336_ = v_isSharedCheck_346_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v_x_322_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_346_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; uint8_t v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = 0;
v___x_339_ = l_IO_Promise_isResolved___redArg(v_a_333_);
lean_dec(v_a_333_);
v___x_340_ = lean_box(v___x_339_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_340_);
v___x_342_ = v___x_335_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_345_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
v___x_344_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_337_, v___x_338_, v___x_343_, v___f_321_);
return v___x_344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__7___boxed(lean_object* v___f_347_, lean_object* v_x_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Async_Sleep_selector___lam__7(v___f_347_, v_x_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__8(lean_object* v___f_351_, lean_object* v_s_352_){
_start:
{
lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v_val_357_; lean_object* v___x_360_; 
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = 0;
v___x_360_ = lean_uv_timer_next(v_s_352_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 1);
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
v_val_357_ = v___x_366_;
goto v___jp_356_;
}
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
v_a_369_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_360_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_360_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 0);
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
v_val_357_ = v___x_374_;
goto v___jp_356_;
}
}
}
v___jp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v_val_357_);
v___x_359_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_354_, v___x_355_, v___x_358_, v___f_351_);
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector___lam__8___boxed(lean_object* v___f_377_, lean_object* v_s_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Async_Sleep_selector___lam__8(v___f_377_, v_s_378_);
lean_dec(v_s_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Sleep_selector(lean_object* v_s_382_){
_start:
{
lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___f_385_; lean_object* v___f_386_; lean_object* v___f_387_; lean_object* v___f_388_; lean_object* v___x_389_; 
v___f_383_ = ((lean_object*)(l_Std_Async_Sleep_selector___closed__0));
lean_inc_n(v_s_382_, 3);
v___f_384_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__1___boxed), 2, 1);
lean_closure_set(v___f_384_, 0, v_s_382_);
v___f_385_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__5___boxed), 3, 1);
lean_closure_set(v___f_385_, 0, v_s_382_);
v___f_386_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__6___boxed), 4, 2);
lean_closure_set(v___f_386_, 0, v___f_383_);
lean_closure_set(v___f_386_, 1, v_s_382_);
v___f_387_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__7___boxed), 3, 1);
lean_closure_set(v___f_387_, 0, v___f_386_);
v___f_388_ = lean_alloc_closure((void*)(l_Std_Async_Sleep_selector___lam__8___boxed), 3, 2);
lean_closure_set(v___f_388_, 0, v___f_387_);
lean_closure_set(v___f_388_, 1, v_s_382_);
v___x_389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_389_, 0, v___f_388_);
lean_ctor_set(v___x_389_, 1, v___f_385_);
lean_ctor_set(v___x_389_, 2, v___f_384_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___lam__1(lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_400_; 
v_a_392_ = lean_ctor_get(v_x_390_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_400_ == 0)
{
v___x_394_ = v_x_390_;
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v_x_390_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_400_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_399_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v___x_398_; 
v___x_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_430_; 
v_a_401_ = lean_ctor_get(v_x_390_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_430_ == 0)
{
v___x_403_ = v_x_390_;
v_isShared_404_ = v_isSharedCheck_430_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v_x_390_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_430_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___f_405_; lean_object* v___x_406_; 
v___f_405_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_406_ = lean_uv_timer_next(v_a_401_);
lean_dec(v_a_401_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_418_; 
lean_del_object(v___x_403_);
v_a_407_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_418_ == 0)
{
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_418_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_411_ = lean_io_promise_result_opt(v_a_407_);
lean_dec(v_a_407_);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = 0;
v___x_414_ = lean_task_map(v___f_405_, v___x_411_, v___x_412_, v___x_413_);
if (v_isShared_410_ == 0)
{
lean_ctor_set_tag(v___x_409_, 1);
lean_ctor_set(v___x_409_, 0, v___x_414_);
v___x_416_ = v___x_409_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_429_; 
v_a_419_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_429_ == 0)
{
v___x_421_ = v___x_406_;
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_406_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 0);
lean_ctor_set(v___x_403_, 0, v_a_419_);
v___x_424_ = v___x_403_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_428_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_426_; 
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 0);
lean_ctor_set(v___x_421_, 0, v___x_424_);
v___x_426_ = v___x_421_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___lam__1___boxed(lean_object* v_x_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_Async_sleep___lam__1(v_x_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep(lean_object* v_duration_435_){
_start:
{
lean_object* v___f_437_; lean_object* v___f_438_; lean_object* v___x_439_; uint8_t v___x_440_; lean_object* v_val_442_; lean_object* v___x_446_; uint64_t v___x_447_; lean_object* v___x_448_; 
v___f_437_ = ((lean_object*)(l_Std_Async_sleep___closed__0));
v___f_438_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = 0;
v___x_446_ = l_Int_toNat(v_duration_435_);
v___x_447_ = lean_uint64_of_nat(v___x_446_);
lean_dec(v___x_446_);
v___x_448_ = lean_uv_timer_mk(v___x_447_, v___x_440_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set_tag(v___x_451_, 1);
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
v_val_442_ = v___x_454_;
goto v___jp_441_;
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_a_457_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_448_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_448_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 0);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
v_val_442_ = v___x_462_;
goto v___jp_441_;
}
}
}
v___jp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v_val_442_);
v___x_444_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_439_, v___x_440_, v___x_443_, v___f_438_);
v___x_445_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_439_, v___x_440_, v___x_444_, v___f_437_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_sleep___boxed(lean_object* v_duration_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_Async_sleep(v_duration_465_);
lean_dec(v_duration_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___lam__0(lean_object* v_x_468_){
_start:
{
if (lean_obj_tag(v_x_468_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_478_; 
v_a_470_ = lean_ctor_get(v_x_468_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_468_);
if (v_isSharedCheck_478_ == 0)
{
v___x_472_ = v_x_468_;
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v_x_468_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_477_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_476_; 
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_488_; 
v_a_479_ = lean_ctor_get(v_x_468_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v_x_468_);
if (v_isSharedCheck_488_ == 0)
{
v___x_481_ = v_x_468_;
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v_x_468_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_488_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = l_Std_Async_Sleep_selector(v_a_479_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_487_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; 
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___lam__0___boxed(lean_object* v_x_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_Async_Selector_sleep___lam__0(v_x_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep(lean_object* v_duration_493_){
_start:
{
lean_object* v___f_495_; lean_object* v___f_496_; lean_object* v___x_497_; uint8_t v___x_498_; lean_object* v_val_500_; lean_object* v___x_504_; uint64_t v___x_505_; lean_object* v___x_506_; 
v___f_495_ = ((lean_object*)(l_Std_Async_Selector_sleep___closed__0));
v___f_496_ = ((lean_object*)(l_Std_Async_Sleep_mk___closed__0));
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = 0;
v___x_504_ = l_Int_toNat(v_duration_493_);
v___x_505_ = lean_uint64_of_nat(v___x_504_);
lean_dec(v___x_504_);
v___x_506_ = lean_uv_timer_mk(v___x_505_, v___x_498_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 1);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
v_val_500_ = v___x_512_;
goto v___jp_499_;
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
v_a_515_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_506_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_506_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set_tag(v___x_517_, 0);
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
v_val_500_ = v___x_520_;
goto v___jp_499_;
}
}
}
v___jp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v_val_500_);
v___x_502_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_497_, v___x_498_, v___x_501_, v___f_496_);
v___x_503_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(lean_box(0), lean_box(0), v___x_497_, v___x_498_, v___x_502_, v___f_495_);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Selector_sleep___boxed(lean_object* v_duration_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_Async_Selector_sleep(v_duration_523_);
lean_dec(v_duration_523_);
return v_res_525_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__12(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__10));
v___x_553_ = l_Lean_mkAtom(v___x_552_);
return v___x_553_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__13(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__12, &l_Std_Async_Interval_mk___auto__1___closed__12_once, _init_l_Std_Async_Interval_mk___auto__1___closed__12);
v___x_555_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_556_ = lean_array_push(v___x_555_, v___x_554_);
return v___x_556_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__17(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__16));
v___x_568_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_569_ = lean_array_push(v___x_568_, v___x_567_);
return v___x_569_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__18(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__17, &l_Std_Async_Interval_mk___auto__1___closed__17_once, _init_l_Std_Async_Interval_mk___auto__1___closed__17);
v___x_571_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__15));
v___x_572_ = lean_box(2);
v___x_573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_571_);
lean_ctor_set(v___x_573_, 2, v___x_570_);
return v___x_573_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__19(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__18, &l_Std_Async_Interval_mk___auto__1___closed__18_once, _init_l_Std_Async_Interval_mk___auto__1___closed__18);
v___x_575_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__13, &l_Std_Async_Interval_mk___auto__1___closed__13_once, _init_l_Std_Async_Interval_mk___auto__1___closed__13);
v___x_576_ = lean_array_push(v___x_575_, v___x_574_);
return v___x_576_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__20(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__19, &l_Std_Async_Interval_mk___auto__1___closed__19_once, _init_l_Std_Async_Interval_mk___auto__1___closed__19);
v___x_578_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__11));
v___x_579_ = lean_box(2);
v___x_580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v___x_578_);
lean_ctor_set(v___x_580_, 2, v___x_577_);
return v___x_580_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__21(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__20, &l_Std_Async_Interval_mk___auto__1___closed__20_once, _init_l_Std_Async_Interval_mk___auto__1___closed__20);
v___x_582_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_583_ = lean_array_push(v___x_582_, v___x_581_);
return v___x_583_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__22(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_584_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__21, &l_Std_Async_Interval_mk___auto__1___closed__21_once, _init_l_Std_Async_Interval_mk___auto__1___closed__21);
v___x_585_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__9));
v___x_586_ = lean_box(2);
v___x_587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
lean_ctor_set(v___x_587_, 2, v___x_584_);
return v___x_587_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__23(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__22, &l_Std_Async_Interval_mk___auto__1___closed__22_once, _init_l_Std_Async_Interval_mk___auto__1___closed__22);
v___x_589_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_590_ = lean_array_push(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__24(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__23, &l_Std_Async_Interval_mk___auto__1___closed__23_once, _init_l_Std_Async_Interval_mk___auto__1___closed__23);
v___x_592_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__7));
v___x_593_ = lean_box(2);
v___x_594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
lean_ctor_set(v___x_594_, 2, v___x_591_);
return v___x_594_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__25(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__24, &l_Std_Async_Interval_mk___auto__1___closed__24_once, _init_l_Std_Async_Interval_mk___auto__1___closed__24);
v___x_596_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__5));
v___x_597_ = lean_array_push(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1___closed__26(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_598_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__25, &l_Std_Async_Interval_mk___auto__1___closed__25_once, _init_l_Std_Async_Interval_mk___auto__1___closed__25);
v___x_599_ = ((lean_object*)(l_Std_Async_Interval_mk___auto__1___closed__4));
v___x_600_ = lean_box(2);
v___x_601_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v___x_599_);
lean_ctor_set(v___x_601_, 2, v___x_598_);
return v___x_601_;
}
}
static lean_object* _init_l_Std_Async_Interval_mk___auto__1(void){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = lean_obj_once(&l_Std_Async_Interval_mk___auto__1___closed__26, &l_Std_Async_Interval_mk___auto__1___closed__26_once, _init_l_Std_Async_Interval_mk___auto__1___closed__26);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___redArg(lean_object* v_duration_603_){
_start:
{
lean_object* v___x_605_; uint64_t v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; 
v___x_605_ = l_Int_toNat(v_duration_603_);
v___x_606_ = lean_uint64_of_nat(v___x_605_);
lean_dec(v___x_605_);
v___x_607_ = 1;
v___x_608_ = lean_uv_timer_mk(v___x_606_, v___x_607_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_a_617_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_608_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_608_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___redArg___boxed(lean_object* v_duration_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_Async_Interval_mk___redArg(v_duration_625_);
lean_dec(v_duration_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk(lean_object* v_duration_628_, lean_object* v_x_629_){
_start:
{
lean_object* v___x_631_; uint64_t v___x_632_; uint8_t v___x_633_; lean_object* v___x_634_; 
v___x_631_ = l_Int_toNat(v_duration_628_);
v___x_632_ = lean_uint64_of_nat(v___x_631_);
lean_dec(v___x_631_);
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
LEAN_EXPORT lean_object* l_Std_Async_Interval_mk___boxed(lean_object* v_duration_651_, lean_object* v_x_652_, lean_object* v_a_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Std_Async_Interval_mk(v_duration_651_, v_x_652_);
lean_dec(v_duration_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_tick(lean_object* v_i_655_){
_start:
{
lean_object* v___f_657_; lean_object* v___x_658_; 
v___f_657_ = ((lean_object*)(l_Std_Async_Sleep_wait___closed__1));
v___x_658_ = lean_uv_timer_next(v_i_655_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_670_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_670_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_663_ = lean_io_promise_result_opt(v_a_659_);
lean_dec(v_a_659_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = 0;
v___x_666_ = lean_task_map(v___f_657_, v___x_663_, v___x_664_, v___x_665_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 1);
lean_ctor_set(v___x_661_, 0, v___x_666_);
v___x_668_ = v___x_661_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_a_671_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v___x_658_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_658_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set_tag(v___x_673_, 0);
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_678_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; 
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_tick___boxed(lean_object* v_i_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_Async_Interval_tick(v_i_680_);
lean_dec(v_i_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_reset(lean_object* v_i_683_){
_start:
{
lean_object* v___x_685_; 
v___x_685_ = lean_uv_timer_reset(v_i_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_reset___boxed(lean_object* v_i_686_, lean_object* v_a_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Std_Async_Interval_reset(v_i_686_);
lean_dec(v_i_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_stop(lean_object* v_i_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = lean_uv_timer_stop(v_i_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Async_Interval_stop___boxed(lean_object* v_i_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_Async_Interval_stop(v_i_692_);
lean_dec(v_i_692_);
return v_res_694_;
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

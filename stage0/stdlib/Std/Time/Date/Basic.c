// Lean compiler output
// Module: Std.Time.Date.Basic
// Imports: public import Std.Time.Date.Unit.Basic public import Std.Time.Date.ValidDate
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_Offset_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_Offset_toDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toDays___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofDays___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_Offset_toWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toWeeks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofWeeks___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Millisecond_Offset_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_Offset_toDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toDays___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofDays___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Millisecond_Offset_toWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toWeeks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofWeeks___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Second_Offset_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_Offset_toDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toDays___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofDays___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Second_Offset_toWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Second_Offset_toWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toWeeks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofWeeks___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Minute_Offset_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Minute_Offset_toDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toDays___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofDays___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Minute_Offset_toWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Minute_Offset_toWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toWeeks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofWeeks___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Hour_Offset_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Hour_Offset_toDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toDays___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofDays___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Hour_Offset_toWeeks___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Hour_Offset_toWeeks___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toWeeks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofWeeks(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofWeeks___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset = (const lean_object*)&l_Std_Time_instHAddOffsetOffset___closed__0_value;
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__1___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__1 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__1___closed__0_value;
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__2___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__2 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__2___closed__0_value;
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__3___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__3 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__3___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__4___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__4___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__4___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__4 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__4___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__5___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__5___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__5___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__5 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__5___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__6___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__6___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__6___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__6 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__6___closed__0_value;
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__7___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__7___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__7___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__7___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__7___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__7 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__7___closed__0_value;
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__8___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__8___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__8___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__8 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__8___closed__0_value;
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__9___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__9___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__9___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__9___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__9___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__9 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__9___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__10___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__10___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__10___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__10___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__10___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__10 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__10___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__11___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__11___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__11___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__11___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__11___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__11 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__11___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__12___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__12___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__12___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__12___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__12___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__12 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__12___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__13___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__13___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__13___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__13___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__13___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__13 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__13___closed__0_value;
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__14___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__14___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__14___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__14___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__14___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__14 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__14___closed__0_value;
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__15___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__15___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__15___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__15___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__15___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__15 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__15___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__16___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__16___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__16___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__16___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__16 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__16___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__17___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__17___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__17___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__17___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__17___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__17 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__17___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__18___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__18___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__18___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__18___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__18___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__18 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__18___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__19___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__19___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__19___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__19___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__19___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__19 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__19___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__20___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__20___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__20___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__20___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__20___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__20 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__20___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__21 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__14___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__22___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__22___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__22___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__22___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__22___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__22 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__22___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__23___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__23___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__23___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__23___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__23___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__23 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__23___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__24___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__24___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__24___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__24___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__24___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__24___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__24 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__24___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__25___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__25___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__25___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__25___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__25___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__25___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__25 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__25___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__26___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__26___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__26___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__26___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__26___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__26___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__26 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__26___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__27 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__20___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__28___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__28___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__28___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__28___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__28___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__28___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__28 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__28___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__29___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__29___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__29___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__29___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__29___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__29 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__29___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__30___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__30___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__30___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__30___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__30___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__30___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__30 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__30___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__31___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__31___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__31___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__31___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__31___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__31___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__31 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__31___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__32___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__32___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__32___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__32___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__32 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__32___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__33___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__33___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__33___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__33___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__33___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__33___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__33 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__33___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__34___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__34___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__34___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__34___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__34___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__34___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__34 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__34___closed__0_value;
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__35___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__35___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__35___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__35___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__35___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__35___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__35 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__35___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__36___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__36___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__36___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__36___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__36___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__36___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__36 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__36___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__37___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__37___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__37___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__37___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__37___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__37___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__37 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__37___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__38___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__38___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__38___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__38___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__38___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__38___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__38 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__38___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__39___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__39___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__39___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__39___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__39___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__39___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__39 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__39___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__40___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__40___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__40___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__40___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__40___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__40___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__40 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__40___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__41___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__41___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffsetOffset__41___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHAddOffsetOffset__41___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffsetOffset__41___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__41___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffsetOffset__41 = (const lean_object*)&l_Std_Time_instHAddOffsetOffset__41___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset = (const lean_object*)&l_Std_Time_instHSubOffsetOffset___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__1___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__1 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__2___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__2 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__3___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__3 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__3___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__4___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__4___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__4___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__4___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__4 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__4___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__5___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__5___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__5___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__5 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__5___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__6___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__6___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__6___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__6 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__6___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__7___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__7___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__7___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__7___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__7___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__7 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__7___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__8___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__8___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__8___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__8___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__8___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__8 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__8___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__9___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__9___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__9___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__9___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__9___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__9 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__9___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__10___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__10___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__10___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__10___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__10___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__10 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__10___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__11___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__11___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__11___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__11___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__11___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__11 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__11___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__12___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__12___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__12___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__12___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__12___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__12 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__12___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__13___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__13___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__13___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__13___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__13___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__13 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__13___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__14___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__14___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__14___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__14___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__14___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__14 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__14___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__15___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__15___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__15___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__15___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__15___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__15 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__15___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__16___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__16___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__16___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__16___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__16___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__16 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__16___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__17___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__17___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__17___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__17___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__17___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__17 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__17___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__18___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__18___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__18___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__18___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__18___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__18 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__18___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__19___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__19___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__19___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__19___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__19___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__19 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__19___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__20___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__20___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__20___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__20___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__20___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__20 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__20___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__21 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__14___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__22___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__22___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__22___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__22___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__22___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__22 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__22___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__23___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__23___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__23___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__23___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__23___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__23 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__23___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__24___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__24___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__24___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__24___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__24___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__24___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__24 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__24___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__25___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__25___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__25___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__25___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__25___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__25___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__25 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__25___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__26___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__26___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__26___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__26___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__26___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__26___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__26 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__26___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__27 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__20___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__28___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__28___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__28___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__28___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__28___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__28___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__28 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__28___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__29___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__29___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__29___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__29___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__29___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__29___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__29 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__29___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__30___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__30___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__30___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__30___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__30___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__30___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__30 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__30___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__31___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__31___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__31___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__31___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__31___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__31___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__31 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__31___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__32___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__32___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__32___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__32___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__32___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__32 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__32___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__33___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__33___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__33___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__33___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__33___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__33___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__33 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__33___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__34___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__34___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__34___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__34___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__34___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__34___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__34 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__34___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__35___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__35___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__35___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__35___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__35___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__35___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__35 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__35___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__36___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__36___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__36___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__36___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__36___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__36___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__36 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__36___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__37___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__37___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__37___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__37___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__37___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__37___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__37 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__37___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__38___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__38___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__38___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__38___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__38___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__38___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__38 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__38___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__39___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__39___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__39___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__39___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__39___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__39___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__39 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__39___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__40___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__40___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__40___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__40___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__40___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__40___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__40 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__40___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__41___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__41___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffsetOffset__41___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instHSubOffsetOffset__41___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffsetOffset__41___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__41___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffsetOffset__41 = (const lean_object*)&l_Std_Time_instHSubOffsetOffset__41___closed__0_value;
static lean_object* _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_cstr_to_nat("86400000000000");
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toDays(lean_object* v_nanoseconds_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
v___x_5_ = lean_int_div(v_nanoseconds_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toDays___boxed(lean_object* v_nanoseconds_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Std_Time_Nanosecond_Offset_toDays(v_nanoseconds_6_);
lean_dec(v_nanoseconds_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofDays(lean_object* v_days_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
v___x_10_ = lean_int_mul(v_days_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofDays___boxed(lean_object* v_days_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Time_Nanosecond_Offset_ofDays(v_days_11_);
lean_dec(v_days_11_);
return v_res_12_;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_cstr_to_nat("604800000000000");
v___x_14_ = lean_nat_to_int(v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toWeeks(lean_object* v_nanoseconds_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
v___x_17_ = lean_int_div(v_nanoseconds_15_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toWeeks___boxed(lean_object* v_nanoseconds_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Std_Time_Nanosecond_Offset_toWeeks(v_nanoseconds_18_);
lean_dec(v_nanoseconds_18_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofWeeks(lean_object* v_weeks_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
v___x_22_ = lean_int_mul(v_weeks_20_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofWeeks___boxed(lean_object* v_weeks_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Std_Time_Nanosecond_Offset_ofWeeks(v_weeks_23_);
lean_dec(v_weeks_23_);
return v_res_24_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_Offset_toDays___closed__0(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = lean_unsigned_to_nat(86400000u);
v___x_26_ = lean_nat_to_int(v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toDays(lean_object* v_milliseconds_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
v___x_29_ = lean_int_div(v_milliseconds_27_, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toDays___boxed(lean_object* v_milliseconds_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Std_Time_Millisecond_Offset_toDays(v_milliseconds_30_);
lean_dec(v_milliseconds_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofDays(lean_object* v_days_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
v___x_34_ = lean_int_mul(v_days_32_, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofDays___boxed(lean_object* v_days_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_Time_Millisecond_Offset_ofDays(v_days_35_);
lean_dec(v_days_35_);
return v_res_36_;
}
}
static lean_object* _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_unsigned_to_nat(604800000u);
v___x_38_ = lean_nat_to_int(v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toWeeks(lean_object* v_milliseconds_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
v___x_41_ = lean_int_div(v_milliseconds_39_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toWeeks___boxed(lean_object* v_milliseconds_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_Time_Millisecond_Offset_toWeeks(v_milliseconds_42_);
lean_dec(v_milliseconds_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofWeeks(lean_object* v_weeks_44_){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
v___x_46_ = lean_int_mul(v_weeks_44_, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofWeeks___boxed(lean_object* v_weeks_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_Time_Millisecond_Offset_ofWeeks(v_weeks_47_);
lean_dec(v_weeks_47_);
return v_res_48_;
}
}
static lean_object* _init_l_Std_Time_Second_Offset_toDays___closed__0(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(86400u);
v___x_50_ = lean_nat_to_int(v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toDays(lean_object* v_seconds_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
v___x_53_ = lean_int_div(v_seconds_51_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toDays___boxed(lean_object* v_seconds_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_Time_Second_Offset_toDays(v_seconds_54_);
lean_dec(v_seconds_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofDays(lean_object* v_days_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
v___x_58_ = lean_int_mul(v_days_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofDays___boxed(lean_object* v_days_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_Time_Second_Offset_ofDays(v_days_59_);
lean_dec(v_days_59_);
return v_res_60_;
}
}
static lean_object* _init_l_Std_Time_Second_Offset_toWeeks___closed__0(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(604800u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toWeeks(lean_object* v_seconds_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
v___x_65_ = lean_int_div(v_seconds_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toWeeks___boxed(lean_object* v_seconds_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Std_Time_Second_Offset_toWeeks(v_seconds_66_);
lean_dec(v_seconds_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofWeeks(lean_object* v_weeks_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
v___x_70_ = lean_int_mul(v_weeks_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofWeeks___boxed(lean_object* v_weeks_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Time_Second_Offset_ofWeeks(v_weeks_71_);
lean_dec(v_weeks_71_);
return v_res_72_;
}
}
static lean_object* _init_l_Std_Time_Minute_Offset_toDays___closed__0(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1440u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toDays(lean_object* v_minutes_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
v___x_77_ = lean_int_div(v_minutes_75_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toDays___boxed(lean_object* v_minutes_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_Time_Minute_Offset_toDays(v_minutes_78_);
lean_dec(v_minutes_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofDays(lean_object* v_days_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
v___x_82_ = lean_int_mul(v_days_80_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofDays___boxed(lean_object* v_days_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Std_Time_Minute_Offset_ofDays(v_days_83_);
lean_dec(v_days_83_);
return v_res_84_;
}
}
static lean_object* _init_l_Std_Time_Minute_Offset_toWeeks___closed__0(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(10080u);
v___x_86_ = lean_nat_to_int(v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toWeeks(lean_object* v_minutes_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
v___x_89_ = lean_int_div(v_minutes_87_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toWeeks___boxed(lean_object* v_minutes_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Std_Time_Minute_Offset_toWeeks(v_minutes_90_);
lean_dec(v_minutes_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofWeeks(lean_object* v_weeks_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
v___x_94_ = lean_int_mul(v_weeks_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofWeeks___boxed(lean_object* v_weeks_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_Time_Minute_Offset_ofWeeks(v_weeks_95_);
lean_dec(v_weeks_95_);
return v_res_96_;
}
}
static lean_object* _init_l_Std_Time_Hour_Offset_toDays___closed__0(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(24u);
v___x_98_ = lean_nat_to_int(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toDays(lean_object* v_hours_99_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
v___x_101_ = lean_int_div(v_hours_99_, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toDays___boxed(lean_object* v_hours_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_Time_Hour_Offset_toDays(v_hours_102_);
lean_dec(v_hours_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofDays(lean_object* v_days_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
v___x_106_ = lean_int_mul(v_days_104_, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofDays___boxed(lean_object* v_days_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_Time_Hour_Offset_ofDays(v_days_107_);
lean_dec(v_days_107_);
return v_res_108_;
}
}
static lean_object* _init_l_Std_Time_Hour_Offset_toWeeks___closed__0(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(168u);
v___x_110_ = lean_nat_to_int(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toWeeks(lean_object* v_hours_111_){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
v___x_113_ = lean_int_div(v_hours_111_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toWeeks___boxed(lean_object* v_hours_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Std_Time_Hour_Offset_toWeeks(v_hours_114_);
lean_dec(v_hours_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofWeeks(lean_object* v_weeks_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
v___x_118_ = lean_int_mul(v_weeks_116_, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofWeeks___boxed(lean_object* v_weeks_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Std_Time_Hour_Offset_ofWeeks(v_weeks_119_);
lean_dec(v_weeks_119_);
return v_res_120_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1000000u);
v___x_122_ = lean_nat_to_int(v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset___lam__0(lean_object* v_x_123_, lean_object* v_y_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
v___x_126_ = lean_int_mul(v_y_124_, v___x_125_);
v___x_127_ = lean_int_add(v_x_123_, v___x_126_);
lean_dec(v___x_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset___lam__0___boxed(lean_object* v_x_128_, lean_object* v_y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Std_Time_instHAddOffsetOffset___lam__0(v_x_128_, v_y_129_);
lean_dec(v_y_129_);
lean_dec(v_x_128_);
return v_res_130_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = lean_unsigned_to_nat(1000000000u);
v___x_134_ = lean_nat_to_int(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__1___lam__0(lean_object* v_x_135_, lean_object* v_y_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
v___x_138_ = lean_int_mul(v_y_136_, v___x_137_);
v___x_139_ = lean_int_add(v_x_135_, v___x_138_);
lean_dec(v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__1___lam__0___boxed(lean_object* v_x_140_, lean_object* v_y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_Time_instHAddOffsetOffset__1___lam__0(v_x_140_, v_y_141_);
lean_dec(v_y_141_);
lean_dec(v_x_140_);
return v_res_142_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_cstr_to_nat("60000000000");
v___x_146_ = lean_nat_to_int(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__2___lam__0(lean_object* v_x_147_, lean_object* v_y_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
v___x_150_ = lean_int_mul(v_y_148_, v___x_149_);
v___x_151_ = lean_int_add(v_x_147_, v___x_150_);
lean_dec(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__2___lam__0___boxed(lean_object* v_x_152_, lean_object* v_y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_Time_instHAddOffsetOffset__2___lam__0(v_x_152_, v_y_153_);
lean_dec(v_y_153_);
lean_dec(v_x_152_);
return v_res_154_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_cstr_to_nat("3600000000000");
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__3___lam__0(lean_object* v_x_159_, lean_object* v_y_160_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
v___x_162_ = lean_int_mul(v_y_160_, v___x_161_);
v___x_163_ = lean_int_add(v_x_159_, v___x_162_);
lean_dec(v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__3___lam__0___boxed(lean_object* v_x_164_, lean_object* v_y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Time_instHAddOffsetOffset__3___lam__0(v_x_164_, v_y_165_);
lean_dec(v_y_165_);
lean_dec(v_x_164_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__4___lam__0(lean_object* v_x_169_, lean_object* v_y_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
v___x_172_ = lean_int_mul(v_y_170_, v___x_171_);
v___x_173_ = lean_int_add(v_x_169_, v___x_172_);
lean_dec(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__4___lam__0___boxed(lean_object* v_x_174_, lean_object* v_y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Std_Time_instHAddOffsetOffset__4___lam__0(v_x_174_, v_y_175_);
lean_dec(v_y_175_);
lean_dec(v_x_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__5___lam__0(lean_object* v_x_179_, lean_object* v_y_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
v___x_182_ = lean_int_mul(v_y_180_, v___x_181_);
v___x_183_ = lean_int_add(v_x_179_, v___x_182_);
lean_dec(v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__5___lam__0___boxed(lean_object* v_x_184_, lean_object* v_y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_Time_instHAddOffsetOffset__5___lam__0(v_x_184_, v_y_185_);
lean_dec(v_y_185_);
lean_dec(v_x_184_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__6___lam__0(lean_object* v_x_189_, lean_object* v_y_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
v___x_192_ = lean_int_mul(v_x_189_, v___x_191_);
v___x_193_ = lean_int_add(v___x_192_, v_y_190_);
lean_dec(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__6___lam__0___boxed(lean_object* v_x_194_, lean_object* v_y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Std_Time_instHAddOffsetOffset__6___lam__0(v_x_194_, v_y_195_);
lean_dec(v_y_195_);
lean_dec(v_x_194_);
return v_res_196_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(1000u);
v___x_200_ = lean_nat_to_int(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__7___lam__0(lean_object* v_x_201_, lean_object* v_y_202_){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
v___x_204_ = lean_int_mul(v_y_202_, v___x_203_);
v___x_205_ = lean_int_add(v_x_201_, v___x_204_);
lean_dec(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__7___lam__0___boxed(lean_object* v_x_206_, lean_object* v_y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Time_instHAddOffsetOffset__7___lam__0(v_x_206_, v_y_207_);
lean_dec(v_y_207_);
lean_dec(v_x_206_);
return v_res_208_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(60000u);
v___x_212_ = lean_nat_to_int(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__8___lam__0(lean_object* v_x_213_, lean_object* v_y_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
v___x_216_ = lean_int_mul(v_y_214_, v___x_215_);
v___x_217_ = lean_int_add(v_x_213_, v___x_216_);
lean_dec(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__8___lam__0___boxed(lean_object* v_x_218_, lean_object* v_y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Time_instHAddOffsetOffset__8___lam__0(v_x_218_, v_y_219_);
lean_dec(v_y_219_);
lean_dec(v_x_218_);
return v_res_220_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(3600000u);
v___x_224_ = lean_nat_to_int(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__9___lam__0(lean_object* v_x_225_, lean_object* v_y_226_){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
v___x_228_ = lean_int_mul(v_y_226_, v___x_227_);
v___x_229_ = lean_int_add(v_x_225_, v___x_228_);
lean_dec(v___x_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__9___lam__0___boxed(lean_object* v_x_230_, lean_object* v_y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Time_instHAddOffsetOffset__9___lam__0(v_x_230_, v_y_231_);
lean_dec(v_y_231_);
lean_dec(v_x_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__10___lam__0(lean_object* v_x_235_, lean_object* v_y_236_){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
v___x_238_ = lean_int_mul(v_y_236_, v___x_237_);
v___x_239_ = lean_int_add(v_x_235_, v___x_238_);
lean_dec(v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__10___lam__0___boxed(lean_object* v_x_240_, lean_object* v_y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_Time_instHAddOffsetOffset__10___lam__0(v_x_240_, v_y_241_);
lean_dec(v_y_241_);
lean_dec(v_x_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__11___lam__0(lean_object* v_x_245_, lean_object* v_y_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
v___x_248_ = lean_int_mul(v_y_246_, v___x_247_);
v___x_249_ = lean_int_add(v_x_245_, v___x_248_);
lean_dec(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__11___lam__0___boxed(lean_object* v_x_250_, lean_object* v_y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_Time_instHAddOffsetOffset__11___lam__0(v_x_250_, v_y_251_);
lean_dec(v_y_251_);
lean_dec(v_x_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__12___lam__0(lean_object* v_x_255_, lean_object* v_y_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
v___x_258_ = lean_int_mul(v_x_255_, v___x_257_);
v___x_259_ = lean_int_add(v___x_258_, v_y_256_);
lean_dec(v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__12___lam__0___boxed(lean_object* v_x_260_, lean_object* v_y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Std_Time_instHAddOffsetOffset__12___lam__0(v_x_260_, v_y_261_);
lean_dec(v_y_261_);
lean_dec(v_x_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__13___lam__0(lean_object* v_x_265_, lean_object* v_y_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
v___x_268_ = lean_int_mul(v_x_265_, v___x_267_);
v___x_269_ = lean_int_add(v___x_268_, v_y_266_);
lean_dec(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__13___lam__0___boxed(lean_object* v_x_270_, lean_object* v_y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Time_instHAddOffsetOffset__13___lam__0(v_x_270_, v_y_271_);
lean_dec(v_y_271_);
lean_dec(v_x_270_);
return v_res_272_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(60u);
v___x_276_ = lean_nat_to_int(v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__14___lam__0(lean_object* v_x_277_, lean_object* v_y_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
v___x_280_ = lean_int_mul(v_y_278_, v___x_279_);
v___x_281_ = lean_int_add(v_x_277_, v___x_280_);
lean_dec(v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__14___lam__0___boxed(lean_object* v_x_282_, lean_object* v_y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_Time_instHAddOffsetOffset__14___lam__0(v_x_282_, v_y_283_);
lean_dec(v_y_283_);
lean_dec(v_x_282_);
return v_res_284_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(3600u);
v___x_288_ = lean_nat_to_int(v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__15___lam__0(lean_object* v_x_289_, lean_object* v_y_290_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
v___x_292_ = lean_int_mul(v_y_290_, v___x_291_);
v___x_293_ = lean_int_add(v_x_289_, v___x_292_);
lean_dec(v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__15___lam__0___boxed(lean_object* v_x_294_, lean_object* v_y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Std_Time_instHAddOffsetOffset__15___lam__0(v_x_294_, v_y_295_);
lean_dec(v_y_295_);
lean_dec(v_x_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__16___lam__0(lean_object* v_x_299_, lean_object* v_y_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
v___x_302_ = lean_int_mul(v_y_300_, v___x_301_);
v___x_303_ = lean_int_add(v_x_299_, v___x_302_);
lean_dec(v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__16___lam__0___boxed(lean_object* v_x_304_, lean_object* v_y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Std_Time_instHAddOffsetOffset__16___lam__0(v_x_304_, v_y_305_);
lean_dec(v_y_305_);
lean_dec(v_x_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__17___lam__0(lean_object* v_x_309_, lean_object* v_y_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
v___x_312_ = lean_int_mul(v_y_310_, v___x_311_);
v___x_313_ = lean_int_add(v_x_309_, v___x_312_);
lean_dec(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__17___lam__0___boxed(lean_object* v_x_314_, lean_object* v_y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Std_Time_instHAddOffsetOffset__17___lam__0(v_x_314_, v_y_315_);
lean_dec(v_y_315_);
lean_dec(v_x_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__18___lam__0(lean_object* v_x_319_, lean_object* v_y_320_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
v___x_322_ = lean_int_mul(v_x_319_, v___x_321_);
v___x_323_ = lean_int_add(v___x_322_, v_y_320_);
lean_dec(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__18___lam__0___boxed(lean_object* v_x_324_, lean_object* v_y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Std_Time_instHAddOffsetOffset__18___lam__0(v_x_324_, v_y_325_);
lean_dec(v_y_325_);
lean_dec(v_x_324_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__19___lam__0(lean_object* v_x_329_, lean_object* v_y_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
v___x_332_ = lean_int_mul(v_x_329_, v___x_331_);
v___x_333_ = lean_int_add(v___x_332_, v_y_330_);
lean_dec(v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__19___lam__0___boxed(lean_object* v_x_334_, lean_object* v_y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_Time_instHAddOffsetOffset__19___lam__0(v_x_334_, v_y_335_);
lean_dec(v_y_335_);
lean_dec(v_x_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__20___lam__0(lean_object* v_x_339_, lean_object* v_y_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
v___x_342_ = lean_int_mul(v_x_339_, v___x_341_);
v___x_343_ = lean_int_add(v___x_342_, v_y_340_);
lean_dec(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__20___lam__0___boxed(lean_object* v_x_344_, lean_object* v_y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_Time_instHAddOffsetOffset__20___lam__0(v_x_344_, v_y_345_);
lean_dec(v_y_345_);
lean_dec(v_x_344_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__22___lam__0(lean_object* v_x_350_, lean_object* v_y_351_){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
v___x_353_ = lean_int_mul(v_y_351_, v___x_352_);
v___x_354_ = lean_int_add(v_x_350_, v___x_353_);
lean_dec(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__22___lam__0___boxed(lean_object* v_x_355_, lean_object* v_y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_Time_instHAddOffsetOffset__22___lam__0(v_x_355_, v_y_356_);
lean_dec(v_y_356_);
lean_dec(v_x_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__23___lam__0(lean_object* v_x_360_, lean_object* v_y_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
v___x_363_ = lean_int_mul(v_y_361_, v___x_362_);
v___x_364_ = lean_int_add(v_x_360_, v___x_363_);
lean_dec(v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__23___lam__0___boxed(lean_object* v_x_365_, lean_object* v_y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_Time_instHAddOffsetOffset__23___lam__0(v_x_365_, v_y_366_);
lean_dec(v_y_366_);
lean_dec(v_x_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__24___lam__0(lean_object* v_x_370_, lean_object* v_y_371_){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
v___x_373_ = lean_int_mul(v_x_370_, v___x_372_);
v___x_374_ = lean_int_add(v___x_373_, v_y_371_);
lean_dec(v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__24___lam__0___boxed(lean_object* v_x_375_, lean_object* v_y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Std_Time_instHAddOffsetOffset__24___lam__0(v_x_375_, v_y_376_);
lean_dec(v_y_376_);
lean_dec(v_x_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__25___lam__0(lean_object* v_x_380_, lean_object* v_y_381_){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
v___x_383_ = lean_int_mul(v_x_380_, v___x_382_);
v___x_384_ = lean_int_add(v___x_383_, v_y_381_);
lean_dec(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__25___lam__0___boxed(lean_object* v_x_385_, lean_object* v_y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_Time_instHAddOffsetOffset__25___lam__0(v_x_385_, v_y_386_);
lean_dec(v_y_386_);
lean_dec(v_x_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__26___lam__0(lean_object* v_x_390_, lean_object* v_y_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
v___x_393_ = lean_int_mul(v_x_390_, v___x_392_);
v___x_394_ = lean_int_add(v___x_393_, v_y_391_);
lean_dec(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__26___lam__0___boxed(lean_object* v_x_395_, lean_object* v_y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_Time_instHAddOffsetOffset__26___lam__0(v_x_395_, v_y_396_);
lean_dec(v_y_396_);
lean_dec(v_x_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__28___lam__0(lean_object* v_x_401_, lean_object* v_y_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
v___x_404_ = lean_int_mul(v_y_402_, v___x_403_);
v___x_405_ = lean_int_add(v_x_401_, v___x_404_);
lean_dec(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__28___lam__0___boxed(lean_object* v_x_406_, lean_object* v_y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Std_Time_instHAddOffsetOffset__28___lam__0(v_x_406_, v_y_407_);
lean_dec(v_y_407_);
lean_dec(v_x_406_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__29___lam__0(lean_object* v_x_411_, lean_object* v_y_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
v___x_414_ = lean_int_mul(v_y_412_, v___x_413_);
v___x_415_ = lean_int_add(v_x_411_, v___x_414_);
lean_dec(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__29___lam__0___boxed(lean_object* v_x_416_, lean_object* v_y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Time_instHAddOffsetOffset__29___lam__0(v_x_416_, v_y_417_);
lean_dec(v_y_417_);
lean_dec(v_x_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__30___lam__0(lean_object* v_x_421_, lean_object* v_y_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
v___x_424_ = lean_int_mul(v_x_421_, v___x_423_);
v___x_425_ = lean_int_add(v___x_424_, v_y_422_);
lean_dec(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__30___lam__0___boxed(lean_object* v_x_426_, lean_object* v_y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_Time_instHAddOffsetOffset__30___lam__0(v_x_426_, v_y_427_);
lean_dec(v_y_427_);
lean_dec(v_x_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__31___lam__0(lean_object* v_x_431_, lean_object* v_y_432_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
v___x_434_ = lean_int_mul(v_x_431_, v___x_433_);
v___x_435_ = lean_int_add(v___x_434_, v_y_432_);
lean_dec(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__31___lam__0___boxed(lean_object* v_x_436_, lean_object* v_y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_Time_instHAddOffsetOffset__31___lam__0(v_x_436_, v_y_437_);
lean_dec(v_y_437_);
lean_dec(v_x_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__32___lam__0(lean_object* v_x_441_, lean_object* v_y_442_){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
v___x_444_ = lean_int_mul(v_x_441_, v___x_443_);
v___x_445_ = lean_int_add(v___x_444_, v_y_442_);
lean_dec(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__32___lam__0___boxed(lean_object* v_x_446_, lean_object* v_y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_Time_instHAddOffsetOffset__32___lam__0(v_x_446_, v_y_447_);
lean_dec(v_y_447_);
lean_dec(v_x_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__33___lam__0(lean_object* v_x_451_, lean_object* v_y_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
v___x_454_ = lean_int_mul(v_x_451_, v___x_453_);
v___x_455_ = lean_int_add(v___x_454_, v_y_452_);
lean_dec(v___x_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__33___lam__0___boxed(lean_object* v_x_456_, lean_object* v_y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_Time_instHAddOffsetOffset__33___lam__0(v_x_456_, v_y_457_);
lean_dec(v_y_457_);
lean_dec(v_x_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__34___lam__0(lean_object* v_x_461_, lean_object* v_y_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
v___x_464_ = lean_int_mul(v_x_461_, v___x_463_);
v___x_465_ = lean_int_add(v___x_464_, v_y_462_);
lean_dec(v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__34___lam__0___boxed(lean_object* v_x_466_, lean_object* v_y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_Time_instHAddOffsetOffset__34___lam__0(v_x_466_, v_y_467_);
lean_dec(v_y_467_);
lean_dec(v_x_466_);
return v_res_468_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = lean_unsigned_to_nat(7u);
v___x_472_ = lean_nat_to_int(v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__35___lam__0(lean_object* v_x_473_, lean_object* v_y_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
v___x_476_ = lean_int_mul(v_y_474_, v___x_475_);
v___x_477_ = lean_int_add(v_x_473_, v___x_476_);
lean_dec(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__35___lam__0___boxed(lean_object* v_x_478_, lean_object* v_y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_Time_instHAddOffsetOffset__35___lam__0(v_x_478_, v_y_479_);
lean_dec(v_y_479_);
lean_dec(v_x_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__36___lam__0(lean_object* v_x_483_, lean_object* v_y_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
v___x_486_ = lean_int_mul(v_x_483_, v___x_485_);
v___x_487_ = lean_int_add(v___x_486_, v_y_484_);
lean_dec(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__36___lam__0___boxed(lean_object* v_x_488_, lean_object* v_y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_Time_instHAddOffsetOffset__36___lam__0(v_x_488_, v_y_489_);
lean_dec(v_y_489_);
lean_dec(v_x_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__37___lam__0(lean_object* v_x_493_, lean_object* v_y_494_){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
v___x_496_ = lean_int_mul(v_x_493_, v___x_495_);
v___x_497_ = lean_int_add(v___x_496_, v_y_494_);
lean_dec(v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__37___lam__0___boxed(lean_object* v_x_498_, lean_object* v_y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Time_instHAddOffsetOffset__37___lam__0(v_x_498_, v_y_499_);
lean_dec(v_y_499_);
lean_dec(v_x_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__38___lam__0(lean_object* v_x_503_, lean_object* v_y_504_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
v___x_506_ = lean_int_mul(v_x_503_, v___x_505_);
v___x_507_ = lean_int_add(v___x_506_, v_y_504_);
lean_dec(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__38___lam__0___boxed(lean_object* v_x_508_, lean_object* v_y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_Time_instHAddOffsetOffset__38___lam__0(v_x_508_, v_y_509_);
lean_dec(v_y_509_);
lean_dec(v_x_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__39___lam__0(lean_object* v_x_513_, lean_object* v_y_514_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
v___x_516_ = lean_int_mul(v_x_513_, v___x_515_);
v___x_517_ = lean_int_add(v___x_516_, v_y_514_);
lean_dec(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__39___lam__0___boxed(lean_object* v_x_518_, lean_object* v_y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_Time_instHAddOffsetOffset__39___lam__0(v_x_518_, v_y_519_);
lean_dec(v_y_519_);
lean_dec(v_x_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__40___lam__0(lean_object* v_x_523_, lean_object* v_y_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
v___x_526_ = lean_int_mul(v_x_523_, v___x_525_);
v___x_527_ = lean_int_add(v___x_526_, v_y_524_);
lean_dec(v___x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__40___lam__0___boxed(lean_object* v_x_528_, lean_object* v_y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_Time_instHAddOffsetOffset__40___lam__0(v_x_528_, v_y_529_);
lean_dec(v_y_529_);
lean_dec(v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__41___lam__0(lean_object* v_x_533_, lean_object* v_y_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
v___x_536_ = lean_int_mul(v_x_533_, v___x_535_);
v___x_537_ = lean_int_add(v___x_536_, v_y_534_);
lean_dec(v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__41___lam__0___boxed(lean_object* v_x_538_, lean_object* v_y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_Time_instHAddOffsetOffset__41___lam__0(v_x_538_, v_y_539_);
lean_dec(v_y_539_);
lean_dec(v_x_538_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset___lam__0(lean_object* v_x_543_, lean_object* v_y_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
v___x_546_ = lean_int_mul(v_y_544_, v___x_545_);
v___x_547_ = lean_int_sub(v_x_543_, v___x_546_);
lean_dec(v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset___lam__0___boxed(lean_object* v_x_548_, lean_object* v_y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_Time_instHSubOffsetOffset___lam__0(v_x_548_, v_y_549_);
lean_dec(v_y_549_);
lean_dec(v_x_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__1___lam__0(lean_object* v_x_553_, lean_object* v_y_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
v___x_556_ = lean_int_mul(v_y_554_, v___x_555_);
v___x_557_ = lean_int_sub(v_x_553_, v___x_556_);
lean_dec(v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__1___lam__0___boxed(lean_object* v_x_558_, lean_object* v_y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Time_instHSubOffsetOffset__1___lam__0(v_x_558_, v_y_559_);
lean_dec(v_y_559_);
lean_dec(v_x_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__2___lam__0(lean_object* v_x_563_, lean_object* v_y_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
v___x_566_ = lean_int_mul(v_y_564_, v___x_565_);
v___x_567_ = lean_int_sub(v_x_563_, v___x_566_);
lean_dec(v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__2___lam__0___boxed(lean_object* v_x_568_, lean_object* v_y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_Time_instHSubOffsetOffset__2___lam__0(v_x_568_, v_y_569_);
lean_dec(v_y_569_);
lean_dec(v_x_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__3___lam__0(lean_object* v_x_573_, lean_object* v_y_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
v___x_576_ = lean_int_mul(v_y_574_, v___x_575_);
v___x_577_ = lean_int_sub(v_x_573_, v___x_576_);
lean_dec(v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__3___lam__0___boxed(lean_object* v_x_578_, lean_object* v_y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_Time_instHSubOffsetOffset__3___lam__0(v_x_578_, v_y_579_);
lean_dec(v_y_579_);
lean_dec(v_x_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__4___lam__0(lean_object* v_x_583_, lean_object* v_y_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
v___x_586_ = lean_int_mul(v_y_584_, v___x_585_);
v___x_587_ = lean_int_sub(v_x_583_, v___x_586_);
lean_dec(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__4___lam__0___boxed(lean_object* v_x_588_, lean_object* v_y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_Time_instHSubOffsetOffset__4___lam__0(v_x_588_, v_y_589_);
lean_dec(v_y_589_);
lean_dec(v_x_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__5___lam__0(lean_object* v_x_593_, lean_object* v_y_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
v___x_596_ = lean_int_mul(v_y_594_, v___x_595_);
v___x_597_ = lean_int_sub(v_x_593_, v___x_596_);
lean_dec(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__5___lam__0___boxed(lean_object* v_x_598_, lean_object* v_y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_Time_instHSubOffsetOffset__5___lam__0(v_x_598_, v_y_599_);
lean_dec(v_y_599_);
lean_dec(v_x_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__6___lam__0(lean_object* v_x_603_, lean_object* v_y_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
v___x_606_ = lean_int_mul(v_x_603_, v___x_605_);
v___x_607_ = lean_int_sub(v___x_606_, v_y_604_);
lean_dec(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__6___lam__0___boxed(lean_object* v_x_608_, lean_object* v_y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_Time_instHSubOffsetOffset__6___lam__0(v_x_608_, v_y_609_);
lean_dec(v_y_609_);
lean_dec(v_x_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__7___lam__0(lean_object* v_x_613_, lean_object* v_y_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
v___x_616_ = lean_int_mul(v_y_614_, v___x_615_);
v___x_617_ = lean_int_sub(v_x_613_, v___x_616_);
lean_dec(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__7___lam__0___boxed(lean_object* v_x_618_, lean_object* v_y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Time_instHSubOffsetOffset__7___lam__0(v_x_618_, v_y_619_);
lean_dec(v_y_619_);
lean_dec(v_x_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__8___lam__0(lean_object* v_x_623_, lean_object* v_y_624_){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
v___x_626_ = lean_int_mul(v_y_624_, v___x_625_);
v___x_627_ = lean_int_sub(v_x_623_, v___x_626_);
lean_dec(v___x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__8___lam__0___boxed(lean_object* v_x_628_, lean_object* v_y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_Time_instHSubOffsetOffset__8___lam__0(v_x_628_, v_y_629_);
lean_dec(v_y_629_);
lean_dec(v_x_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__9___lam__0(lean_object* v_x_633_, lean_object* v_y_634_){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
v___x_636_ = lean_int_mul(v_y_634_, v___x_635_);
v___x_637_ = lean_int_sub(v_x_633_, v___x_636_);
lean_dec(v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__9___lam__0___boxed(lean_object* v_x_638_, lean_object* v_y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_Time_instHSubOffsetOffset__9___lam__0(v_x_638_, v_y_639_);
lean_dec(v_y_639_);
lean_dec(v_x_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__10___lam__0(lean_object* v_x_643_, lean_object* v_y_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
v___x_646_ = lean_int_mul(v_y_644_, v___x_645_);
v___x_647_ = lean_int_sub(v_x_643_, v___x_646_);
lean_dec(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__10___lam__0___boxed(lean_object* v_x_648_, lean_object* v_y_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Std_Time_instHSubOffsetOffset__10___lam__0(v_x_648_, v_y_649_);
lean_dec(v_y_649_);
lean_dec(v_x_648_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__11___lam__0(lean_object* v_x_653_, lean_object* v_y_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
v___x_656_ = lean_int_mul(v_y_654_, v___x_655_);
v___x_657_ = lean_int_sub(v_x_653_, v___x_656_);
lean_dec(v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__11___lam__0___boxed(lean_object* v_x_658_, lean_object* v_y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_Time_instHSubOffsetOffset__11___lam__0(v_x_658_, v_y_659_);
lean_dec(v_y_659_);
lean_dec(v_x_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__12___lam__0(lean_object* v_x_663_, lean_object* v_y_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
v___x_666_ = lean_int_mul(v_x_663_, v___x_665_);
v___x_667_ = lean_int_sub(v___x_666_, v_y_664_);
lean_dec(v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__12___lam__0___boxed(lean_object* v_x_668_, lean_object* v_y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Std_Time_instHSubOffsetOffset__12___lam__0(v_x_668_, v_y_669_);
lean_dec(v_y_669_);
lean_dec(v_x_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__13___lam__0(lean_object* v_x_673_, lean_object* v_y_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
v___x_676_ = lean_int_mul(v_x_673_, v___x_675_);
v___x_677_ = lean_int_sub(v___x_676_, v_y_674_);
lean_dec(v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__13___lam__0___boxed(lean_object* v_x_678_, lean_object* v_y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_Time_instHSubOffsetOffset__13___lam__0(v_x_678_, v_y_679_);
lean_dec(v_y_679_);
lean_dec(v_x_678_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__14___lam__0(lean_object* v_x_683_, lean_object* v_y_684_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
v___x_686_ = lean_int_mul(v_y_684_, v___x_685_);
v___x_687_ = lean_int_sub(v_x_683_, v___x_686_);
lean_dec(v___x_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__14___lam__0___boxed(lean_object* v_x_688_, lean_object* v_y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_Time_instHSubOffsetOffset__14___lam__0(v_x_688_, v_y_689_);
lean_dec(v_y_689_);
lean_dec(v_x_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__15___lam__0(lean_object* v_x_693_, lean_object* v_y_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
v___x_696_ = lean_int_mul(v_y_694_, v___x_695_);
v___x_697_ = lean_int_sub(v_x_693_, v___x_696_);
lean_dec(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__15___lam__0___boxed(lean_object* v_x_698_, lean_object* v_y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Std_Time_instHSubOffsetOffset__15___lam__0(v_x_698_, v_y_699_);
lean_dec(v_y_699_);
lean_dec(v_x_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__16___lam__0(lean_object* v_x_703_, lean_object* v_y_704_){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
v___x_706_ = lean_int_mul(v_y_704_, v___x_705_);
v___x_707_ = lean_int_sub(v_x_703_, v___x_706_);
lean_dec(v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__16___lam__0___boxed(lean_object* v_x_708_, lean_object* v_y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_Time_instHSubOffsetOffset__16___lam__0(v_x_708_, v_y_709_);
lean_dec(v_y_709_);
lean_dec(v_x_708_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__17___lam__0(lean_object* v_x_713_, lean_object* v_y_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
v___x_716_ = lean_int_mul(v_y_714_, v___x_715_);
v___x_717_ = lean_int_sub(v_x_713_, v___x_716_);
lean_dec(v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__17___lam__0___boxed(lean_object* v_x_718_, lean_object* v_y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_Time_instHSubOffsetOffset__17___lam__0(v_x_718_, v_y_719_);
lean_dec(v_y_719_);
lean_dec(v_x_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__18___lam__0(lean_object* v_x_723_, lean_object* v_y_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
v___x_726_ = lean_int_mul(v_x_723_, v___x_725_);
v___x_727_ = lean_int_sub(v___x_726_, v_y_724_);
lean_dec(v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__18___lam__0___boxed(lean_object* v_x_728_, lean_object* v_y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_Time_instHSubOffsetOffset__18___lam__0(v_x_728_, v_y_729_);
lean_dec(v_y_729_);
lean_dec(v_x_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__19___lam__0(lean_object* v_x_733_, lean_object* v_y_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
v___x_736_ = lean_int_mul(v_x_733_, v___x_735_);
v___x_737_ = lean_int_sub(v___x_736_, v_y_734_);
lean_dec(v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__19___lam__0___boxed(lean_object* v_x_738_, lean_object* v_y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_Time_instHSubOffsetOffset__19___lam__0(v_x_738_, v_y_739_);
lean_dec(v_y_739_);
lean_dec(v_x_738_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__20___lam__0(lean_object* v_x_743_, lean_object* v_y_744_){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
v___x_746_ = lean_int_mul(v_x_743_, v___x_745_);
v___x_747_ = lean_int_sub(v___x_746_, v_y_744_);
lean_dec(v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__20___lam__0___boxed(lean_object* v_x_748_, lean_object* v_y_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_Time_instHSubOffsetOffset__20___lam__0(v_x_748_, v_y_749_);
lean_dec(v_y_749_);
lean_dec(v_x_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__22___lam__0(lean_object* v_x_754_, lean_object* v_y_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_756_ = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
v___x_757_ = lean_int_mul(v_y_755_, v___x_756_);
v___x_758_ = lean_int_sub(v_x_754_, v___x_757_);
lean_dec(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__22___lam__0___boxed(lean_object* v_x_759_, lean_object* v_y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Std_Time_instHSubOffsetOffset__22___lam__0(v_x_759_, v_y_760_);
lean_dec(v_y_760_);
lean_dec(v_x_759_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__23___lam__0(lean_object* v_x_764_, lean_object* v_y_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
v___x_767_ = lean_int_mul(v_y_765_, v___x_766_);
v___x_768_ = lean_int_sub(v_x_764_, v___x_767_);
lean_dec(v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__23___lam__0___boxed(lean_object* v_x_769_, lean_object* v_y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_Time_instHSubOffsetOffset__23___lam__0(v_x_769_, v_y_770_);
lean_dec(v_y_770_);
lean_dec(v_x_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__24___lam__0(lean_object* v_x_774_, lean_object* v_y_775_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_776_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
v___x_777_ = lean_int_mul(v_x_774_, v___x_776_);
v___x_778_ = lean_int_sub(v___x_777_, v_y_775_);
lean_dec(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__24___lam__0___boxed(lean_object* v_x_779_, lean_object* v_y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Std_Time_instHSubOffsetOffset__24___lam__0(v_x_779_, v_y_780_);
lean_dec(v_y_780_);
lean_dec(v_x_779_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__25___lam__0(lean_object* v_x_784_, lean_object* v_y_785_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
v___x_787_ = lean_int_mul(v_x_784_, v___x_786_);
v___x_788_ = lean_int_sub(v___x_787_, v_y_785_);
lean_dec(v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__25___lam__0___boxed(lean_object* v_x_789_, lean_object* v_y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_Time_instHSubOffsetOffset__25___lam__0(v_x_789_, v_y_790_);
lean_dec(v_y_790_);
lean_dec(v_x_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__26___lam__0(lean_object* v_x_794_, lean_object* v_y_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
v___x_797_ = lean_int_mul(v_x_794_, v___x_796_);
v___x_798_ = lean_int_sub(v___x_797_, v_y_795_);
lean_dec(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__26___lam__0___boxed(lean_object* v_x_799_, lean_object* v_y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Std_Time_instHSubOffsetOffset__26___lam__0(v_x_799_, v_y_800_);
lean_dec(v_y_800_);
lean_dec(v_x_799_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__28___lam__0(lean_object* v_x_805_, lean_object* v_y_806_){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
v___x_808_ = lean_int_mul(v_y_806_, v___x_807_);
v___x_809_ = lean_int_sub(v_x_805_, v___x_808_);
lean_dec(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__28___lam__0___boxed(lean_object* v_x_810_, lean_object* v_y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Std_Time_instHSubOffsetOffset__28___lam__0(v_x_810_, v_y_811_);
lean_dec(v_y_811_);
lean_dec(v_x_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__29___lam__0(lean_object* v_x_815_, lean_object* v_y_816_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
v___x_818_ = lean_int_mul(v_y_816_, v___x_817_);
v___x_819_ = lean_int_sub(v_x_815_, v___x_818_);
lean_dec(v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__29___lam__0___boxed(lean_object* v_x_820_, lean_object* v_y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_Time_instHSubOffsetOffset__29___lam__0(v_x_820_, v_y_821_);
lean_dec(v_y_821_);
lean_dec(v_x_820_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__30___lam__0(lean_object* v_x_825_, lean_object* v_y_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
v___x_828_ = lean_int_mul(v_x_825_, v___x_827_);
v___x_829_ = lean_int_sub(v___x_828_, v_y_826_);
lean_dec(v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__30___lam__0___boxed(lean_object* v_x_830_, lean_object* v_y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_Time_instHSubOffsetOffset__30___lam__0(v_x_830_, v_y_831_);
lean_dec(v_y_831_);
lean_dec(v_x_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__31___lam__0(lean_object* v_x_835_, lean_object* v_y_836_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
v___x_838_ = lean_int_mul(v_x_835_, v___x_837_);
v___x_839_ = lean_int_sub(v___x_838_, v_y_836_);
lean_dec(v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__31___lam__0___boxed(lean_object* v_x_840_, lean_object* v_y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_Time_instHSubOffsetOffset__31___lam__0(v_x_840_, v_y_841_);
lean_dec(v_y_841_);
lean_dec(v_x_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__32___lam__0(lean_object* v_x_845_, lean_object* v_y_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_847_ = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
v___x_848_ = lean_int_mul(v_x_845_, v___x_847_);
v___x_849_ = lean_int_sub(v___x_848_, v_y_846_);
lean_dec(v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__32___lam__0___boxed(lean_object* v_x_850_, lean_object* v_y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_Time_instHSubOffsetOffset__32___lam__0(v_x_850_, v_y_851_);
lean_dec(v_y_851_);
lean_dec(v_x_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__33___lam__0(lean_object* v_x_855_, lean_object* v_y_856_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
v___x_858_ = lean_int_mul(v_x_855_, v___x_857_);
v___x_859_ = lean_int_sub(v___x_858_, v_y_856_);
lean_dec(v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__33___lam__0___boxed(lean_object* v_x_860_, lean_object* v_y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_Time_instHSubOffsetOffset__33___lam__0(v_x_860_, v_y_861_);
lean_dec(v_y_861_);
lean_dec(v_x_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__34___lam__0(lean_object* v_x_865_, lean_object* v_y_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
v___x_868_ = lean_int_mul(v_x_865_, v___x_867_);
v___x_869_ = lean_int_sub(v___x_868_, v_y_866_);
lean_dec(v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__34___lam__0___boxed(lean_object* v_x_870_, lean_object* v_y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_Time_instHSubOffsetOffset__34___lam__0(v_x_870_, v_y_871_);
lean_dec(v_y_871_);
lean_dec(v_x_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__35___lam__0(lean_object* v_x_875_, lean_object* v_y_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
v___x_878_ = lean_int_mul(v_y_876_, v___x_877_);
v___x_879_ = lean_int_sub(v_x_875_, v___x_878_);
lean_dec(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__35___lam__0___boxed(lean_object* v_x_880_, lean_object* v_y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_Time_instHSubOffsetOffset__35___lam__0(v_x_880_, v_y_881_);
lean_dec(v_y_881_);
lean_dec(v_x_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__36___lam__0(lean_object* v_x_885_, lean_object* v_y_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
v___x_888_ = lean_int_mul(v_x_885_, v___x_887_);
v___x_889_ = lean_int_sub(v___x_888_, v_y_886_);
lean_dec(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__36___lam__0___boxed(lean_object* v_x_890_, lean_object* v_y_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Std_Time_instHSubOffsetOffset__36___lam__0(v_x_890_, v_y_891_);
lean_dec(v_y_891_);
lean_dec(v_x_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__37___lam__0(lean_object* v_x_895_, lean_object* v_y_896_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
v___x_898_ = lean_int_mul(v_x_895_, v___x_897_);
v___x_899_ = lean_int_sub(v___x_898_, v_y_896_);
lean_dec(v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__37___lam__0___boxed(lean_object* v_x_900_, lean_object* v_y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_Time_instHSubOffsetOffset__37___lam__0(v_x_900_, v_y_901_);
lean_dec(v_y_901_);
lean_dec(v_x_900_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__38___lam__0(lean_object* v_x_905_, lean_object* v_y_906_){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
v___x_908_ = lean_int_mul(v_x_905_, v___x_907_);
v___x_909_ = lean_int_sub(v___x_908_, v_y_906_);
lean_dec(v___x_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__38___lam__0___boxed(lean_object* v_x_910_, lean_object* v_y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Std_Time_instHSubOffsetOffset__38___lam__0(v_x_910_, v_y_911_);
lean_dec(v_y_911_);
lean_dec(v_x_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__39___lam__0(lean_object* v_x_915_, lean_object* v_y_916_){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
v___x_918_ = lean_int_mul(v_x_915_, v___x_917_);
v___x_919_ = lean_int_sub(v___x_918_, v_y_916_);
lean_dec(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__39___lam__0___boxed(lean_object* v_x_920_, lean_object* v_y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Std_Time_instHSubOffsetOffset__39___lam__0(v_x_920_, v_y_921_);
lean_dec(v_y_921_);
lean_dec(v_x_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__40___lam__0(lean_object* v_x_925_, lean_object* v_y_926_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
v___x_928_ = lean_int_mul(v_x_925_, v___x_927_);
v___x_929_ = lean_int_sub(v___x_928_, v_y_926_);
lean_dec(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__40___lam__0___boxed(lean_object* v_x_930_, lean_object* v_y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Std_Time_instHSubOffsetOffset__40___lam__0(v_x_930_, v_y_931_);
lean_dec(v_y_931_);
lean_dec(v_x_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__41___lam__0(lean_object* v_x_935_, lean_object* v_y_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
v___x_938_ = lean_int_mul(v_x_935_, v___x_937_);
v___x_939_ = lean_int_sub(v___x_938_, v_y_936_);
lean_dec(v___x_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__41___lam__0___boxed(lean_object* v_x_940_, lean_object* v_y_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_Time_instHSubOffsetOffset__41___lam__0(v_x_940_, v_y_941_);
lean_dec(v_y_941_);
lean_dec(v_x_940_);
return v_res_942_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_ValidDate(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Time_Date_Unit_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_ValidDate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Date_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Date_Unit_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Date_ValidDate(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Date_Unit_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_ValidDate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Date_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Date_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Date_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

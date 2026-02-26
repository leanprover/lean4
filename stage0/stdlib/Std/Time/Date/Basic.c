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
static lean_once_cell_t l_Std_Time_Nanosecond_Offset_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Nanosecond_Offset_toDays___closed__0;
lean_object* lean_int_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toDays___boxed(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
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
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffset___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffset = (const lean_object*)&l_Std_Time_instHAddOffset___closed__0_value;
static lean_once_cell_t l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instHAddOffsetOffset___lam__0___closed__0;
lean_object* lean_int_add(lean_object*, lean_object*);
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
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffset__1 = (const lean_object*)&l_Std_Time_instHAddOffset___closed__0_value;
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
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffset__2 = (const lean_object*)&l_Std_Time_instHAddOffset___closed__0_value;
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
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffset__3 = (const lean_object*)&l_Std_Time_instHAddOffset___closed__0_value;
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
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffset__4 = (const lean_object*)&l_Std_Time_instHAddOffset___closed__0_value;
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
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffset__5 = (const lean_object*)&l_Std_Time_instHAddOffset___closed__0_value;
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
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffset__6 = (const lean_object*)&l_Std_Time_instHAddOffset___closed__0_value;
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instHSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffset___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffset = (const lean_object*)&l_Std_Time_instHSubOffset___closed__0_value;
lean_object* lean_int_sub(lean_object*, lean_object*);
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
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffset__1 = (const lean_object*)&l_Std_Time_instHSubOffset___closed__0_value;
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
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffset__2 = (const lean_object*)&l_Std_Time_instHSubOffset___closed__0_value;
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
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffset__3 = (const lean_object*)&l_Std_Time_instHSubOffset___closed__0_value;
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
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffset__4 = (const lean_object*)&l_Std_Time_instHSubOffset___closed__0_value;
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
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffset__5 = (const lean_object*)&l_Std_Time_instHSubOffset___closed__0_value;
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
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffset__6 = (const lean_object*)&l_Std_Time_instHSubOffset___closed__0_value;
static lean_object* _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_cstr_to_nat("86400000000000");
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toDays(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
x_3 = lean_int_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toDays___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Nanosecond_Offset_toDays(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofDays(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofDays___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Nanosecond_Offset_ofDays(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_cstr_to_nat("604800000000000");
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
x_3 = lean_int_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_toWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Nanosecond_Offset_toWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Nanosecond_Offset_ofWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Nanosecond_Offset_ofWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Millisecond_Offset_toDays___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(86400000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toDays(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
x_3 = lean_int_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toDays___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Millisecond_Offset_toDays(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofDays(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofDays___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Millisecond_Offset_ofDays(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(604800000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
x_3 = lean_int_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_toWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Millisecond_Offset_toWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Millisecond_Offset_ofWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Millisecond_Offset_ofWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Second_Offset_toDays___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(86400u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toDays(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
x_3 = lean_int_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toDays___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Second_Offset_toDays(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofDays(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofDays___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Second_Offset_ofDays(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Second_Offset_toWeeks___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(604800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
x_3 = lean_int_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_toWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Second_Offset_toWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Second_Offset_ofWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Second_Offset_ofWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Minute_Offset_toDays___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1440u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toDays(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
x_3 = lean_int_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toDays___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Minute_Offset_toDays(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofDays(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofDays___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Minute_Offset_ofDays(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Minute_Offset_toWeeks___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10080u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
x_3 = lean_int_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_toWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Minute_Offset_toWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Minute_Offset_ofWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Minute_Offset_ofWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Hour_Offset_toDays___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(24u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toDays(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
x_3 = lean_int_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toDays___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Hour_Offset_toDays(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofDays(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofDays___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Hour_Offset_ofDays(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_Hour_Offset_toWeeks___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(168u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
x_3 = lean_int_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_toWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Hour_Offset_toWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofWeeks(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
x_3 = lean_int_mul(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Hour_Offset_ofWeeks___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_Hour_Offset_ofWeeks(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__1___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_cstr_to_nat("60000000000");
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__2___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__2___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_cstr_to_nat("3600000000000");
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__3___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__3___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__4___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__4___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__4___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__5___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__5___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__6___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__6___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__6___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__7___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__7___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__7___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(60000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__8___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__8___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3600000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__9___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__9___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__9___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__10___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__10___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__10___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__11___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__11___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__11___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__12___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__12___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__12___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__13___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__13___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__13___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(60u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__14___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__14___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__14___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__15___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__15___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__15___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__16___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__16___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__16___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__17___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__17___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__17___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__18___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__18___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__18___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__19___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__19___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__19___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__20___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__20___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__20___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__22___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__22___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__22___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__23___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__23___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__23___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__24___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__24___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__24___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__25___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__25___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__25___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__26___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__26___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__26___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__28___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__28___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__28___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__29___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__29___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__29___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__30___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__30___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__30___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__31___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__31___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__31___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__32___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__32___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__32___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__33___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__33___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__33___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__34___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__34___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__34___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__35___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_add(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__35___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__35___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__36___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__36___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__36___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__37___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__37___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__37___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__38___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__38___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__38___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__39___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__39___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__39___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__40___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__40___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__40___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__41___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_add(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__41___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHAddOffsetOffset__41___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__1___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__2___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__2___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__2___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__3___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__3___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__3___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__4___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__4___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__4___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__5___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__5___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__5___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__6___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__6___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__6___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__7___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__7___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__7___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__8___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__8___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__8___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__9___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__9___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__9___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__10___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__10___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__10___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__11___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__11___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__11___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__12___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__12___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__12___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__13___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__13___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__13___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__14___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__14___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__14___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__15___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__15___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__15___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__16___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__16___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__16___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__17___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__17___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__17___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__18___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__18___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__18___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__19___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__19___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__19___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__20___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__20___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__20___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__22___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__22___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__22___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__23___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__23___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__23___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__24___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__24___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__24___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__25___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__25___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__25___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__26___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__26___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__26___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__28___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__28___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__28___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__29___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__29___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__29___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__30___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__30___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__30___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__31___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__31___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__31___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__32___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__32___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__32___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__33___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__33___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__33___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__34___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__34___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__34___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__35___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
x_4 = lean_int_mul(x_2, x_3);
x_5 = lean_int_sub(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__35___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__35___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__36___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__36___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__36___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__37___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__37___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__37___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__38___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__38___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__38___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__39___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__39___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__39___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__40___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__40___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__40___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__41___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
x_4 = lean_int_mul(x_1, x_3);
x_5 = lean_int_sub(x_4, x_2);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__41___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Time_instHSubOffsetOffset__41___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

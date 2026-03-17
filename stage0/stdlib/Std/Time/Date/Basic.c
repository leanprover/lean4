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
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_Time_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_add___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHAddOffset___closed__0 = (const lean_object*)&l_Std_Time_instHAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHAddOffset = (const lean_object*)&l_Std_Time_instHAddOffset___closed__0_value;
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
static const lean_closure_object l_Std_Time_instHSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_sub___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instHSubOffset___closed__0 = (const lean_object*)&l_Std_Time_instHSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instHSubOffset = (const lean_object*)&l_Std_Time_instHSubOffset___closed__0_value;
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
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1000000u);
v___x_124_ = lean_nat_to_int(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset___lam__0(lean_object* v_x_125_, lean_object* v_y_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
v___x_128_ = lean_int_mul(v_y_126_, v___x_127_);
v___x_129_ = lean_int_add(v_x_125_, v___x_128_);
lean_dec(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset___lam__0___boxed(lean_object* v_x_130_, lean_object* v_y_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Std_Time_instHAddOffsetOffset___lam__0(v_x_130_, v_y_131_);
lean_dec(v_y_131_);
lean_dec(v_x_130_);
return v_res_132_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(1000000000u);
v___x_136_ = lean_nat_to_int(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__1___lam__0(lean_object* v_x_137_, lean_object* v_y_138_){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
v___x_140_ = lean_int_mul(v_y_138_, v___x_139_);
v___x_141_ = lean_int_add(v_x_137_, v___x_140_);
lean_dec(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__1___lam__0___boxed(lean_object* v_x_142_, lean_object* v_y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_Time_instHAddOffsetOffset__1___lam__0(v_x_142_, v_y_143_);
lean_dec(v_y_143_);
lean_dec(v_x_142_);
return v_res_144_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_cstr_to_nat("60000000000");
v___x_148_ = lean_nat_to_int(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__2___lam__0(lean_object* v_x_149_, lean_object* v_y_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
v___x_152_ = lean_int_mul(v_y_150_, v___x_151_);
v___x_153_ = lean_int_add(v_x_149_, v___x_152_);
lean_dec(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__2___lam__0___boxed(lean_object* v_x_154_, lean_object* v_y_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Time_instHAddOffsetOffset__2___lam__0(v_x_154_, v_y_155_);
lean_dec(v_y_155_);
lean_dec(v_x_154_);
return v_res_156_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_cstr_to_nat("3600000000000");
v___x_160_ = lean_nat_to_int(v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__3___lam__0(lean_object* v_x_161_, lean_object* v_y_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
v___x_164_ = lean_int_mul(v_y_162_, v___x_163_);
v___x_165_ = lean_int_add(v_x_161_, v___x_164_);
lean_dec(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__3___lam__0___boxed(lean_object* v_x_166_, lean_object* v_y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Std_Time_instHAddOffsetOffset__3___lam__0(v_x_166_, v_y_167_);
lean_dec(v_y_167_);
lean_dec(v_x_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__4___lam__0(lean_object* v_x_171_, lean_object* v_y_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
v___x_174_ = lean_int_mul(v_y_172_, v___x_173_);
v___x_175_ = lean_int_add(v_x_171_, v___x_174_);
lean_dec(v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__4___lam__0___boxed(lean_object* v_x_176_, lean_object* v_y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Time_instHAddOffsetOffset__4___lam__0(v_x_176_, v_y_177_);
lean_dec(v_y_177_);
lean_dec(v_x_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__5___lam__0(lean_object* v_x_181_, lean_object* v_y_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
v___x_184_ = lean_int_mul(v_y_182_, v___x_183_);
v___x_185_ = lean_int_add(v_x_181_, v___x_184_);
lean_dec(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__5___lam__0___boxed(lean_object* v_x_186_, lean_object* v_y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_Time_instHAddOffsetOffset__5___lam__0(v_x_186_, v_y_187_);
lean_dec(v_y_187_);
lean_dec(v_x_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__6___lam__0(lean_object* v_x_191_, lean_object* v_y_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
v___x_194_ = lean_int_mul(v_x_191_, v___x_193_);
v___x_195_ = lean_int_add(v___x_194_, v_y_192_);
lean_dec(v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__6___lam__0___boxed(lean_object* v_x_196_, lean_object* v_y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Time_instHAddOffsetOffset__6___lam__0(v_x_196_, v_y_197_);
lean_dec(v_y_197_);
lean_dec(v_x_196_);
return v_res_198_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(1000u);
v___x_203_ = lean_nat_to_int(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__7___lam__0(lean_object* v_x_204_, lean_object* v_y_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
v___x_207_ = lean_int_mul(v_y_205_, v___x_206_);
v___x_208_ = lean_int_add(v_x_204_, v___x_207_);
lean_dec(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__7___lam__0___boxed(lean_object* v_x_209_, lean_object* v_y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Std_Time_instHAddOffsetOffset__7___lam__0(v_x_209_, v_y_210_);
lean_dec(v_y_210_);
lean_dec(v_x_209_);
return v_res_211_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(60000u);
v___x_215_ = lean_nat_to_int(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__8___lam__0(lean_object* v_x_216_, lean_object* v_y_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
v___x_219_ = lean_int_mul(v_y_217_, v___x_218_);
v___x_220_ = lean_int_add(v_x_216_, v___x_219_);
lean_dec(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__8___lam__0___boxed(lean_object* v_x_221_, lean_object* v_y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Std_Time_instHAddOffsetOffset__8___lam__0(v_x_221_, v_y_222_);
lean_dec(v_y_222_);
lean_dec(v_x_221_);
return v_res_223_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_unsigned_to_nat(3600000u);
v___x_227_ = lean_nat_to_int(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__9___lam__0(lean_object* v_x_228_, lean_object* v_y_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
v___x_231_ = lean_int_mul(v_y_229_, v___x_230_);
v___x_232_ = lean_int_add(v_x_228_, v___x_231_);
lean_dec(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__9___lam__0___boxed(lean_object* v_x_233_, lean_object* v_y_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Time_instHAddOffsetOffset__9___lam__0(v_x_233_, v_y_234_);
lean_dec(v_y_234_);
lean_dec(v_x_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__10___lam__0(lean_object* v_x_238_, lean_object* v_y_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
v___x_241_ = lean_int_mul(v_y_239_, v___x_240_);
v___x_242_ = lean_int_add(v_x_238_, v___x_241_);
lean_dec(v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__10___lam__0___boxed(lean_object* v_x_243_, lean_object* v_y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_Time_instHAddOffsetOffset__10___lam__0(v_x_243_, v_y_244_);
lean_dec(v_y_244_);
lean_dec(v_x_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__11___lam__0(lean_object* v_x_248_, lean_object* v_y_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
v___x_251_ = lean_int_mul(v_y_249_, v___x_250_);
v___x_252_ = lean_int_add(v_x_248_, v___x_251_);
lean_dec(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__11___lam__0___boxed(lean_object* v_x_253_, lean_object* v_y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_Time_instHAddOffsetOffset__11___lam__0(v_x_253_, v_y_254_);
lean_dec(v_y_254_);
lean_dec(v_x_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__12___lam__0(lean_object* v_x_258_, lean_object* v_y_259_){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
v___x_261_ = lean_int_mul(v_x_258_, v___x_260_);
v___x_262_ = lean_int_add(v___x_261_, v_y_259_);
lean_dec(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__12___lam__0___boxed(lean_object* v_x_263_, lean_object* v_y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Time_instHAddOffsetOffset__12___lam__0(v_x_263_, v_y_264_);
lean_dec(v_y_264_);
lean_dec(v_x_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__13___lam__0(lean_object* v_x_268_, lean_object* v_y_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
v___x_271_ = lean_int_mul(v_x_268_, v___x_270_);
v___x_272_ = lean_int_add(v___x_271_, v_y_269_);
lean_dec(v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__13___lam__0___boxed(lean_object* v_x_273_, lean_object* v_y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_Time_instHAddOffsetOffset__13___lam__0(v_x_273_, v_y_274_);
lean_dec(v_y_274_);
lean_dec(v_x_273_);
return v_res_275_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(60u);
v___x_280_ = lean_nat_to_int(v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__14___lam__0(lean_object* v_x_281_, lean_object* v_y_282_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
v___x_284_ = lean_int_mul(v_y_282_, v___x_283_);
v___x_285_ = lean_int_add(v_x_281_, v___x_284_);
lean_dec(v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__14___lam__0___boxed(lean_object* v_x_286_, lean_object* v_y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Time_instHAddOffsetOffset__14___lam__0(v_x_286_, v_y_287_);
lean_dec(v_y_287_);
lean_dec(v_x_286_);
return v_res_288_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(3600u);
v___x_292_ = lean_nat_to_int(v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__15___lam__0(lean_object* v_x_293_, lean_object* v_y_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
v___x_296_ = lean_int_mul(v_y_294_, v___x_295_);
v___x_297_ = lean_int_add(v_x_293_, v___x_296_);
lean_dec(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__15___lam__0___boxed(lean_object* v_x_298_, lean_object* v_y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Std_Time_instHAddOffsetOffset__15___lam__0(v_x_298_, v_y_299_);
lean_dec(v_y_299_);
lean_dec(v_x_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__16___lam__0(lean_object* v_x_303_, lean_object* v_y_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
v___x_306_ = lean_int_mul(v_y_304_, v___x_305_);
v___x_307_ = lean_int_add(v_x_303_, v___x_306_);
lean_dec(v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__16___lam__0___boxed(lean_object* v_x_308_, lean_object* v_y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Time_instHAddOffsetOffset__16___lam__0(v_x_308_, v_y_309_);
lean_dec(v_y_309_);
lean_dec(v_x_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__17___lam__0(lean_object* v_x_313_, lean_object* v_y_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
v___x_316_ = lean_int_mul(v_y_314_, v___x_315_);
v___x_317_ = lean_int_add(v_x_313_, v___x_316_);
lean_dec(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__17___lam__0___boxed(lean_object* v_x_318_, lean_object* v_y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_Time_instHAddOffsetOffset__17___lam__0(v_x_318_, v_y_319_);
lean_dec(v_y_319_);
lean_dec(v_x_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__18___lam__0(lean_object* v_x_323_, lean_object* v_y_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
v___x_326_ = lean_int_mul(v_x_323_, v___x_325_);
v___x_327_ = lean_int_add(v___x_326_, v_y_324_);
lean_dec(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__18___lam__0___boxed(lean_object* v_x_328_, lean_object* v_y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_Time_instHAddOffsetOffset__18___lam__0(v_x_328_, v_y_329_);
lean_dec(v_y_329_);
lean_dec(v_x_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__19___lam__0(lean_object* v_x_333_, lean_object* v_y_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
v___x_336_ = lean_int_mul(v_x_333_, v___x_335_);
v___x_337_ = lean_int_add(v___x_336_, v_y_334_);
lean_dec(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__19___lam__0___boxed(lean_object* v_x_338_, lean_object* v_y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Std_Time_instHAddOffsetOffset__19___lam__0(v_x_338_, v_y_339_);
lean_dec(v_y_339_);
lean_dec(v_x_338_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__20___lam__0(lean_object* v_x_343_, lean_object* v_y_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
v___x_346_ = lean_int_mul(v_x_343_, v___x_345_);
v___x_347_ = lean_int_add(v___x_346_, v_y_344_);
lean_dec(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__20___lam__0___boxed(lean_object* v_x_348_, lean_object* v_y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Time_instHAddOffsetOffset__20___lam__0(v_x_348_, v_y_349_);
lean_dec(v_y_349_);
lean_dec(v_x_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__22___lam__0(lean_object* v_x_355_, lean_object* v_y_356_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
v___x_358_ = lean_int_mul(v_y_356_, v___x_357_);
v___x_359_ = lean_int_add(v_x_355_, v___x_358_);
lean_dec(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__22___lam__0___boxed(lean_object* v_x_360_, lean_object* v_y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Time_instHAddOffsetOffset__22___lam__0(v_x_360_, v_y_361_);
lean_dec(v_y_361_);
lean_dec(v_x_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__23___lam__0(lean_object* v_x_365_, lean_object* v_y_366_){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
v___x_368_ = lean_int_mul(v_y_366_, v___x_367_);
v___x_369_ = lean_int_add(v_x_365_, v___x_368_);
lean_dec(v___x_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__23___lam__0___boxed(lean_object* v_x_370_, lean_object* v_y_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_Time_instHAddOffsetOffset__23___lam__0(v_x_370_, v_y_371_);
lean_dec(v_y_371_);
lean_dec(v_x_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__24___lam__0(lean_object* v_x_375_, lean_object* v_y_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
v___x_378_ = lean_int_mul(v_x_375_, v___x_377_);
v___x_379_ = lean_int_add(v___x_378_, v_y_376_);
lean_dec(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__24___lam__0___boxed(lean_object* v_x_380_, lean_object* v_y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Time_instHAddOffsetOffset__24___lam__0(v_x_380_, v_y_381_);
lean_dec(v_y_381_);
lean_dec(v_x_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__25___lam__0(lean_object* v_x_385_, lean_object* v_y_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
v___x_388_ = lean_int_mul(v_x_385_, v___x_387_);
v___x_389_ = lean_int_add(v___x_388_, v_y_386_);
lean_dec(v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__25___lam__0___boxed(lean_object* v_x_390_, lean_object* v_y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_Time_instHAddOffsetOffset__25___lam__0(v_x_390_, v_y_391_);
lean_dec(v_y_391_);
lean_dec(v_x_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__26___lam__0(lean_object* v_x_395_, lean_object* v_y_396_){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
v___x_398_ = lean_int_mul(v_x_395_, v___x_397_);
v___x_399_ = lean_int_add(v___x_398_, v_y_396_);
lean_dec(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__26___lam__0___boxed(lean_object* v_x_400_, lean_object* v_y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Std_Time_instHAddOffsetOffset__26___lam__0(v_x_400_, v_y_401_);
lean_dec(v_y_401_);
lean_dec(v_x_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__28___lam__0(lean_object* v_x_407_, lean_object* v_y_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
v___x_410_ = lean_int_mul(v_y_408_, v___x_409_);
v___x_411_ = lean_int_add(v_x_407_, v___x_410_);
lean_dec(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__28___lam__0___boxed(lean_object* v_x_412_, lean_object* v_y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Time_instHAddOffsetOffset__28___lam__0(v_x_412_, v_y_413_);
lean_dec(v_y_413_);
lean_dec(v_x_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__29___lam__0(lean_object* v_x_417_, lean_object* v_y_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
v___x_420_ = lean_int_mul(v_y_418_, v___x_419_);
v___x_421_ = lean_int_add(v_x_417_, v___x_420_);
lean_dec(v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__29___lam__0___boxed(lean_object* v_x_422_, lean_object* v_y_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_Time_instHAddOffsetOffset__29___lam__0(v_x_422_, v_y_423_);
lean_dec(v_y_423_);
lean_dec(v_x_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__30___lam__0(lean_object* v_x_427_, lean_object* v_y_428_){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
v___x_430_ = lean_int_mul(v_x_427_, v___x_429_);
v___x_431_ = lean_int_add(v___x_430_, v_y_428_);
lean_dec(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__30___lam__0___boxed(lean_object* v_x_432_, lean_object* v_y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_Time_instHAddOffsetOffset__30___lam__0(v_x_432_, v_y_433_);
lean_dec(v_y_433_);
lean_dec(v_x_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__31___lam__0(lean_object* v_x_437_, lean_object* v_y_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
v___x_440_ = lean_int_mul(v_x_437_, v___x_439_);
v___x_441_ = lean_int_add(v___x_440_, v_y_438_);
lean_dec(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__31___lam__0___boxed(lean_object* v_x_442_, lean_object* v_y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_Time_instHAddOffsetOffset__31___lam__0(v_x_442_, v_y_443_);
lean_dec(v_y_443_);
lean_dec(v_x_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__32___lam__0(lean_object* v_x_447_, lean_object* v_y_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
v___x_450_ = lean_int_mul(v_x_447_, v___x_449_);
v___x_451_ = lean_int_add(v___x_450_, v_y_448_);
lean_dec(v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__32___lam__0___boxed(lean_object* v_x_452_, lean_object* v_y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Time_instHAddOffsetOffset__32___lam__0(v_x_452_, v_y_453_);
lean_dec(v_y_453_);
lean_dec(v_x_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__33___lam__0(lean_object* v_x_457_, lean_object* v_y_458_){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
v___x_460_ = lean_int_mul(v_x_457_, v___x_459_);
v___x_461_ = lean_int_add(v___x_460_, v_y_458_);
lean_dec(v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__33___lam__0___boxed(lean_object* v_x_462_, lean_object* v_y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_Time_instHAddOffsetOffset__33___lam__0(v_x_462_, v_y_463_);
lean_dec(v_y_463_);
lean_dec(v_x_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__34___lam__0(lean_object* v_x_467_, lean_object* v_y_468_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
v___x_470_ = lean_int_mul(v_x_467_, v___x_469_);
v___x_471_ = lean_int_add(v___x_470_, v_y_468_);
lean_dec(v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__34___lam__0___boxed(lean_object* v_x_472_, lean_object* v_y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_Time_instHAddOffsetOffset__34___lam__0(v_x_472_, v_y_473_);
lean_dec(v_y_473_);
lean_dec(v_x_472_);
return v_res_474_;
}
}
static lean_object* _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(7u);
v___x_479_ = lean_nat_to_int(v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__35___lam__0(lean_object* v_x_480_, lean_object* v_y_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
v___x_483_ = lean_int_mul(v_y_481_, v___x_482_);
v___x_484_ = lean_int_add(v_x_480_, v___x_483_);
lean_dec(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__35___lam__0___boxed(lean_object* v_x_485_, lean_object* v_y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_Time_instHAddOffsetOffset__35___lam__0(v_x_485_, v_y_486_);
lean_dec(v_y_486_);
lean_dec(v_x_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__36___lam__0(lean_object* v_x_490_, lean_object* v_y_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
v___x_493_ = lean_int_mul(v_x_490_, v___x_492_);
v___x_494_ = lean_int_add(v___x_493_, v_y_491_);
lean_dec(v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__36___lam__0___boxed(lean_object* v_x_495_, lean_object* v_y_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l_Std_Time_instHAddOffsetOffset__36___lam__0(v_x_495_, v_y_496_);
lean_dec(v_y_496_);
lean_dec(v_x_495_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__37___lam__0(lean_object* v_x_500_, lean_object* v_y_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
v___x_503_ = lean_int_mul(v_x_500_, v___x_502_);
v___x_504_ = lean_int_add(v___x_503_, v_y_501_);
lean_dec(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__37___lam__0___boxed(lean_object* v_x_505_, lean_object* v_y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_Time_instHAddOffsetOffset__37___lam__0(v_x_505_, v_y_506_);
lean_dec(v_y_506_);
lean_dec(v_x_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__38___lam__0(lean_object* v_x_510_, lean_object* v_y_511_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
v___x_513_ = lean_int_mul(v_x_510_, v___x_512_);
v___x_514_ = lean_int_add(v___x_513_, v_y_511_);
lean_dec(v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__38___lam__0___boxed(lean_object* v_x_515_, lean_object* v_y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_Time_instHAddOffsetOffset__38___lam__0(v_x_515_, v_y_516_);
lean_dec(v_y_516_);
lean_dec(v_x_515_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__39___lam__0(lean_object* v_x_520_, lean_object* v_y_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
v___x_523_ = lean_int_mul(v_x_520_, v___x_522_);
v___x_524_ = lean_int_add(v___x_523_, v_y_521_);
lean_dec(v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__39___lam__0___boxed(lean_object* v_x_525_, lean_object* v_y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_Time_instHAddOffsetOffset__39___lam__0(v_x_525_, v_y_526_);
lean_dec(v_y_526_);
lean_dec(v_x_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__40___lam__0(lean_object* v_x_530_, lean_object* v_y_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
v___x_533_ = lean_int_mul(v_x_530_, v___x_532_);
v___x_534_ = lean_int_add(v___x_533_, v_y_531_);
lean_dec(v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__40___lam__0___boxed(lean_object* v_x_535_, lean_object* v_y_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Time_instHAddOffsetOffset__40___lam__0(v_x_535_, v_y_536_);
lean_dec(v_y_536_);
lean_dec(v_x_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__41___lam__0(lean_object* v_x_540_, lean_object* v_y_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
v___x_543_ = lean_int_mul(v_x_540_, v___x_542_);
v___x_544_ = lean_int_add(v___x_543_, v_y_541_);
lean_dec(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHAddOffsetOffset__41___lam__0___boxed(lean_object* v_x_545_, lean_object* v_y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_Time_instHAddOffsetOffset__41___lam__0(v_x_545_, v_y_546_);
lean_dec(v_y_546_);
lean_dec(v_x_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset___lam__0(lean_object* v_x_553_, lean_object* v_y_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
v___x_556_ = lean_int_mul(v_y_554_, v___x_555_);
v___x_557_ = lean_int_sub(v_x_553_, v___x_556_);
lean_dec(v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset___lam__0___boxed(lean_object* v_x_558_, lean_object* v_y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Std_Time_instHSubOffsetOffset___lam__0(v_x_558_, v_y_559_);
lean_dec(v_y_559_);
lean_dec(v_x_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__1___lam__0(lean_object* v_x_563_, lean_object* v_y_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
v___x_566_ = lean_int_mul(v_y_564_, v___x_565_);
v___x_567_ = lean_int_sub(v_x_563_, v___x_566_);
lean_dec(v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__1___lam__0___boxed(lean_object* v_x_568_, lean_object* v_y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_Time_instHSubOffsetOffset__1___lam__0(v_x_568_, v_y_569_);
lean_dec(v_y_569_);
lean_dec(v_x_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__2___lam__0(lean_object* v_x_573_, lean_object* v_y_574_){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
v___x_576_ = lean_int_mul(v_y_574_, v___x_575_);
v___x_577_ = lean_int_sub(v_x_573_, v___x_576_);
lean_dec(v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__2___lam__0___boxed(lean_object* v_x_578_, lean_object* v_y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_Time_instHSubOffsetOffset__2___lam__0(v_x_578_, v_y_579_);
lean_dec(v_y_579_);
lean_dec(v_x_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__3___lam__0(lean_object* v_x_583_, lean_object* v_y_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
v___x_586_ = lean_int_mul(v_y_584_, v___x_585_);
v___x_587_ = lean_int_sub(v_x_583_, v___x_586_);
lean_dec(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__3___lam__0___boxed(lean_object* v_x_588_, lean_object* v_y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_Time_instHSubOffsetOffset__3___lam__0(v_x_588_, v_y_589_);
lean_dec(v_y_589_);
lean_dec(v_x_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__4___lam__0(lean_object* v_x_593_, lean_object* v_y_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
v___x_596_ = lean_int_mul(v_y_594_, v___x_595_);
v___x_597_ = lean_int_sub(v_x_593_, v___x_596_);
lean_dec(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__4___lam__0___boxed(lean_object* v_x_598_, lean_object* v_y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Std_Time_instHSubOffsetOffset__4___lam__0(v_x_598_, v_y_599_);
lean_dec(v_y_599_);
lean_dec(v_x_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__5___lam__0(lean_object* v_x_603_, lean_object* v_y_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
v___x_606_ = lean_int_mul(v_y_604_, v___x_605_);
v___x_607_ = lean_int_sub(v_x_603_, v___x_606_);
lean_dec(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__5___lam__0___boxed(lean_object* v_x_608_, lean_object* v_y_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_Time_instHSubOffsetOffset__5___lam__0(v_x_608_, v_y_609_);
lean_dec(v_y_609_);
lean_dec(v_x_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__6___lam__0(lean_object* v_x_613_, lean_object* v_y_614_){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset___lam__0___closed__0);
v___x_616_ = lean_int_mul(v_x_613_, v___x_615_);
v___x_617_ = lean_int_sub(v___x_616_, v_y_614_);
lean_dec(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__6___lam__0___boxed(lean_object* v_x_618_, lean_object* v_y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_Time_instHSubOffsetOffset__6___lam__0(v_x_618_, v_y_619_);
lean_dec(v_y_619_);
lean_dec(v_x_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__7___lam__0(lean_object* v_x_624_, lean_object* v_y_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
v___x_627_ = lean_int_mul(v_y_625_, v___x_626_);
v___x_628_ = lean_int_sub(v_x_624_, v___x_627_);
lean_dec(v___x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__7___lam__0___boxed(lean_object* v_x_629_, lean_object* v_y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_Time_instHSubOffsetOffset__7___lam__0(v_x_629_, v_y_630_);
lean_dec(v_y_630_);
lean_dec(v_x_629_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__8___lam__0(lean_object* v_x_634_, lean_object* v_y_635_){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
v___x_637_ = lean_int_mul(v_y_635_, v___x_636_);
v___x_638_ = lean_int_sub(v_x_634_, v___x_637_);
lean_dec(v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__8___lam__0___boxed(lean_object* v_x_639_, lean_object* v_y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Std_Time_instHSubOffsetOffset__8___lam__0(v_x_639_, v_y_640_);
lean_dec(v_y_640_);
lean_dec(v_x_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__9___lam__0(lean_object* v_x_644_, lean_object* v_y_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
v___x_647_ = lean_int_mul(v_y_645_, v___x_646_);
v___x_648_ = lean_int_sub(v_x_644_, v___x_647_);
lean_dec(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__9___lam__0___boxed(lean_object* v_x_649_, lean_object* v_y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Time_instHSubOffsetOffset__9___lam__0(v_x_649_, v_y_650_);
lean_dec(v_y_650_);
lean_dec(v_x_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__10___lam__0(lean_object* v_x_654_, lean_object* v_y_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
v___x_657_ = lean_int_mul(v_y_655_, v___x_656_);
v___x_658_ = lean_int_sub(v_x_654_, v___x_657_);
lean_dec(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__10___lam__0___boxed(lean_object* v_x_659_, lean_object* v_y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_Time_instHSubOffsetOffset__10___lam__0(v_x_659_, v_y_660_);
lean_dec(v_y_660_);
lean_dec(v_x_659_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__11___lam__0(lean_object* v_x_664_, lean_object* v_y_665_){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
v___x_667_ = lean_int_mul(v_y_665_, v___x_666_);
v___x_668_ = lean_int_sub(v_x_664_, v___x_667_);
lean_dec(v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__11___lam__0___boxed(lean_object* v_x_669_, lean_object* v_y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Std_Time_instHSubOffsetOffset__11___lam__0(v_x_669_, v_y_670_);
lean_dec(v_y_670_);
lean_dec(v_x_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__12___lam__0(lean_object* v_x_674_, lean_object* v_y_675_){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_676_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__1___lam__0___closed__0);
v___x_677_ = lean_int_mul(v_x_674_, v___x_676_);
v___x_678_ = lean_int_sub(v___x_677_, v_y_675_);
lean_dec(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__12___lam__0___boxed(lean_object* v_x_679_, lean_object* v_y_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_Time_instHSubOffsetOffset__12___lam__0(v_x_679_, v_y_680_);
lean_dec(v_y_680_);
lean_dec(v_x_679_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__13___lam__0(lean_object* v_x_684_, lean_object* v_y_685_){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__7___lam__0___closed__0);
v___x_687_ = lean_int_mul(v_x_684_, v___x_686_);
v___x_688_ = lean_int_sub(v___x_687_, v_y_685_);
lean_dec(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__13___lam__0___boxed(lean_object* v_x_689_, lean_object* v_y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Std_Time_instHSubOffsetOffset__13___lam__0(v_x_689_, v_y_690_);
lean_dec(v_y_690_);
lean_dec(v_x_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__14___lam__0(lean_object* v_x_695_, lean_object* v_y_696_){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
v___x_698_ = lean_int_mul(v_y_696_, v___x_697_);
v___x_699_ = lean_int_sub(v_x_695_, v___x_698_);
lean_dec(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__14___lam__0___boxed(lean_object* v_x_700_, lean_object* v_y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Std_Time_instHSubOffsetOffset__14___lam__0(v_x_700_, v_y_701_);
lean_dec(v_y_701_);
lean_dec(v_x_700_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__15___lam__0(lean_object* v_x_705_, lean_object* v_y_706_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
v___x_708_ = lean_int_mul(v_y_706_, v___x_707_);
v___x_709_ = lean_int_sub(v_x_705_, v___x_708_);
lean_dec(v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__15___lam__0___boxed(lean_object* v_x_710_, lean_object* v_y_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_Time_instHSubOffsetOffset__15___lam__0(v_x_710_, v_y_711_);
lean_dec(v_y_711_);
lean_dec(v_x_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__16___lam__0(lean_object* v_x_715_, lean_object* v_y_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
v___x_718_ = lean_int_mul(v_y_716_, v___x_717_);
v___x_719_ = lean_int_sub(v_x_715_, v___x_718_);
lean_dec(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__16___lam__0___boxed(lean_object* v_x_720_, lean_object* v_y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_Time_instHSubOffsetOffset__16___lam__0(v_x_720_, v_y_721_);
lean_dec(v_y_721_);
lean_dec(v_x_720_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__17___lam__0(lean_object* v_x_725_, lean_object* v_y_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
v___x_728_ = lean_int_mul(v_y_726_, v___x_727_);
v___x_729_ = lean_int_sub(v_x_725_, v___x_728_);
lean_dec(v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__17___lam__0___boxed(lean_object* v_x_730_, lean_object* v_y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Std_Time_instHSubOffsetOffset__17___lam__0(v_x_730_, v_y_731_);
lean_dec(v_y_731_);
lean_dec(v_x_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__18___lam__0(lean_object* v_x_735_, lean_object* v_y_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__2___lam__0___closed__0);
v___x_738_ = lean_int_mul(v_x_735_, v___x_737_);
v___x_739_ = lean_int_sub(v___x_738_, v_y_736_);
lean_dec(v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__18___lam__0___boxed(lean_object* v_x_740_, lean_object* v_y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_Time_instHSubOffsetOffset__18___lam__0(v_x_740_, v_y_741_);
lean_dec(v_y_741_);
lean_dec(v_x_740_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__19___lam__0(lean_object* v_x_745_, lean_object* v_y_746_){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__8___lam__0___closed__0);
v___x_748_ = lean_int_mul(v_x_745_, v___x_747_);
v___x_749_ = lean_int_sub(v___x_748_, v_y_746_);
lean_dec(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__19___lam__0___boxed(lean_object* v_x_750_, lean_object* v_y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Std_Time_instHSubOffsetOffset__19___lam__0(v_x_750_, v_y_751_);
lean_dec(v_y_751_);
lean_dec(v_x_750_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__20___lam__0(lean_object* v_x_755_, lean_object* v_y_756_){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_757_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__14___lam__0___closed__0);
v___x_758_ = lean_int_mul(v_x_755_, v___x_757_);
v___x_759_ = lean_int_sub(v___x_758_, v_y_756_);
lean_dec(v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__20___lam__0___boxed(lean_object* v_x_760_, lean_object* v_y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_Time_instHSubOffsetOffset__20___lam__0(v_x_760_, v_y_761_);
lean_dec(v_y_761_);
lean_dec(v_x_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__22___lam__0(lean_object* v_x_767_, lean_object* v_y_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
v___x_770_ = lean_int_mul(v_y_768_, v___x_769_);
v___x_771_ = lean_int_sub(v_x_767_, v___x_770_);
lean_dec(v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__22___lam__0___boxed(lean_object* v_x_772_, lean_object* v_y_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Std_Time_instHSubOffsetOffset__22___lam__0(v_x_772_, v_y_773_);
lean_dec(v_y_773_);
lean_dec(v_x_772_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__23___lam__0(lean_object* v_x_777_, lean_object* v_y_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_779_ = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
v___x_780_ = lean_int_mul(v_y_778_, v___x_779_);
v___x_781_ = lean_int_sub(v_x_777_, v___x_780_);
lean_dec(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__23___lam__0___boxed(lean_object* v_x_782_, lean_object* v_y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_Time_instHSubOffsetOffset__23___lam__0(v_x_782_, v_y_783_);
lean_dec(v_y_783_);
lean_dec(v_x_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__24___lam__0(lean_object* v_x_787_, lean_object* v_y_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_789_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__3___lam__0___closed__0);
v___x_790_ = lean_int_mul(v_x_787_, v___x_789_);
v___x_791_ = lean_int_sub(v___x_790_, v_y_788_);
lean_dec(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__24___lam__0___boxed(lean_object* v_x_792_, lean_object* v_y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_Time_instHSubOffsetOffset__24___lam__0(v_x_792_, v_y_793_);
lean_dec(v_y_793_);
lean_dec(v_x_792_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__25___lam__0(lean_object* v_x_797_, lean_object* v_y_798_){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__9___lam__0___closed__0);
v___x_800_ = lean_int_mul(v_x_797_, v___x_799_);
v___x_801_ = lean_int_sub(v___x_800_, v_y_798_);
lean_dec(v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__25___lam__0___boxed(lean_object* v_x_802_, lean_object* v_y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_Time_instHSubOffsetOffset__25___lam__0(v_x_802_, v_y_803_);
lean_dec(v_y_803_);
lean_dec(v_x_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__26___lam__0(lean_object* v_x_807_, lean_object* v_y_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__15___lam__0___closed__0);
v___x_810_ = lean_int_mul(v_x_807_, v___x_809_);
v___x_811_ = lean_int_sub(v___x_810_, v_y_808_);
lean_dec(v___x_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__26___lam__0___boxed(lean_object* v_x_812_, lean_object* v_y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_Time_instHSubOffsetOffset__26___lam__0(v_x_812_, v_y_813_);
lean_dec(v_y_813_);
lean_dec(v_x_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__28___lam__0(lean_object* v_x_819_, lean_object* v_y_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_821_ = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
v___x_822_ = lean_int_mul(v_y_820_, v___x_821_);
v___x_823_ = lean_int_sub(v_x_819_, v___x_822_);
lean_dec(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__28___lam__0___boxed(lean_object* v_x_824_, lean_object* v_y_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_Time_instHSubOffsetOffset__28___lam__0(v_x_824_, v_y_825_);
lean_dec(v_y_825_);
lean_dec(v_x_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__29___lam__0(lean_object* v_x_829_, lean_object* v_y_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
v___x_832_ = lean_int_mul(v_y_830_, v___x_831_);
v___x_833_ = lean_int_sub(v_x_829_, v___x_832_);
lean_dec(v___x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__29___lam__0___boxed(lean_object* v_x_834_, lean_object* v_y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Std_Time_instHSubOffsetOffset__29___lam__0(v_x_834_, v_y_835_);
lean_dec(v_y_835_);
lean_dec(v_x_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__30___lam__0(lean_object* v_x_839_, lean_object* v_y_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toDays___closed__0, &l_Std_Time_Nanosecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toDays___closed__0);
v___x_842_ = lean_int_mul(v_x_839_, v___x_841_);
v___x_843_ = lean_int_sub(v___x_842_, v_y_840_);
lean_dec(v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__30___lam__0___boxed(lean_object* v_x_844_, lean_object* v_y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_Time_instHSubOffsetOffset__30___lam__0(v_x_844_, v_y_845_);
lean_dec(v_y_845_);
lean_dec(v_x_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__31___lam__0(lean_object* v_x_849_, lean_object* v_y_850_){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toDays___closed__0, &l_Std_Time_Millisecond_Offset_toDays___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toDays___closed__0);
v___x_852_ = lean_int_mul(v_x_849_, v___x_851_);
v___x_853_ = lean_int_sub(v___x_852_, v_y_850_);
lean_dec(v___x_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__31___lam__0___boxed(lean_object* v_x_854_, lean_object* v_y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Std_Time_instHSubOffsetOffset__31___lam__0(v_x_854_, v_y_855_);
lean_dec(v_y_855_);
lean_dec(v_x_854_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__32___lam__0(lean_object* v_x_859_, lean_object* v_y_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = lean_obj_once(&l_Std_Time_Second_Offset_toDays___closed__0, &l_Std_Time_Second_Offset_toDays___closed__0_once, _init_l_Std_Time_Second_Offset_toDays___closed__0);
v___x_862_ = lean_int_mul(v_x_859_, v___x_861_);
v___x_863_ = lean_int_sub(v___x_862_, v_y_860_);
lean_dec(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__32___lam__0___boxed(lean_object* v_x_864_, lean_object* v_y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_Time_instHSubOffsetOffset__32___lam__0(v_x_864_, v_y_865_);
lean_dec(v_y_865_);
lean_dec(v_x_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__33___lam__0(lean_object* v_x_869_, lean_object* v_y_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = lean_obj_once(&l_Std_Time_Minute_Offset_toDays___closed__0, &l_Std_Time_Minute_Offset_toDays___closed__0_once, _init_l_Std_Time_Minute_Offset_toDays___closed__0);
v___x_872_ = lean_int_mul(v_x_869_, v___x_871_);
v___x_873_ = lean_int_sub(v___x_872_, v_y_870_);
lean_dec(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__33___lam__0___boxed(lean_object* v_x_874_, lean_object* v_y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_Time_instHSubOffsetOffset__33___lam__0(v_x_874_, v_y_875_);
lean_dec(v_y_875_);
lean_dec(v_x_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__34___lam__0(lean_object* v_x_879_, lean_object* v_y_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_obj_once(&l_Std_Time_Hour_Offset_toDays___closed__0, &l_Std_Time_Hour_Offset_toDays___closed__0_once, _init_l_Std_Time_Hour_Offset_toDays___closed__0);
v___x_882_ = lean_int_mul(v_x_879_, v___x_881_);
v___x_883_ = lean_int_sub(v___x_882_, v_y_880_);
lean_dec(v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__34___lam__0___boxed(lean_object* v_x_884_, lean_object* v_y_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_Time_instHSubOffsetOffset__34___lam__0(v_x_884_, v_y_885_);
lean_dec(v_y_885_);
lean_dec(v_x_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__35___lam__0(lean_object* v_x_890_, lean_object* v_y_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
v___x_893_ = lean_int_mul(v_y_891_, v___x_892_);
v___x_894_ = lean_int_sub(v_x_890_, v___x_893_);
lean_dec(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__35___lam__0___boxed(lean_object* v_x_895_, lean_object* v_y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Std_Time_instHSubOffsetOffset__35___lam__0(v_x_895_, v_y_896_);
lean_dec(v_y_896_);
lean_dec(v_x_895_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__36___lam__0(lean_object* v_x_900_, lean_object* v_y_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_obj_once(&l_Std_Time_Nanosecond_Offset_toWeeks___closed__0, &l_Std_Time_Nanosecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Nanosecond_Offset_toWeeks___closed__0);
v___x_903_ = lean_int_mul(v_x_900_, v___x_902_);
v___x_904_ = lean_int_sub(v___x_903_, v_y_901_);
lean_dec(v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__36___lam__0___boxed(lean_object* v_x_905_, lean_object* v_y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_Time_instHSubOffsetOffset__36___lam__0(v_x_905_, v_y_906_);
lean_dec(v_y_906_);
lean_dec(v_x_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__37___lam__0(lean_object* v_x_910_, lean_object* v_y_911_){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = lean_obj_once(&l_Std_Time_Millisecond_Offset_toWeeks___closed__0, &l_Std_Time_Millisecond_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Millisecond_Offset_toWeeks___closed__0);
v___x_913_ = lean_int_mul(v_x_910_, v___x_912_);
v___x_914_ = lean_int_sub(v___x_913_, v_y_911_);
lean_dec(v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__37___lam__0___boxed(lean_object* v_x_915_, lean_object* v_y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Std_Time_instHSubOffsetOffset__37___lam__0(v_x_915_, v_y_916_);
lean_dec(v_y_916_);
lean_dec(v_x_915_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__38___lam__0(lean_object* v_x_920_, lean_object* v_y_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_obj_once(&l_Std_Time_Second_Offset_toWeeks___closed__0, &l_Std_Time_Second_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Second_Offset_toWeeks___closed__0);
v___x_923_ = lean_int_mul(v_x_920_, v___x_922_);
v___x_924_ = lean_int_sub(v___x_923_, v_y_921_);
lean_dec(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__38___lam__0___boxed(lean_object* v_x_925_, lean_object* v_y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Std_Time_instHSubOffsetOffset__38___lam__0(v_x_925_, v_y_926_);
lean_dec(v_y_926_);
lean_dec(v_x_925_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__39___lam__0(lean_object* v_x_930_, lean_object* v_y_931_){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_obj_once(&l_Std_Time_Minute_Offset_toWeeks___closed__0, &l_Std_Time_Minute_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Minute_Offset_toWeeks___closed__0);
v___x_933_ = lean_int_mul(v_x_930_, v___x_932_);
v___x_934_ = lean_int_sub(v___x_933_, v_y_931_);
lean_dec(v___x_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__39___lam__0___boxed(lean_object* v_x_935_, lean_object* v_y_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_Time_instHSubOffsetOffset__39___lam__0(v_x_935_, v_y_936_);
lean_dec(v_y_936_);
lean_dec(v_x_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__40___lam__0(lean_object* v_x_940_, lean_object* v_y_941_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = lean_obj_once(&l_Std_Time_Hour_Offset_toWeeks___closed__0, &l_Std_Time_Hour_Offset_toWeeks___closed__0_once, _init_l_Std_Time_Hour_Offset_toWeeks___closed__0);
v___x_943_ = lean_int_mul(v_x_940_, v___x_942_);
v___x_944_ = lean_int_sub(v___x_943_, v_y_941_);
lean_dec(v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__40___lam__0___boxed(lean_object* v_x_945_, lean_object* v_y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Std_Time_instHSubOffsetOffset__40___lam__0(v_x_945_, v_y_946_);
lean_dec(v_y_946_);
lean_dec(v_x_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__41___lam__0(lean_object* v_x_950_, lean_object* v_y_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_952_ = lean_obj_once(&l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0, &l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0_once, _init_l_Std_Time_instHAddOffsetOffset__35___lam__0___closed__0);
v___x_953_ = lean_int_mul(v_x_950_, v___x_952_);
v___x_954_ = lean_int_sub(v___x_953_, v_y_951_);
lean_dec(v___x_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instHSubOffsetOffset__41___lam__0___boxed(lean_object* v_x_955_, lean_object* v_y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Std_Time_instHSubOffsetOffset__41___lam__0(v_x_955_, v_y_956_);
lean_dec(v_y_956_);
lean_dec(v_x_955_);
return v_res_957_;
}
}
lean_object* runtime_initialize_Std_Time_Date_Unit_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Date_ValidDate(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Date_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

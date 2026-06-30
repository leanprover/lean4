// Lean compiler output
// Module: Std.Time.DateTime.WallTime
// Imports: public import Init.System.IO public import Std.Time.Duration
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
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Int_repr(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_instToStringDuration_leftPad(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* l_Std_Time_Nanosecond_instReprOrdinal___lam__0(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
uint8_t l_Std_Time_Duration_instDecidableLe(lean_object*, lean_object*);
uint8_t l_Std_Time_instDecidableEqDuration_decEq(lean_object*, lean_object*);
extern lean_object* l_Std_Time_instOrdDuration;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Time_Duration_instDecidableLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprWallTime_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_instReprWallTime_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_instReprWallTime_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprWallTime_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprWallTime_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_instReprWallTime_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprWallTime_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_instReprWallTime_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_instReprWallTime_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_instReprWallTime_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__8_value;
static const lean_string_object l_Std_Time_instReprWallTime_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__9_value;
static lean_once_cell_t l_Std_Time_instReprWallTime_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__10;
static lean_once_cell_t l_Std_Time_instReprWallTime_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__11;
static const lean_ctor_object l_Std_Time_instReprWallTime_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Time_instReprWallTime_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__9_value)}};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__13_value;
static lean_once_cell_t l_Std_Time_instReprWallTime_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__14;
static const lean_string_object l_Std_Time_instReprWallTime_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__15 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__15_value;
static const lean_string_object l_Std_Time_instReprWallTime_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__16_value;
static const lean_string_object l_Std_Time_instReprWallTime_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Time_instReprWallTime_repr___redArg___closed__17 = (const lean_object*)&l_Std_Time_instReprWallTime_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprWallTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprWallTime_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprWallTime___closed__0 = (const lean_object*)&l_Std_Time_instReprWallTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprWallTime = (const lean_object*)&l_Std_Time_instReprWallTime___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqWallTime_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqWallTime_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqWallTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqWallTime___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedWallTime_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedWallTime_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedWallTime_default;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedWallTime_default_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedWallTime;
LEAN_EXPORT lean_object* l_Std_Time_instLEWallTime;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLeWallTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeWallTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instLTWallTime;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLtWallTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtWallTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdWallTime___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdWallTime___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_instOrdWallTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdWallTime___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdWallTime___closed__0 = (const lean_object*)&l_Std_Time_instOrdWallTime___closed__0_value;
static lean_once_cell_t l_Std_Time_instOrdWallTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdWallTime___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_instOrdWallTime;
LEAN_EXPORT lean_object* l_Std_Time_instToStringWallTime___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instToStringWallTime___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_instToStringWallTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instToStringWallTime___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instToStringWallTime___closed__0 = (const lean_object*)&l_Std_Time_instToStringWallTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instToStringWallTime = (const lean_object*)&l_Std_Time_instToStringWallTime___closed__0_value;
static const lean_string_object l_Std_Time_instReprWallTime__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "WallTime.ofNanoseconds "};
static const lean_object* l_Std_Time_instReprWallTime__1___lam__0___closed__0 = (const lean_object*)&l_Std_Time_instReprWallTime__1___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprWallTime__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprWallTime__1___lam__0___closed__0_value)}};
static const lean_object* l_Std_Time_instReprWallTime__1___lam__0___closed__1 = (const lean_object*)&l_Std_Time_instReprWallTime__1___lam__0___closed__1_value;
static lean_once_cell_t l_Std_Time_instReprWallTime__1___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprWallTime__1___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprWallTime__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprWallTime__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprWallTime__1___closed__0 = (const lean_object*)&l_Std_Time_instReprWallTime__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprWallTime__1 = (const lean_object*)&l_Std_Time_instReprWallTime__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofDuration(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofDuration___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofNanoseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toNanoseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toNanoseconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_WallTime_toMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_WallTime_toMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMinutes___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_WallTime_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_WallTime_toDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDays___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_WallTime_ofMilliseconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_WallTime_ofMilliseconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMilliseconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMilliseconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addSeconds___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_WallTime_subSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_WallTime_subSeconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMinutes___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_WallTime_addHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_WallTime_addHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDuration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDuration___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDuration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDuration___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDuration(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDuration___boxed(lean_object*);
static const lean_closure_object l_Std_Time_WallTime_instHAddDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_addDuration___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHAddDuration___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHAddDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHAddDuration = (const lean_object*)&l_Std_Time_WallTime_instHAddDuration___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_subDuration___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHSubDuration = (const lean_object*)&l_Std_Time_WallTime_instHSubDuration___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_addDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHAddOffset___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHAddOffset = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_subDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHSubOffset___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHSubOffset = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHAddOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_addWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHAddOffset__1___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHAddOffset__1 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHSubOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_subWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHSubOffset__1___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHSubOffset__1 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHAddOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_addHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHAddOffset__2___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHAddOffset__2 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHSubOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_subHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHSubOffset__2___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHSubOffset__2 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHAddOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_addMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHAddOffset__3___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHAddOffset__3 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHSubOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_subMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHSubOffset__3___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHSubOffset__3 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHAddOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_addSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHAddOffset__4___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHAddOffset__4 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHSubOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_subSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHSubOffset__4___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHSubOffset__4 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHAddOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_addMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHAddOffset__5___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHAddOffset__5 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHSubOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_subMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHSubOffset__5___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHSubOffset__5 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHAddOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_addNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHAddOffset__6___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHAddOffset__6 = (const lean_object*)&l_Std_Time_WallTime_instHAddOffset__6___closed__0_value;
static const lean_closure_object l_Std_Time_WallTime_instHSubOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_subNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHSubOffset__6___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHSubOffset__6 = (const lean_object*)&l_Std_Time_WallTime_instHSubOffset__6___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_WallTime_instHSubDuration__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_instHSubDuration__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_WallTime_instHSubDuration__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_WallTime_instHSubDuration__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_WallTime_instHSubDuration__1___closed__0 = (const lean_object*)&l_Std_Time_WallTime_instHSubDuration__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_WallTime_instHSubDuration__1 = (const lean_object*)&l_Std_Time_WallTime_instHSubDuration__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_WallTime_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprWallTime_repr_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(7u);
v___x_17_ = lean_nat_to_int(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_Time_instReprWallTime_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__0));
v___x_21_ = lean_string_length(v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_l_Std_Time_instReprWallTime_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__10, &l_Std_Time_instReprWallTime_repr___redArg___closed__10_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__10);
v___x_23_ = lean_nat_to_int(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_to_int(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime_repr___redArg(lean_object* v_x_33_){
_start:
{
lean_object* v_second_34_; lean_object* v_nano_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_88_; 
v_second_34_ = lean_ctor_get(v_x_33_, 0);
v_nano_35_ = lean_ctor_get(v_x_33_, 1);
v_isSharedCheck_88_ = !lean_is_exclusive(v_x_33_);
if (v_isSharedCheck_88_ == 0)
{
v___x_37_ = v_x_33_;
v_isShared_38_ = v_isSharedCheck_88_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_nano_35_);
lean_inc(v_second_34_);
lean_dec(v_x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_88_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___y_42_; lean_object* v___y_43_; lean_object* v_fst_63_; lean_object* v_fst_64_; lean_object* v_snd_65_; lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_39_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__6));
v___x_40_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__7, &l_Std_Time_instReprWallTime_repr___redArg___closed__7_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7);
v___x_76_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_77_ = lean_int_dec_lt(v___x_76_, v_second_34_);
if (v___x_77_ == 0)
{
uint8_t v___x_78_; 
v___x_78_ = lean_int_dec_lt(v_second_34_, v___x_76_);
if (v___x_78_ == 0)
{
uint8_t v___x_79_; 
v___x_79_ = lean_int_dec_lt(v_nano_35_, v___x_76_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; 
v___x_80_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__16));
lean_inc(v_nano_35_);
v_fst_63_ = v___x_80_;
v_fst_64_ = v_second_34_;
v_snd_65_ = v_nano_35_;
goto v___jp_62_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__17));
v___x_82_ = lean_int_neg(v_second_34_);
lean_dec(v_second_34_);
v___x_83_ = lean_int_neg(v_nano_35_);
v_fst_63_ = v___x_81_;
v_fst_64_ = v___x_82_;
v_snd_65_ = v___x_83_;
goto v___jp_62_;
}
}
else
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__17));
v___x_85_ = lean_int_neg(v_second_34_);
lean_dec(v_second_34_);
v___x_86_ = lean_int_neg(v_nano_35_);
v_fst_63_ = v___x_84_;
v_fst_64_ = v___x_85_;
v_snd_65_ = v___x_86_;
goto v___jp_62_;
}
}
else
{
lean_object* v___x_87_; 
v___x_87_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__16));
lean_inc(v_nano_35_);
v_fst_63_ = v___x_87_;
v_fst_64_ = v_second_34_;
v_snd_65_ = v_nano_35_;
goto v___jp_62_;
}
v___jp_41_:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_44_ = lean_string_append(v___y_42_, v___y_43_);
lean_dec_ref(v___y_43_);
v___x_45_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__8));
v___x_46_ = lean_string_append(v___x_44_, v___x_45_);
v___x_47_ = l_String_quote(v___x_46_);
v___x_48_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 4);
lean_ctor_set(v___x_37_, 1, v___x_48_);
lean_ctor_set(v___x_37_, 0, v___x_40_);
v___x_50_ = v___x_37_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v___x_48_);
v___x_50_ = v_reuseFailAlloc_61_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
uint8_t v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_51_ = 0;
v___x_52_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_52_, 0, v___x_50_);
lean_ctor_set_uint8(v___x_52_, sizeof(void*)*1, v___x_51_);
v___x_53_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_39_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__11, &l_Std_Time_instReprWallTime_repr___redArg___closed__11_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__11);
v___x_55_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__12));
v___x_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_53_);
v___x_57_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__13));
v___x_58_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_54_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set_uint8(v___x_60_, sizeof(void*)*1, v___x_51_);
return v___x_60_;
}
}
v___jp_62_:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_66_ = l_Int_repr(v_fst_64_);
lean_dec(v_fst_64_);
lean_inc_ref(v_fst_63_);
v___x_67_ = lean_string_append(v_fst_63_, v___x_66_);
lean_dec_ref(v___x_66_);
v___x_68_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_69_ = lean_int_dec_eq(v_nano_35_, v___x_68_);
lean_dec(v_nano_35_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_70_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__15));
v___x_71_ = lean_unsigned_to_nat(9u);
v___x_72_ = l_Int_repr(v_snd_65_);
lean_dec(v_snd_65_);
v___x_73_ = l_Std_Time_instToStringDuration_leftPad(v___x_71_, v___x_72_);
lean_dec_ref(v___x_72_);
v___x_74_ = lean_string_append(v___x_70_, v___x_73_);
lean_dec_ref(v___x_73_);
v___y_42_ = v___x_67_;
v___y_43_ = v___x_74_;
goto v___jp_41_;
}
else
{
lean_object* v___x_75_; 
lean_dec(v_snd_65_);
v___x_75_ = ((lean_object*)(l_Std_Time_instReprWallTime_repr___redArg___closed__16));
v___y_42_ = v___x_67_;
v___y_43_ = v___x_75_;
goto v___jp_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime_repr(lean_object* v_x_89_, lean_object* v_prec_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Std_Time_instReprWallTime_repr___redArg(v_x_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime_repr___boxed(lean_object* v_x_92_, lean_object* v_prec_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Time_instReprWallTime_repr(v_x_92_, v_prec_93_);
lean_dec(v_prec_93_);
return v_res_94_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqWallTime_decEq(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_97_, v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqWallTime_decEq___boxed(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Std_Time_instDecidableEqWallTime_decEq(v_x_100_, v_x_101_);
lean_dec_ref(v_x_101_);
lean_dec_ref(v_x_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqWallTime(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_104_, v_x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqWallTime___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_Time_instDecidableEqWallTime(v_x_107_, v_x_108_);
lean_dec_ref(v_x_108_);
lean_dec_ref(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedWallTime_default___closed__0(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedWallTime_default(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Std_Time_instInhabitedWallTime_default___closed__0, &l_Std_Time_instInhabitedWallTime_default___closed__0_once, _init_l_Std_Time_instInhabitedWallTime_default___closed__0);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedWallTime_default_spec__0(lean_object* v_a_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_nat_to_int(v_a_114_);
v___x_116_ = l_Rat_ofInt(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedWallTime(void){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_Time_instInhabitedWallTime_default;
return v___x_117_;
}
}
static lean_object* _init_l_Std_Time_instLEWallTime(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLeWallTime(lean_object* v_x_119_, lean_object* v_y_120_){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = l_Std_Time_Duration_instDecidableLe(v_x_119_, v_y_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeWallTime___boxed(lean_object* v_x_122_, lean_object* v_y_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Std_Time_instDecidableLeWallTime(v_x_122_, v_y_123_);
lean_dec_ref(v_y_123_);
lean_dec_ref(v_x_122_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
static lean_object* _init_l_Std_Time_instLTWallTime(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLtWallTime(lean_object* v_x_127_, lean_object* v_y_128_){
_start:
{
uint8_t v___x_129_; 
v___x_129_ = l_Std_Time_Duration_instDecidableLt(v_x_127_, v_y_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtWallTime___boxed(lean_object* v_x_130_, lean_object* v_y_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Std_Time_instDecidableLtWallTime(v_x_130_, v_y_131_);
lean_dec_ref(v_y_131_);
lean_dec_ref(v_x_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdWallTime___lam__0(lean_object* v_x_134_){
_start:
{
lean_inc_ref(v_x_134_);
return v_x_134_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdWallTime___lam__0___boxed(lean_object* v_x_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_Time_instOrdWallTime___lam__0(v_x_135_);
lean_dec_ref(v_x_135_);
return v_res_136_;
}
}
static lean_object* _init_l_Std_Time_instOrdWallTime___closed__1(void){
_start:
{
lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___f_138_ = ((lean_object*)(l_Std_Time_instOrdWallTime___closed__0));
v___x_139_ = l_Std_Time_instOrdDuration;
v___x_140_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_140_, 0, lean_box(0));
lean_closure_set(v___x_140_, 1, lean_box(0));
lean_closure_set(v___x_140_, 2, v___x_139_);
lean_closure_set(v___x_140_, 3, v___f_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Std_Time_instOrdWallTime(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Std_Time_instOrdWallTime___closed__1, &l_Std_Time_instOrdWallTime___closed__1_once, _init_l_Std_Time_instOrdWallTime___closed__1);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringWallTime___lam__0(lean_object* v_s_142_){
_start:
{
lean_object* v_second_143_; lean_object* v___x_144_; 
v_second_143_ = lean_ctor_get(v_s_142_, 0);
v___x_144_ = l_Int_repr(v_second_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringWallTime___lam__0___boxed(lean_object* v_s_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_Time_instToStringWallTime___lam__0(v_s_145_);
lean_dec_ref(v_s_145_);
return v_res_146_;
}
}
static lean_object* _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1000000000u);
v___x_153_ = lean_nat_to_int(v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime__1___lam__0(lean_object* v_s_154_, lean_object* v___y_155_){
_start:
{
lean_object* v_second_156_; lean_object* v_nano_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_171_; 
v_second_156_ = lean_ctor_get(v_s_154_, 0);
v_nano_157_ = lean_ctor_get(v_s_154_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_s_154_);
if (v_isSharedCheck_171_ == 0)
{
v___x_159_ = v_s_154_;
v_isShared_160_ = v_isSharedCheck_171_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_nano_157_);
lean_inc(v_second_156_);
lean_dec(v_s_154_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_171_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_nanos_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_161_ = ((lean_object*)(l_Std_Time_instReprWallTime__1___lam__0___closed__1));
v___x_162_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_163_ = lean_int_mul(v_second_156_, v___x_162_);
lean_dec(v_second_156_);
v_nanos_164_ = lean_int_add(v___x_163_, v_nano_157_);
lean_dec(v_nano_157_);
lean_dec(v___x_163_);
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanos_164_, v___x_165_);
lean_dec(v_nanos_164_);
if (v_isShared_160_ == 0)
{
lean_ctor_set_tag(v___x_159_, 5);
lean_ctor_set(v___x_159_, 1, v___x_166_);
lean_ctor_set(v___x_159_, 0, v___x_161_);
v___x_168_ = v___x_159_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v___x_166_);
v___x_168_ = v_reuseFailAlloc_170_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; 
v___x_169_ = l_Repr_addAppParen(v___x_168_, v___y_155_);
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime__1___lam__0___boxed(lean_object* v_s_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_Time_instReprWallTime__1___lam__0(v_s_172_, v___y_173_);
lean_dec(v___y_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofDuration(lean_object* v_duration_177_){
_start:
{
lean_inc_ref(v_duration_177_);
return v_duration_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofDuration___boxed(lean_object* v_duration_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Std_Time_WallTime_ofDuration(v_duration_178_);
lean_dec_ref(v_duration_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofSeconds(lean_object* v_secs_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_secs_180_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofNanoseconds(lean_object* v_nanos_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofNanoseconds___boxed(lean_object* v_nanos_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Std_Time_WallTime_ofNanoseconds(v_nanos_185_);
lean_dec(v_nanos_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toSeconds(lean_object* v_wt_187_){
_start:
{
lean_object* v_second_188_; 
v_second_188_ = lean_ctor_get(v_wt_187_, 0);
lean_inc(v_second_188_);
return v_second_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toSeconds___boxed(lean_object* v_wt_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_Time_WallTime_toSeconds(v_wt_189_);
lean_dec_ref(v_wt_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toNanoseconds(lean_object* v_wt_191_){
_start:
{
lean_object* v_second_192_; lean_object* v_nano_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v_nanos_196_; 
v_second_192_ = lean_ctor_get(v_wt_191_, 0);
v_nano_193_ = lean_ctor_get(v_wt_191_, 1);
v___x_194_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_195_ = lean_int_mul(v_second_192_, v___x_194_);
v_nanos_196_ = lean_int_add(v___x_195_, v_nano_193_);
lean_dec(v___x_195_);
return v_nanos_196_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toNanoseconds___boxed(lean_object* v_wt_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Std_Time_WallTime_toNanoseconds(v_wt_197_);
lean_dec_ref(v_wt_197_);
return v_res_198_;
}
}
static lean_object* _init_l_Std_Time_WallTime_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(60u);
v___x_200_ = lean_nat_to_int(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMinutes(lean_object* v_tm_201_){
_start:
{
lean_object* v_second_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_second_202_ = lean_ctor_get(v_tm_201_, 0);
v___x_203_ = lean_obj_once(&l_Std_Time_WallTime_toMinutes___closed__0, &l_Std_Time_WallTime_toMinutes___closed__0_once, _init_l_Std_Time_WallTime_toMinutes___closed__0);
v___x_204_ = lean_int_div(v_second_202_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMinutes___boxed(lean_object* v_tm_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Time_WallTime_toMinutes(v_tm_205_);
lean_dec_ref(v_tm_205_);
return v_res_206_;
}
}
static lean_object* _init_l_Std_Time_WallTime_toDays___closed__0(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(86400u);
v___x_208_ = lean_nat_to_int(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDays(lean_object* v_tm_209_){
_start:
{
lean_object* v_second_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_second_210_ = lean_ctor_get(v_tm_209_, 0);
v___x_211_ = lean_obj_once(&l_Std_Time_WallTime_toDays___closed__0, &l_Std_Time_WallTime_toDays___closed__0_once, _init_l_Std_Time_WallTime_toDays___closed__0);
v___x_212_ = lean_int_div(v_second_210_, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDays___boxed(lean_object* v_tm_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Time_WallTime_toDays(v_tm_213_);
lean_dec_ref(v_tm_213_);
return v_res_214_;
}
}
static lean_object* _init_l_Std_Time_WallTime_ofMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(1000000u);
v___x_216_ = lean_nat_to_int(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofMilliseconds(lean_object* v_milli_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_obj_once(&l_Std_Time_WallTime_ofMilliseconds___closed__0, &l_Std_Time_WallTime_ofMilliseconds___closed__0_once, _init_l_Std_Time_WallTime_ofMilliseconds___closed__0);
v___x_219_ = lean_int_mul(v_milli_217_, v___x_218_);
v___x_220_ = l_Std_Time_Duration_ofNanoseconds(v___x_219_);
lean_dec(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofMilliseconds___boxed(lean_object* v_milli_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_Time_WallTime_ofMilliseconds(v_milli_221_);
lean_dec(v_milli_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMilliseconds(lean_object* v_tm_223_){
_start:
{
lean_object* v_second_224_; lean_object* v_nano_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v_second_224_ = lean_ctor_get(v_tm_223_, 0);
v_nano_225_ = lean_ctor_get(v_tm_223_, 1);
v___x_226_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_227_ = lean_int_mul(v_second_224_, v___x_226_);
v___x_228_ = lean_int_add(v___x_227_, v_nano_225_);
lean_dec(v___x_227_);
v___x_229_ = lean_obj_once(&l_Std_Time_WallTime_ofMilliseconds___closed__0, &l_Std_Time_WallTime_ofMilliseconds___closed__0_once, _init_l_Std_Time_WallTime_ofMilliseconds___closed__0);
v___x_230_ = lean_int_div(v___x_228_, v___x_229_);
lean_dec(v___x_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMilliseconds___boxed(lean_object* v_tm_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Time_WallTime_toMilliseconds(v_tm_231_);
lean_dec_ref(v_tm_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMilliseconds(lean_object* v_t_233_, lean_object* v_s_234_){
_start:
{
lean_object* v_second_235_; lean_object* v_nano_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v_second_240_; lean_object* v_nano_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_second_235_ = lean_ctor_get(v_t_233_, 0);
v_nano_236_ = lean_ctor_get(v_t_233_, 1);
v___x_237_ = lean_obj_once(&l_Std_Time_WallTime_ofMilliseconds___closed__0, &l_Std_Time_WallTime_ofMilliseconds___closed__0_once, _init_l_Std_Time_WallTime_ofMilliseconds___closed__0);
v___x_238_ = lean_int_mul(v_s_234_, v___x_237_);
v___x_239_ = l_Std_Time_Duration_ofNanoseconds(v___x_238_);
lean_dec(v___x_238_);
v_second_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_second_240_);
v_nano_241_ = lean_ctor_get(v___x_239_, 1);
lean_inc(v_nano_241_);
lean_dec_ref(v___x_239_);
v___x_242_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_243_ = lean_int_mul(v_second_235_, v___x_242_);
v___x_244_ = lean_int_add(v___x_243_, v_nano_236_);
lean_dec(v___x_243_);
v___x_245_ = lean_int_mul(v_second_240_, v___x_242_);
lean_dec(v_second_240_);
v___x_246_ = lean_int_add(v___x_245_, v_nano_241_);
lean_dec(v_nano_241_);
lean_dec(v___x_245_);
v___x_247_ = lean_int_add(v___x_244_, v___x_246_);
lean_dec(v___x_246_);
lean_dec(v___x_244_);
v___x_248_ = l_Std_Time_Duration_ofNanoseconds(v___x_247_);
lean_dec(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMilliseconds___boxed(lean_object* v_t_249_, lean_object* v_s_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_Time_WallTime_addMilliseconds(v_t_249_, v_s_250_);
lean_dec(v_s_250_);
lean_dec_ref(v_t_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMilliseconds(lean_object* v_t_252_, lean_object* v_s_253_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_second_257_; lean_object* v_nano_258_; lean_object* v_second_259_; lean_object* v_nano_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_254_ = lean_obj_once(&l_Std_Time_WallTime_ofMilliseconds___closed__0, &l_Std_Time_WallTime_ofMilliseconds___closed__0_once, _init_l_Std_Time_WallTime_ofMilliseconds___closed__0);
v___x_255_ = lean_int_mul(v_s_253_, v___x_254_);
v___x_256_ = l_Std_Time_Duration_ofNanoseconds(v___x_255_);
lean_dec(v___x_255_);
v_second_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_second_257_);
v_nano_258_ = lean_ctor_get(v___x_256_, 1);
lean_inc(v_nano_258_);
lean_dec_ref(v___x_256_);
v_second_259_ = lean_ctor_get(v_t_252_, 0);
v_nano_260_ = lean_ctor_get(v_t_252_, 1);
v___x_261_ = lean_int_neg(v_second_257_);
lean_dec(v_second_257_);
v___x_262_ = lean_int_neg(v_nano_258_);
lean_dec(v_nano_258_);
v___x_263_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_264_ = lean_int_mul(v_second_259_, v___x_263_);
v___x_265_ = lean_int_add(v___x_264_, v_nano_260_);
lean_dec(v___x_264_);
v___x_266_ = lean_int_mul(v___x_261_, v___x_263_);
lean_dec(v___x_261_);
v___x_267_ = lean_int_add(v___x_266_, v___x_262_);
lean_dec(v___x_262_);
lean_dec(v___x_266_);
v___x_268_ = lean_int_add(v___x_265_, v___x_267_);
lean_dec(v___x_267_);
lean_dec(v___x_265_);
v___x_269_ = l_Std_Time_Duration_ofNanoseconds(v___x_268_);
lean_dec(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMilliseconds___boxed(lean_object* v_t_270_, lean_object* v_s_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Std_Time_WallTime_subMilliseconds(v_t_270_, v_s_271_);
lean_dec(v_s_271_);
lean_dec_ref(v_t_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addNanoseconds(lean_object* v_t_273_, lean_object* v_s_274_){
_start:
{
lean_object* v_second_275_; lean_object* v_nano_276_; lean_object* v___x_277_; lean_object* v_second_278_; lean_object* v_nano_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v_second_275_ = lean_ctor_get(v_t_273_, 0);
v_nano_276_ = lean_ctor_get(v_t_273_, 1);
v___x_277_ = l_Std_Time_Duration_ofNanoseconds(v_s_274_);
v_second_278_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_second_278_);
v_nano_279_ = lean_ctor_get(v___x_277_, 1);
lean_inc(v_nano_279_);
lean_dec_ref(v___x_277_);
v___x_280_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_281_ = lean_int_mul(v_second_275_, v___x_280_);
v___x_282_ = lean_int_add(v___x_281_, v_nano_276_);
lean_dec(v___x_281_);
v___x_283_ = lean_int_mul(v_second_278_, v___x_280_);
lean_dec(v_second_278_);
v___x_284_ = lean_int_add(v___x_283_, v_nano_279_);
lean_dec(v_nano_279_);
lean_dec(v___x_283_);
v___x_285_ = lean_int_add(v___x_282_, v___x_284_);
lean_dec(v___x_284_);
lean_dec(v___x_282_);
v___x_286_ = l_Std_Time_Duration_ofNanoseconds(v___x_285_);
lean_dec(v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addNanoseconds___boxed(lean_object* v_t_287_, lean_object* v_s_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_Time_WallTime_addNanoseconds(v_t_287_, v_s_288_);
lean_dec(v_s_288_);
lean_dec_ref(v_t_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subNanoseconds(lean_object* v_t_290_, lean_object* v_s_291_){
_start:
{
lean_object* v___x_292_; lean_object* v_second_293_; lean_object* v_nano_294_; lean_object* v_second_295_; lean_object* v_nano_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_292_ = l_Std_Time_Duration_ofNanoseconds(v_s_291_);
v_second_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_second_293_);
v_nano_294_ = lean_ctor_get(v___x_292_, 1);
lean_inc(v_nano_294_);
lean_dec_ref(v___x_292_);
v_second_295_ = lean_ctor_get(v_t_290_, 0);
v_nano_296_ = lean_ctor_get(v_t_290_, 1);
v___x_297_ = lean_int_neg(v_second_293_);
lean_dec(v_second_293_);
v___x_298_ = lean_int_neg(v_nano_294_);
lean_dec(v_nano_294_);
v___x_299_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_300_ = lean_int_mul(v_second_295_, v___x_299_);
v___x_301_ = lean_int_add(v___x_300_, v_nano_296_);
lean_dec(v___x_300_);
v___x_302_ = lean_int_mul(v___x_297_, v___x_299_);
lean_dec(v___x_297_);
v___x_303_ = lean_int_add(v___x_302_, v___x_298_);
lean_dec(v___x_298_);
lean_dec(v___x_302_);
v___x_304_ = lean_int_add(v___x_301_, v___x_303_);
lean_dec(v___x_303_);
lean_dec(v___x_301_);
v___x_305_ = l_Std_Time_Duration_ofNanoseconds(v___x_304_);
lean_dec(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subNanoseconds___boxed(lean_object* v_t_306_, lean_object* v_s_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Std_Time_WallTime_subNanoseconds(v_t_306_, v_s_307_);
lean_dec(v_s_307_);
lean_dec_ref(v_t_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addSeconds(lean_object* v_t_309_, lean_object* v_s_310_){
_start:
{
lean_object* v_second_311_; lean_object* v_nano_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_second_311_ = lean_ctor_get(v_t_309_, 0);
v_nano_312_ = lean_ctor_get(v_t_309_, 1);
v___x_313_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_314_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_315_ = lean_int_mul(v_second_311_, v___x_314_);
v___x_316_ = lean_int_add(v___x_315_, v_nano_312_);
lean_dec(v___x_315_);
v___x_317_ = lean_int_mul(v_s_310_, v___x_314_);
v___x_318_ = lean_int_add(v___x_317_, v___x_313_);
lean_dec(v___x_317_);
v___x_319_ = lean_int_add(v___x_316_, v___x_318_);
lean_dec(v___x_318_);
lean_dec(v___x_316_);
v___x_320_ = l_Std_Time_Duration_ofNanoseconds(v___x_319_);
lean_dec(v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addSeconds___boxed(lean_object* v_t_321_, lean_object* v_s_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Std_Time_WallTime_addSeconds(v_t_321_, v_s_322_);
lean_dec(v_s_322_);
lean_dec_ref(v_t_321_);
return v_res_323_;
}
}
static lean_object* _init_l_Std_Time_WallTime_subSeconds___closed__0(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_325_ = lean_int_neg(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subSeconds(lean_object* v_t_326_, lean_object* v_s_327_){
_start:
{
lean_object* v_second_328_; lean_object* v_nano_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_second_328_ = lean_ctor_get(v_t_326_, 0);
v_nano_329_ = lean_ctor_get(v_t_326_, 1);
v___x_330_ = lean_int_neg(v_s_327_);
v___x_331_ = lean_obj_once(&l_Std_Time_WallTime_subSeconds___closed__0, &l_Std_Time_WallTime_subSeconds___closed__0_once, _init_l_Std_Time_WallTime_subSeconds___closed__0);
v___x_332_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_333_ = lean_int_mul(v_second_328_, v___x_332_);
v___x_334_ = lean_int_add(v___x_333_, v_nano_329_);
lean_dec(v___x_333_);
v___x_335_ = lean_int_mul(v___x_330_, v___x_332_);
lean_dec(v___x_330_);
v___x_336_ = lean_int_add(v___x_335_, v___x_331_);
lean_dec(v___x_335_);
v___x_337_ = lean_int_add(v___x_334_, v___x_336_);
lean_dec(v___x_336_);
lean_dec(v___x_334_);
v___x_338_ = l_Std_Time_Duration_ofNanoseconds(v___x_337_);
lean_dec(v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subSeconds___boxed(lean_object* v_t_339_, lean_object* v_s_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_Time_WallTime_subSeconds(v_t_339_, v_s_340_);
lean_dec(v_s_340_);
lean_dec_ref(v_t_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMinutes(lean_object* v_t_342_, lean_object* v_m_343_){
_start:
{
lean_object* v_second_344_; lean_object* v_nano_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_second_344_ = lean_ctor_get(v_t_342_, 0);
v_nano_345_ = lean_ctor_get(v_t_342_, 1);
v___x_346_ = lean_obj_once(&l_Std_Time_WallTime_toMinutes___closed__0, &l_Std_Time_WallTime_toMinutes___closed__0_once, _init_l_Std_Time_WallTime_toMinutes___closed__0);
v___x_347_ = lean_int_mul(v_m_343_, v___x_346_);
v___x_348_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_349_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_350_ = lean_int_mul(v_second_344_, v___x_349_);
v___x_351_ = lean_int_add(v___x_350_, v_nano_345_);
lean_dec(v___x_350_);
v___x_352_ = lean_int_mul(v___x_347_, v___x_349_);
lean_dec(v___x_347_);
v___x_353_ = lean_int_add(v___x_352_, v___x_348_);
lean_dec(v___x_352_);
v___x_354_ = lean_int_add(v___x_351_, v___x_353_);
lean_dec(v___x_353_);
lean_dec(v___x_351_);
v___x_355_ = l_Std_Time_Duration_ofNanoseconds(v___x_354_);
lean_dec(v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMinutes___boxed(lean_object* v_t_356_, lean_object* v_m_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Time_WallTime_addMinutes(v_t_356_, v_m_357_);
lean_dec(v_m_357_);
lean_dec_ref(v_t_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMinutes(lean_object* v_t_359_, lean_object* v_m_360_){
_start:
{
lean_object* v_second_361_; lean_object* v_nano_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_second_361_ = lean_ctor_get(v_t_359_, 0);
v_nano_362_ = lean_ctor_get(v_t_359_, 1);
v___x_363_ = lean_obj_once(&l_Std_Time_WallTime_toMinutes___closed__0, &l_Std_Time_WallTime_toMinutes___closed__0_once, _init_l_Std_Time_WallTime_toMinutes___closed__0);
v___x_364_ = lean_int_mul(v_m_360_, v___x_363_);
v___x_365_ = lean_int_neg(v___x_364_);
lean_dec(v___x_364_);
v___x_366_ = lean_obj_once(&l_Std_Time_WallTime_subSeconds___closed__0, &l_Std_Time_WallTime_subSeconds___closed__0_once, _init_l_Std_Time_WallTime_subSeconds___closed__0);
v___x_367_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_368_ = lean_int_mul(v_second_361_, v___x_367_);
v___x_369_ = lean_int_add(v___x_368_, v_nano_362_);
lean_dec(v___x_368_);
v___x_370_ = lean_int_mul(v___x_365_, v___x_367_);
lean_dec(v___x_365_);
v___x_371_ = lean_int_add(v___x_370_, v___x_366_);
lean_dec(v___x_370_);
v___x_372_ = lean_int_add(v___x_369_, v___x_371_);
lean_dec(v___x_371_);
lean_dec(v___x_369_);
v___x_373_ = l_Std_Time_Duration_ofNanoseconds(v___x_372_);
lean_dec(v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMinutes___boxed(lean_object* v_t_374_, lean_object* v_m_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Std_Time_WallTime_subMinutes(v_t_374_, v_m_375_);
lean_dec(v_m_375_);
lean_dec_ref(v_t_374_);
return v_res_376_;
}
}
static lean_object* _init_l_Std_Time_WallTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_unsigned_to_nat(3600u);
v___x_378_ = lean_nat_to_int(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addHours(lean_object* v_t_379_, lean_object* v_h_380_){
_start:
{
lean_object* v_second_381_; lean_object* v_nano_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_second_381_ = lean_ctor_get(v_t_379_, 0);
v_nano_382_ = lean_ctor_get(v_t_379_, 1);
v___x_383_ = lean_obj_once(&l_Std_Time_WallTime_addHours___closed__0, &l_Std_Time_WallTime_addHours___closed__0_once, _init_l_Std_Time_WallTime_addHours___closed__0);
v___x_384_ = lean_int_mul(v_h_380_, v___x_383_);
v___x_385_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_386_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_387_ = lean_int_mul(v_second_381_, v___x_386_);
v___x_388_ = lean_int_add(v___x_387_, v_nano_382_);
lean_dec(v___x_387_);
v___x_389_ = lean_int_mul(v___x_384_, v___x_386_);
lean_dec(v___x_384_);
v___x_390_ = lean_int_add(v___x_389_, v___x_385_);
lean_dec(v___x_389_);
v___x_391_ = lean_int_add(v___x_388_, v___x_390_);
lean_dec(v___x_390_);
lean_dec(v___x_388_);
v___x_392_ = l_Std_Time_Duration_ofNanoseconds(v___x_391_);
lean_dec(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addHours___boxed(lean_object* v_t_393_, lean_object* v_h_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_Time_WallTime_addHours(v_t_393_, v_h_394_);
lean_dec(v_h_394_);
lean_dec_ref(v_t_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subHours(lean_object* v_t_396_, lean_object* v_h_397_){
_start:
{
lean_object* v_second_398_; lean_object* v_nano_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v_second_398_ = lean_ctor_get(v_t_396_, 0);
v_nano_399_ = lean_ctor_get(v_t_396_, 1);
v___x_400_ = lean_obj_once(&l_Std_Time_WallTime_addHours___closed__0, &l_Std_Time_WallTime_addHours___closed__0_once, _init_l_Std_Time_WallTime_addHours___closed__0);
v___x_401_ = lean_int_mul(v_h_397_, v___x_400_);
v___x_402_ = lean_int_neg(v___x_401_);
lean_dec(v___x_401_);
v___x_403_ = lean_obj_once(&l_Std_Time_WallTime_subSeconds___closed__0, &l_Std_Time_WallTime_subSeconds___closed__0_once, _init_l_Std_Time_WallTime_subSeconds___closed__0);
v___x_404_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_405_ = lean_int_mul(v_second_398_, v___x_404_);
v___x_406_ = lean_int_add(v___x_405_, v_nano_399_);
lean_dec(v___x_405_);
v___x_407_ = lean_int_mul(v___x_402_, v___x_404_);
lean_dec(v___x_402_);
v___x_408_ = lean_int_add(v___x_407_, v___x_403_);
lean_dec(v___x_407_);
v___x_409_ = lean_int_add(v___x_406_, v___x_408_);
lean_dec(v___x_408_);
lean_dec(v___x_406_);
v___x_410_ = l_Std_Time_Duration_ofNanoseconds(v___x_409_);
lean_dec(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subHours___boxed(lean_object* v_t_411_, lean_object* v_h_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_Time_WallTime_subHours(v_t_411_, v_h_412_);
lean_dec(v_h_412_);
lean_dec_ref(v_t_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDays(lean_object* v_t_414_, lean_object* v_d_415_){
_start:
{
lean_object* v_second_416_; lean_object* v_nano_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_second_416_ = lean_ctor_get(v_t_414_, 0);
v_nano_417_ = lean_ctor_get(v_t_414_, 1);
v___x_418_ = lean_obj_once(&l_Std_Time_WallTime_toDays___closed__0, &l_Std_Time_WallTime_toDays___closed__0_once, _init_l_Std_Time_WallTime_toDays___closed__0);
v___x_419_ = lean_int_mul(v_d_415_, v___x_418_);
v___x_420_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_421_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_422_ = lean_int_mul(v_second_416_, v___x_421_);
v___x_423_ = lean_int_add(v___x_422_, v_nano_417_);
lean_dec(v___x_422_);
v___x_424_ = lean_int_mul(v___x_419_, v___x_421_);
lean_dec(v___x_419_);
v___x_425_ = lean_int_add(v___x_424_, v___x_420_);
lean_dec(v___x_424_);
v___x_426_ = lean_int_add(v___x_423_, v___x_425_);
lean_dec(v___x_425_);
lean_dec(v___x_423_);
v___x_427_ = l_Std_Time_Duration_ofNanoseconds(v___x_426_);
lean_dec(v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDays___boxed(lean_object* v_t_428_, lean_object* v_d_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_Time_WallTime_addDays(v_t_428_, v_d_429_);
lean_dec(v_d_429_);
lean_dec_ref(v_t_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDays(lean_object* v_t_431_, lean_object* v_d_432_){
_start:
{
lean_object* v_second_433_; lean_object* v_nano_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_second_433_ = lean_ctor_get(v_t_431_, 0);
v_nano_434_ = lean_ctor_get(v_t_431_, 1);
v___x_435_ = lean_obj_once(&l_Std_Time_WallTime_toDays___closed__0, &l_Std_Time_WallTime_toDays___closed__0_once, _init_l_Std_Time_WallTime_toDays___closed__0);
v___x_436_ = lean_int_mul(v_d_432_, v___x_435_);
v___x_437_ = lean_int_neg(v___x_436_);
lean_dec(v___x_436_);
v___x_438_ = lean_obj_once(&l_Std_Time_WallTime_subSeconds___closed__0, &l_Std_Time_WallTime_subSeconds___closed__0_once, _init_l_Std_Time_WallTime_subSeconds___closed__0);
v___x_439_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_440_ = lean_int_mul(v_second_433_, v___x_439_);
v___x_441_ = lean_int_add(v___x_440_, v_nano_434_);
lean_dec(v___x_440_);
v___x_442_ = lean_int_mul(v___x_437_, v___x_439_);
lean_dec(v___x_437_);
v___x_443_ = lean_int_add(v___x_442_, v___x_438_);
lean_dec(v___x_442_);
v___x_444_ = lean_int_add(v___x_441_, v___x_443_);
lean_dec(v___x_443_);
lean_dec(v___x_441_);
v___x_445_ = l_Std_Time_Duration_ofNanoseconds(v___x_444_);
lean_dec(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDays___boxed(lean_object* v_t_446_, lean_object* v_d_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_Time_WallTime_subDays(v_t_446_, v_d_447_);
lean_dec(v_d_447_);
lean_dec_ref(v_t_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addWeeks(lean_object* v_t_449_, lean_object* v_d_450_){
_start:
{
lean_object* v_second_451_; lean_object* v_nano_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_second_451_ = lean_ctor_get(v_t_449_, 0);
v_nano_452_ = lean_ctor_get(v_t_449_, 1);
v___x_453_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__7, &l_Std_Time_instReprWallTime_repr___redArg___closed__7_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7);
v___x_454_ = lean_int_mul(v_d_450_, v___x_453_);
v___x_455_ = lean_obj_once(&l_Std_Time_WallTime_toDays___closed__0, &l_Std_Time_WallTime_toDays___closed__0_once, _init_l_Std_Time_WallTime_toDays___closed__0);
v___x_456_ = lean_int_mul(v___x_454_, v___x_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_458_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_459_ = lean_int_mul(v_second_451_, v___x_458_);
v___x_460_ = lean_int_add(v___x_459_, v_nano_452_);
lean_dec(v___x_459_);
v___x_461_ = lean_int_mul(v___x_456_, v___x_458_);
lean_dec(v___x_456_);
v___x_462_ = lean_int_add(v___x_461_, v___x_457_);
lean_dec(v___x_461_);
v___x_463_ = lean_int_add(v___x_460_, v___x_462_);
lean_dec(v___x_462_);
lean_dec(v___x_460_);
v___x_464_ = l_Std_Time_Duration_ofNanoseconds(v___x_463_);
lean_dec(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addWeeks___boxed(lean_object* v_t_465_, lean_object* v_d_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_Time_WallTime_addWeeks(v_t_465_, v_d_466_);
lean_dec(v_d_466_);
lean_dec_ref(v_t_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subWeeks(lean_object* v_t_468_, lean_object* v_d_469_){
_start:
{
lean_object* v_second_470_; lean_object* v_nano_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v_second_470_ = lean_ctor_get(v_t_468_, 0);
v_nano_471_ = lean_ctor_get(v_t_468_, 1);
v___x_472_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__7, &l_Std_Time_instReprWallTime_repr___redArg___closed__7_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7);
v___x_473_ = lean_int_mul(v_d_469_, v___x_472_);
v___x_474_ = lean_obj_once(&l_Std_Time_WallTime_toDays___closed__0, &l_Std_Time_WallTime_toDays___closed__0_once, _init_l_Std_Time_WallTime_toDays___closed__0);
v___x_475_ = lean_int_mul(v___x_473_, v___x_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_int_neg(v___x_475_);
lean_dec(v___x_475_);
v___x_477_ = lean_obj_once(&l_Std_Time_WallTime_subSeconds___closed__0, &l_Std_Time_WallTime_subSeconds___closed__0_once, _init_l_Std_Time_WallTime_subSeconds___closed__0);
v___x_478_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_479_ = lean_int_mul(v_second_470_, v___x_478_);
v___x_480_ = lean_int_add(v___x_479_, v_nano_471_);
lean_dec(v___x_479_);
v___x_481_ = lean_int_mul(v___x_476_, v___x_478_);
lean_dec(v___x_476_);
v___x_482_ = lean_int_add(v___x_481_, v___x_477_);
lean_dec(v___x_481_);
v___x_483_ = lean_int_add(v___x_480_, v___x_482_);
lean_dec(v___x_482_);
lean_dec(v___x_480_);
v___x_484_ = l_Std_Time_Duration_ofNanoseconds(v___x_483_);
lean_dec(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subWeeks___boxed(lean_object* v_t_485_, lean_object* v_d_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Std_Time_WallTime_subWeeks(v_t_485_, v_d_486_);
lean_dec(v_d_486_);
lean_dec_ref(v_t_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDuration(lean_object* v_t_488_, lean_object* v_d_489_){
_start:
{
lean_object* v_second_490_; lean_object* v_nano_491_; lean_object* v_second_492_; lean_object* v_nano_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_second_490_ = lean_ctor_get(v_t_488_, 0);
v_nano_491_ = lean_ctor_get(v_t_488_, 1);
v_second_492_ = lean_ctor_get(v_d_489_, 0);
v_nano_493_ = lean_ctor_get(v_d_489_, 1);
v___x_494_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_495_ = lean_int_mul(v_second_490_, v___x_494_);
v___x_496_ = lean_int_add(v___x_495_, v_nano_491_);
lean_dec(v___x_495_);
v___x_497_ = lean_int_mul(v_second_492_, v___x_494_);
v___x_498_ = lean_int_add(v___x_497_, v_nano_493_);
lean_dec(v___x_497_);
v___x_499_ = lean_int_add(v___x_496_, v___x_498_);
lean_dec(v___x_498_);
lean_dec(v___x_496_);
v___x_500_ = l_Std_Time_Duration_ofNanoseconds(v___x_499_);
lean_dec(v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDuration___boxed(lean_object* v_t_501_, lean_object* v_d_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_Time_WallTime_addDuration(v_t_501_, v_d_502_);
lean_dec_ref(v_d_502_);
lean_dec_ref(v_t_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDuration(lean_object* v_t_504_, lean_object* v_d_505_){
_start:
{
lean_object* v_second_506_; lean_object* v_nano_507_; lean_object* v_second_508_; lean_object* v_nano_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v_second_506_ = lean_ctor_get(v_d_505_, 0);
v_nano_507_ = lean_ctor_get(v_d_505_, 1);
v_second_508_ = lean_ctor_get(v_t_504_, 0);
v_nano_509_ = lean_ctor_get(v_t_504_, 1);
v___x_510_ = lean_int_neg(v_second_506_);
v___x_511_ = lean_int_neg(v_nano_507_);
v___x_512_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_513_ = lean_int_mul(v_second_508_, v___x_512_);
v___x_514_ = lean_int_add(v___x_513_, v_nano_509_);
lean_dec(v___x_513_);
v___x_515_ = lean_int_mul(v___x_510_, v___x_512_);
lean_dec(v___x_510_);
v___x_516_ = lean_int_add(v___x_515_, v___x_511_);
lean_dec(v___x_511_);
lean_dec(v___x_515_);
v___x_517_ = lean_int_add(v___x_514_, v___x_516_);
lean_dec(v___x_516_);
lean_dec(v___x_514_);
v___x_518_ = l_Std_Time_Duration_ofNanoseconds(v___x_517_);
lean_dec(v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDuration___boxed(lean_object* v_t_519_, lean_object* v_d_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Std_Time_WallTime_subDuration(v_t_519_, v_d_520_);
lean_dec_ref(v_d_520_);
lean_dec_ref(v_t_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDuration(lean_object* v_wt_522_){
_start:
{
lean_inc_ref(v_wt_522_);
return v_wt_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDuration___boxed(lean_object* v_wt_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_Time_WallTime_toDuration(v_wt_523_);
lean_dec_ref(v_wt_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_instHSubDuration__1___lam__0(lean_object* v_x_557_, lean_object* v_y_558_){
_start:
{
lean_object* v_second_559_; lean_object* v_nano_560_; lean_object* v_second_561_; lean_object* v_nano_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_second_559_ = lean_ctor_get(v_y_558_, 0);
v_nano_560_ = lean_ctor_get(v_y_558_, 1);
v_second_561_ = lean_ctor_get(v_x_557_, 0);
v_nano_562_ = lean_ctor_get(v_x_557_, 1);
v___x_563_ = lean_int_neg(v_second_559_);
v___x_564_ = lean_int_neg(v_nano_560_);
v___x_565_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_566_ = lean_int_mul(v_second_561_, v___x_565_);
v___x_567_ = lean_int_add(v___x_566_, v_nano_562_);
lean_dec(v___x_566_);
v___x_568_ = lean_int_mul(v___x_563_, v___x_565_);
lean_dec(v___x_563_);
v___x_569_ = lean_int_add(v___x_568_, v___x_564_);
lean_dec(v___x_564_);
lean_dec(v___x_568_);
v___x_570_ = lean_int_add(v___x_567_, v___x_569_);
lean_dec(v___x_569_);
lean_dec(v___x_567_);
v___x_571_ = l_Std_Time_Duration_ofNanoseconds(v___x_570_);
lean_dec(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_instHSubDuration__1___lam__0___boxed(lean_object* v_x_572_, lean_object* v_y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Std_Time_WallTime_instHSubDuration__1___lam__0(v_x_572_, v_y_573_);
lean_dec_ref(v_y_573_);
lean_dec_ref(v_x_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_instOfNat(lean_object* v_n_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_nat_to_int(v_n_577_);
v___x_579_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
return v___x_580_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Duration(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_DateTime_WallTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Duration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedWallTime_default = _init_l_Std_Time_instInhabitedWallTime_default();
lean_mark_persistent(l_Std_Time_instInhabitedWallTime_default);
l_Std_Time_instInhabitedWallTime = _init_l_Std_Time_instInhabitedWallTime();
lean_mark_persistent(l_Std_Time_instInhabitedWallTime);
l_Std_Time_instLEWallTime = _init_l_Std_Time_instLEWallTime();
lean_mark_persistent(l_Std_Time_instLEWallTime);
l_Std_Time_instLTWallTime = _init_l_Std_Time_instLTWallTime();
lean_mark_persistent(l_Std_Time_instLTWallTime);
l_Std_Time_instOrdWallTime = _init_l_Std_Time_instOrdWallTime();
lean_mark_persistent(l_Std_Time_instOrdWallTime);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_DateTime_WallTime(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Std_Time_Duration(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_DateTime_WallTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Duration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_DateTime_WallTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_DateTime_WallTime(builtin);
}
#ifdef __cplusplus
}
#endif

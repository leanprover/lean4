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
uint8_t l_Std_Time_instDecidableEqWallTime_decEq(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_97_, v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqWallTime_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_97_ = stack[0].m_obj;
lean_object* v_x_98_ = stack[1].m_obj;
uint8_t v_res_100_;
v_res_100_ = l_Std_Time_instDecidableEqWallTime_decEq(v_x_97_, v_x_98_);
stack->m_num = v_res_100_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqWallTime_decEq___boxed(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Std_Time_instDecidableEqWallTime_decEq(v_x_101_, v_x_102_);
lean_dec_ref(v_x_102_);
lean_dec_ref(v_x_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
uint8_t l_Std_Time_instDecidableEqWallTime(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_105_, v_x_106_);
return v___x_107_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqWallTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_105_ = stack[0].m_obj;
lean_object* v_x_106_ = stack[1].m_obj;
uint8_t v_res_108_;
v_res_108_ = l_Std_Time_instDecidableEqWallTime(v_x_105_, v_x_106_);
stack->m_num = v_res_108_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqWallTime___boxed(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Std_Time_instDecidableEqWallTime(v_x_109_, v_x_110_);
lean_dec_ref(v_x_110_);
lean_dec_ref(v_x_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedWallTime_default___closed__0(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedWallTime_default(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Std_Time_instInhabitedWallTime_default___closed__0, &l_Std_Time_instInhabitedWallTime_default___closed__0_once, _init_l_Std_Time_instInhabitedWallTime_default___closed__0);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedWallTime_default_spec__0(lean_object* v_a_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_nat_to_int(v_a_116_);
v___x_118_ = l_Rat_ofInt(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedWallTime(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Std_Time_instInhabitedWallTime_default;
return v___x_119_;
}
}
static lean_object* _init_l_Std_Time_instLEWallTime(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_box(0);
return v___x_120_;
}
}
uint8_t l_Std_Time_instDecidableLeWallTime(lean_object* v_x_121_, lean_object* v_y_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = l_Std_Time_Duration_instDecidableLe(v_x_121_, v_y_122_);
return v___x_123_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableLeWallTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_121_ = stack[0].m_obj;
lean_object* v_y_122_ = stack[1].m_obj;
uint8_t v_res_124_;
v_res_124_ = l_Std_Time_instDecidableLeWallTime(v_x_121_, v_y_122_);
stack->m_num = v_res_124_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeWallTime___boxed(lean_object* v_x_125_, lean_object* v_y_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Std_Time_instDecidableLeWallTime(v_x_125_, v_y_126_);
lean_dec_ref(v_y_126_);
lean_dec_ref(v_x_125_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
static lean_object* _init_l_Std_Time_instLTWallTime(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(0);
return v___x_129_;
}
}
uint8_t l_Std_Time_instDecidableLtWallTime(lean_object* v_x_130_, lean_object* v_y_131_){
_start:
{
uint8_t v___x_132_; 
v___x_132_ = l_Std_Time_Duration_instDecidableLt(v_x_130_, v_y_131_);
return v___x_132_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableLtWallTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_130_ = stack[0].m_obj;
lean_object* v_y_131_ = stack[1].m_obj;
uint8_t v_res_133_;
v_res_133_ = l_Std_Time_instDecidableLtWallTime(v_x_130_, v_y_131_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtWallTime___boxed(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Std_Time_instDecidableLtWallTime(v_x_134_, v_y_135_);
lean_dec_ref(v_y_135_);
lean_dec_ref(v_x_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdWallTime___lam__0(lean_object* v_x_138_){
_start:
{
lean_inc_ref(v_x_138_);
return v_x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdWallTime___lam__0___boxed(lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_Time_instOrdWallTime___lam__0(v_x_139_);
lean_dec_ref(v_x_139_);
return v_res_140_;
}
}
static lean_object* _init_l_Std_Time_instOrdWallTime___closed__1(void){
_start:
{
lean_object* v___f_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___f_142_ = ((lean_object*)(l_Std_Time_instOrdWallTime___closed__0));
v___x_143_ = l_Std_Time_instOrdDuration;
v___x_144_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_144_, 0, lean_box(0));
lean_closure_set(v___x_144_, 1, lean_box(0));
lean_closure_set(v___x_144_, 2, v___x_143_);
lean_closure_set(v___x_144_, 3, v___f_142_);
return v___x_144_;
}
}
static lean_object* _init_l_Std_Time_instOrdWallTime(void){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&l_Std_Time_instOrdWallTime___closed__1, &l_Std_Time_instOrdWallTime___closed__1_once, _init_l_Std_Time_instOrdWallTime___closed__1);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringWallTime___lam__0(lean_object* v_s_146_){
_start:
{
lean_object* v_second_147_; lean_object* v___x_148_; 
v_second_147_ = lean_ctor_get(v_s_146_, 0);
v___x_148_ = l_Int_repr(v_second_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringWallTime___lam__0___boxed(lean_object* v_s_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_Time_instToStringWallTime___lam__0(v_s_149_);
lean_dec_ref(v_s_149_);
return v_res_150_;
}
}
static lean_object* _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1000000000u);
v___x_157_ = lean_nat_to_int(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime__1___lam__0(lean_object* v_s_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_second_160_; lean_object* v_nano_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_175_; 
v_second_160_ = lean_ctor_get(v_s_158_, 0);
v_nano_161_ = lean_ctor_get(v_s_158_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_s_158_);
if (v_isSharedCheck_175_ == 0)
{
v___x_163_ = v_s_158_;
v_isShared_164_ = v_isSharedCheck_175_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_nano_161_);
lean_inc(v_second_160_);
lean_dec(v_s_158_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_175_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_nanos_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_172_; 
v___x_165_ = ((lean_object*)(l_Std_Time_instReprWallTime__1___lam__0___closed__1));
v___x_166_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_167_ = lean_int_mul(v_second_160_, v___x_166_);
lean_dec(v_second_160_);
v_nanos_168_ = lean_int_add(v___x_167_, v_nano_161_);
lean_dec(v_nano_161_);
lean_dec(v___x_167_);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanos_168_, v___x_169_);
lean_dec(v_nanos_168_);
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 5);
lean_ctor_set(v___x_163_, 1, v___x_170_);
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_172_ = v___x_163_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___x_170_);
v___x_172_ = v_reuseFailAlloc_174_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
lean_object* v___x_173_; 
v___x_173_ = l_Repr_addAppParen(v___x_172_, v___y_159_);
return v___x_173_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprWallTime__1___lam__0___boxed(lean_object* v_s_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_Time_instReprWallTime__1___lam__0(v_s_176_, v___y_177_);
lean_dec(v___y_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofDuration(lean_object* v_duration_181_){
_start:
{
lean_inc_ref(v_duration_181_);
return v_duration_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofDuration___boxed(lean_object* v_duration_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Std_Time_WallTime_ofDuration(v_duration_182_);
lean_dec_ref(v_duration_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofSeconds(lean_object* v_secs_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v_secs_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofNanoseconds(lean_object* v_nanos_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofNanoseconds___boxed(lean_object* v_nanos_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_Time_WallTime_ofNanoseconds(v_nanos_189_);
lean_dec(v_nanos_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toSeconds(lean_object* v_wt_191_){
_start:
{
lean_object* v_second_192_; 
v_second_192_ = lean_ctor_get(v_wt_191_, 0);
lean_inc(v_second_192_);
return v_second_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toSeconds___boxed(lean_object* v_wt_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Std_Time_WallTime_toSeconds(v_wt_193_);
lean_dec_ref(v_wt_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toNanoseconds(lean_object* v_wt_195_){
_start:
{
lean_object* v_second_196_; lean_object* v_nano_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v_nanos_200_; 
v_second_196_ = lean_ctor_get(v_wt_195_, 0);
v_nano_197_ = lean_ctor_get(v_wt_195_, 1);
v___x_198_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_199_ = lean_int_mul(v_second_196_, v___x_198_);
v_nanos_200_ = lean_int_add(v___x_199_, v_nano_197_);
lean_dec(v___x_199_);
return v_nanos_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toNanoseconds___boxed(lean_object* v_wt_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Time_WallTime_toNanoseconds(v_wt_201_);
lean_dec_ref(v_wt_201_);
return v_res_202_;
}
}
static lean_object* _init_l_Std_Time_WallTime_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_203_ = lean_unsigned_to_nat(60u);
v___x_204_ = lean_nat_to_int(v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMinutes(lean_object* v_tm_205_){
_start:
{
lean_object* v_second_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_second_206_ = lean_ctor_get(v_tm_205_, 0);
v___x_207_ = lean_obj_once(&l_Std_Time_WallTime_toMinutes___closed__0, &l_Std_Time_WallTime_toMinutes___closed__0_once, _init_l_Std_Time_WallTime_toMinutes___closed__0);
v___x_208_ = lean_int_div(v_second_206_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMinutes___boxed(lean_object* v_tm_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Time_WallTime_toMinutes(v_tm_209_);
lean_dec_ref(v_tm_209_);
return v_res_210_;
}
}
static lean_object* _init_l_Std_Time_WallTime_toDays___closed__0(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(86400u);
v___x_212_ = lean_nat_to_int(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDays(lean_object* v_tm_213_){
_start:
{
lean_object* v_second_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v_second_214_ = lean_ctor_get(v_tm_213_, 0);
v___x_215_ = lean_obj_once(&l_Std_Time_WallTime_toDays___closed__0, &l_Std_Time_WallTime_toDays___closed__0_once, _init_l_Std_Time_WallTime_toDays___closed__0);
v___x_216_ = lean_int_div(v_second_214_, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDays___boxed(lean_object* v_tm_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_Time_WallTime_toDays(v_tm_217_);
lean_dec_ref(v_tm_217_);
return v_res_218_;
}
}
static lean_object* _init_l_Std_Time_WallTime_ofMilliseconds___closed__0(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_unsigned_to_nat(1000000u);
v___x_220_ = lean_nat_to_int(v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofMilliseconds(lean_object* v_milli_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_obj_once(&l_Std_Time_WallTime_ofMilliseconds___closed__0, &l_Std_Time_WallTime_ofMilliseconds___closed__0_once, _init_l_Std_Time_WallTime_ofMilliseconds___closed__0);
v___x_223_ = lean_int_mul(v_milli_221_, v___x_222_);
v___x_224_ = l_Std_Time_Duration_ofNanoseconds(v___x_223_);
lean_dec(v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofMilliseconds___boxed(lean_object* v_milli_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_Time_WallTime_ofMilliseconds(v_milli_225_);
lean_dec(v_milli_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMilliseconds(lean_object* v_tm_227_){
_start:
{
lean_object* v_second_228_; lean_object* v_nano_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_second_228_ = lean_ctor_get(v_tm_227_, 0);
v_nano_229_ = lean_ctor_get(v_tm_227_, 1);
v___x_230_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_231_ = lean_int_mul(v_second_228_, v___x_230_);
v___x_232_ = lean_int_add(v___x_231_, v_nano_229_);
lean_dec(v___x_231_);
v___x_233_ = lean_obj_once(&l_Std_Time_WallTime_ofMilliseconds___closed__0, &l_Std_Time_WallTime_ofMilliseconds___closed__0_once, _init_l_Std_Time_WallTime_ofMilliseconds___closed__0);
v___x_234_ = lean_int_div(v___x_232_, v___x_233_);
lean_dec(v___x_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toMilliseconds___boxed(lean_object* v_tm_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Time_WallTime_toMilliseconds(v_tm_235_);
lean_dec_ref(v_tm_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMilliseconds(lean_object* v_t_237_, lean_object* v_s_238_){
_start:
{
lean_object* v_second_239_; lean_object* v_nano_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v_second_244_; lean_object* v_nano_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_nanos_248_; lean_object* v___x_249_; lean_object* v_nanos_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_second_239_ = lean_ctor_get(v_t_237_, 0);
v_nano_240_ = lean_ctor_get(v_t_237_, 1);
v___x_241_ = lean_obj_once(&l_Std_Time_WallTime_ofMilliseconds___closed__0, &l_Std_Time_WallTime_ofMilliseconds___closed__0_once, _init_l_Std_Time_WallTime_ofMilliseconds___closed__0);
v___x_242_ = lean_int_mul(v_s_238_, v___x_241_);
v___x_243_ = l_Std_Time_Duration_ofNanoseconds(v___x_242_);
lean_dec(v___x_242_);
v_second_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_second_244_);
v_nano_245_ = lean_ctor_get(v___x_243_, 1);
lean_inc(v_nano_245_);
lean_dec_ref(v___x_243_);
v___x_246_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_247_ = lean_int_mul(v_second_239_, v___x_246_);
v_nanos_248_ = lean_int_add(v___x_247_, v_nano_240_);
lean_dec(v___x_247_);
v___x_249_ = lean_int_mul(v_second_244_, v___x_246_);
lean_dec(v_second_244_);
v_nanos_250_ = lean_int_add(v___x_249_, v_nano_245_);
lean_dec(v_nano_245_);
lean_dec(v___x_249_);
v___x_251_ = lean_int_add(v_nanos_248_, v_nanos_250_);
lean_dec(v_nanos_250_);
lean_dec(v_nanos_248_);
v___x_252_ = l_Std_Time_Duration_ofNanoseconds(v___x_251_);
lean_dec(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMilliseconds___boxed(lean_object* v_t_253_, lean_object* v_s_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_Time_WallTime_addMilliseconds(v_t_253_, v_s_254_);
lean_dec(v_s_254_);
lean_dec_ref(v_t_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMilliseconds(lean_object* v_t_256_, lean_object* v_s_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_second_261_; lean_object* v_nano_262_; lean_object* v_second_263_; lean_object* v_nano_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_nanos_269_; lean_object* v___x_270_; lean_object* v_nanos_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_258_ = lean_obj_once(&l_Std_Time_WallTime_ofMilliseconds___closed__0, &l_Std_Time_WallTime_ofMilliseconds___closed__0_once, _init_l_Std_Time_WallTime_ofMilliseconds___closed__0);
v___x_259_ = lean_int_mul(v_s_257_, v___x_258_);
v___x_260_ = l_Std_Time_Duration_ofNanoseconds(v___x_259_);
lean_dec(v___x_259_);
v_second_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_second_261_);
v_nano_262_ = lean_ctor_get(v___x_260_, 1);
lean_inc(v_nano_262_);
lean_dec_ref(v___x_260_);
v_second_263_ = lean_ctor_get(v_t_256_, 0);
v_nano_264_ = lean_ctor_get(v_t_256_, 1);
v___x_265_ = lean_int_neg(v_second_261_);
lean_dec(v_second_261_);
v___x_266_ = lean_int_neg(v_nano_262_);
lean_dec(v_nano_262_);
v___x_267_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_268_ = lean_int_mul(v_second_263_, v___x_267_);
v_nanos_269_ = lean_int_add(v___x_268_, v_nano_264_);
lean_dec(v___x_268_);
v___x_270_ = lean_int_mul(v___x_265_, v___x_267_);
lean_dec(v___x_265_);
v_nanos_271_ = lean_int_add(v___x_270_, v___x_266_);
lean_dec(v___x_266_);
lean_dec(v___x_270_);
v___x_272_ = lean_int_add(v_nanos_269_, v_nanos_271_);
lean_dec(v_nanos_271_);
lean_dec(v_nanos_269_);
v___x_273_ = l_Std_Time_Duration_ofNanoseconds(v___x_272_);
lean_dec(v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMilliseconds___boxed(lean_object* v_t_274_, lean_object* v_s_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_Time_WallTime_subMilliseconds(v_t_274_, v_s_275_);
lean_dec(v_s_275_);
lean_dec_ref(v_t_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addNanoseconds(lean_object* v_t_277_, lean_object* v_s_278_){
_start:
{
lean_object* v_second_279_; lean_object* v_nano_280_; lean_object* v___x_281_; lean_object* v_second_282_; lean_object* v_nano_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_nanos_286_; lean_object* v___x_287_; lean_object* v_nanos_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_second_279_ = lean_ctor_get(v_t_277_, 0);
v_nano_280_ = lean_ctor_get(v_t_277_, 1);
v___x_281_ = l_Std_Time_Duration_ofNanoseconds(v_s_278_);
v_second_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_second_282_);
v_nano_283_ = lean_ctor_get(v___x_281_, 1);
lean_inc(v_nano_283_);
lean_dec_ref(v___x_281_);
v___x_284_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_285_ = lean_int_mul(v_second_279_, v___x_284_);
v_nanos_286_ = lean_int_add(v___x_285_, v_nano_280_);
lean_dec(v___x_285_);
v___x_287_ = lean_int_mul(v_second_282_, v___x_284_);
lean_dec(v_second_282_);
v_nanos_288_ = lean_int_add(v___x_287_, v_nano_283_);
lean_dec(v_nano_283_);
lean_dec(v___x_287_);
v___x_289_ = lean_int_add(v_nanos_286_, v_nanos_288_);
lean_dec(v_nanos_288_);
lean_dec(v_nanos_286_);
v___x_290_ = l_Std_Time_Duration_ofNanoseconds(v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addNanoseconds___boxed(lean_object* v_t_291_, lean_object* v_s_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_Time_WallTime_addNanoseconds(v_t_291_, v_s_292_);
lean_dec(v_s_292_);
lean_dec_ref(v_t_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subNanoseconds(lean_object* v_t_294_, lean_object* v_s_295_){
_start:
{
lean_object* v___x_296_; lean_object* v_second_297_; lean_object* v_nano_298_; lean_object* v_second_299_; lean_object* v_nano_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_nanos_305_; lean_object* v___x_306_; lean_object* v_nanos_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_296_ = l_Std_Time_Duration_ofNanoseconds(v_s_295_);
v_second_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_second_297_);
v_nano_298_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_nano_298_);
lean_dec_ref(v___x_296_);
v_second_299_ = lean_ctor_get(v_t_294_, 0);
v_nano_300_ = lean_ctor_get(v_t_294_, 1);
v___x_301_ = lean_int_neg(v_second_297_);
lean_dec(v_second_297_);
v___x_302_ = lean_int_neg(v_nano_298_);
lean_dec(v_nano_298_);
v___x_303_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_304_ = lean_int_mul(v_second_299_, v___x_303_);
v_nanos_305_ = lean_int_add(v___x_304_, v_nano_300_);
lean_dec(v___x_304_);
v___x_306_ = lean_int_mul(v___x_301_, v___x_303_);
lean_dec(v___x_301_);
v_nanos_307_ = lean_int_add(v___x_306_, v___x_302_);
lean_dec(v___x_302_);
lean_dec(v___x_306_);
v___x_308_ = lean_int_add(v_nanos_305_, v_nanos_307_);
lean_dec(v_nanos_307_);
lean_dec(v_nanos_305_);
v___x_309_ = l_Std_Time_Duration_ofNanoseconds(v___x_308_);
lean_dec(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subNanoseconds___boxed(lean_object* v_t_310_, lean_object* v_s_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_Time_WallTime_subNanoseconds(v_t_310_, v_s_311_);
lean_dec(v_s_311_);
lean_dec_ref(v_t_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addSeconds(lean_object* v_t_313_, lean_object* v_s_314_){
_start:
{
lean_object* v_second_315_; lean_object* v_nano_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_nanos_320_; lean_object* v___x_321_; lean_object* v_nanos_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_second_315_ = lean_ctor_get(v_t_313_, 0);
v_nano_316_ = lean_ctor_get(v_t_313_, 1);
v___x_317_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_318_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_319_ = lean_int_mul(v_second_315_, v___x_318_);
v_nanos_320_ = lean_int_add(v___x_319_, v_nano_316_);
lean_dec(v___x_319_);
v___x_321_ = lean_int_mul(v_s_314_, v___x_318_);
v_nanos_322_ = lean_int_add(v___x_321_, v___x_317_);
lean_dec(v___x_321_);
v___x_323_ = lean_int_add(v_nanos_320_, v_nanos_322_);
lean_dec(v_nanos_322_);
lean_dec(v_nanos_320_);
v___x_324_ = l_Std_Time_Duration_ofNanoseconds(v___x_323_);
lean_dec(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addSeconds___boxed(lean_object* v_t_325_, lean_object* v_s_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Std_Time_WallTime_addSeconds(v_t_325_, v_s_326_);
lean_dec(v_s_326_);
lean_dec_ref(v_t_325_);
return v_res_327_;
}
}
static lean_object* _init_l_Std_Time_WallTime_subSeconds___closed__0(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_329_ = lean_int_neg(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subSeconds(lean_object* v_t_330_, lean_object* v_s_331_){
_start:
{
lean_object* v_second_332_; lean_object* v_nano_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v_nanos_338_; lean_object* v___x_339_; lean_object* v_nanos_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_second_332_ = lean_ctor_get(v_t_330_, 0);
v_nano_333_ = lean_ctor_get(v_t_330_, 1);
v___x_334_ = lean_int_neg(v_s_331_);
v___x_335_ = lean_obj_once(&l_Std_Time_WallTime_subSeconds___closed__0, &l_Std_Time_WallTime_subSeconds___closed__0_once, _init_l_Std_Time_WallTime_subSeconds___closed__0);
v___x_336_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_337_ = lean_int_mul(v_second_332_, v___x_336_);
v_nanos_338_ = lean_int_add(v___x_337_, v_nano_333_);
lean_dec(v___x_337_);
v___x_339_ = lean_int_mul(v___x_334_, v___x_336_);
lean_dec(v___x_334_);
v_nanos_340_ = lean_int_add(v___x_339_, v___x_335_);
lean_dec(v___x_339_);
v___x_341_ = lean_int_add(v_nanos_338_, v_nanos_340_);
lean_dec(v_nanos_340_);
lean_dec(v_nanos_338_);
v___x_342_ = l_Std_Time_Duration_ofNanoseconds(v___x_341_);
lean_dec(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subSeconds___boxed(lean_object* v_t_343_, lean_object* v_s_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Time_WallTime_subSeconds(v_t_343_, v_s_344_);
lean_dec(v_s_344_);
lean_dec_ref(v_t_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMinutes(lean_object* v_t_346_, lean_object* v_m_347_){
_start:
{
lean_object* v_second_348_; lean_object* v_nano_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_nanos_355_; lean_object* v___x_356_; lean_object* v_nanos_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_second_348_ = lean_ctor_get(v_t_346_, 0);
v_nano_349_ = lean_ctor_get(v_t_346_, 1);
v___x_350_ = lean_obj_once(&l_Std_Time_WallTime_toMinutes___closed__0, &l_Std_Time_WallTime_toMinutes___closed__0_once, _init_l_Std_Time_WallTime_toMinutes___closed__0);
v___x_351_ = lean_int_mul(v_m_347_, v___x_350_);
v___x_352_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_353_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_354_ = lean_int_mul(v_second_348_, v___x_353_);
v_nanos_355_ = lean_int_add(v___x_354_, v_nano_349_);
lean_dec(v___x_354_);
v___x_356_ = lean_int_mul(v___x_351_, v___x_353_);
lean_dec(v___x_351_);
v_nanos_357_ = lean_int_add(v___x_356_, v___x_352_);
lean_dec(v___x_356_);
v___x_358_ = lean_int_add(v_nanos_355_, v_nanos_357_);
lean_dec(v_nanos_357_);
lean_dec(v_nanos_355_);
v___x_359_ = l_Std_Time_Duration_ofNanoseconds(v___x_358_);
lean_dec(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addMinutes___boxed(lean_object* v_t_360_, lean_object* v_m_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_Time_WallTime_addMinutes(v_t_360_, v_m_361_);
lean_dec(v_m_361_);
lean_dec_ref(v_t_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMinutes(lean_object* v_t_363_, lean_object* v_m_364_){
_start:
{
lean_object* v_second_365_; lean_object* v_nano_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v_nanos_373_; lean_object* v___x_374_; lean_object* v_nanos_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_second_365_ = lean_ctor_get(v_t_363_, 0);
v_nano_366_ = lean_ctor_get(v_t_363_, 1);
v___x_367_ = lean_obj_once(&l_Std_Time_WallTime_toMinutes___closed__0, &l_Std_Time_WallTime_toMinutes___closed__0_once, _init_l_Std_Time_WallTime_toMinutes___closed__0);
v___x_368_ = lean_int_mul(v_m_364_, v___x_367_);
v___x_369_ = lean_int_neg(v___x_368_);
lean_dec(v___x_368_);
v___x_370_ = lean_obj_once(&l_Std_Time_WallTime_subSeconds___closed__0, &l_Std_Time_WallTime_subSeconds___closed__0_once, _init_l_Std_Time_WallTime_subSeconds___closed__0);
v___x_371_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_372_ = lean_int_mul(v_second_365_, v___x_371_);
v_nanos_373_ = lean_int_add(v___x_372_, v_nano_366_);
lean_dec(v___x_372_);
v___x_374_ = lean_int_mul(v___x_369_, v___x_371_);
lean_dec(v___x_369_);
v_nanos_375_ = lean_int_add(v___x_374_, v___x_370_);
lean_dec(v___x_374_);
v___x_376_ = lean_int_add(v_nanos_373_, v_nanos_375_);
lean_dec(v_nanos_375_);
lean_dec(v_nanos_373_);
v___x_377_ = l_Std_Time_Duration_ofNanoseconds(v___x_376_);
lean_dec(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subMinutes___boxed(lean_object* v_t_378_, lean_object* v_m_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Time_WallTime_subMinutes(v_t_378_, v_m_379_);
lean_dec(v_m_379_);
lean_dec_ref(v_t_378_);
return v_res_380_;
}
}
static lean_object* _init_l_Std_Time_WallTime_addHours___closed__0(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(3600u);
v___x_382_ = lean_nat_to_int(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addHours(lean_object* v_t_383_, lean_object* v_h_384_){
_start:
{
lean_object* v_second_385_; lean_object* v_nano_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_nanos_392_; lean_object* v___x_393_; lean_object* v_nanos_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_second_385_ = lean_ctor_get(v_t_383_, 0);
v_nano_386_ = lean_ctor_get(v_t_383_, 1);
v___x_387_ = lean_obj_once(&l_Std_Time_WallTime_addHours___closed__0, &l_Std_Time_WallTime_addHours___closed__0_once, _init_l_Std_Time_WallTime_addHours___closed__0);
v___x_388_ = lean_int_mul(v_h_384_, v___x_387_);
v___x_389_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_390_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_391_ = lean_int_mul(v_second_385_, v___x_390_);
v_nanos_392_ = lean_int_add(v___x_391_, v_nano_386_);
lean_dec(v___x_391_);
v___x_393_ = lean_int_mul(v___x_388_, v___x_390_);
lean_dec(v___x_388_);
v_nanos_394_ = lean_int_add(v___x_393_, v___x_389_);
lean_dec(v___x_393_);
v___x_395_ = lean_int_add(v_nanos_392_, v_nanos_394_);
lean_dec(v_nanos_394_);
lean_dec(v_nanos_392_);
v___x_396_ = l_Std_Time_Duration_ofNanoseconds(v___x_395_);
lean_dec(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addHours___boxed(lean_object* v_t_397_, lean_object* v_h_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_Time_WallTime_addHours(v_t_397_, v_h_398_);
lean_dec(v_h_398_);
lean_dec_ref(v_t_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subHours(lean_object* v_t_400_, lean_object* v_h_401_){
_start:
{
lean_object* v_second_402_; lean_object* v_nano_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_nanos_410_; lean_object* v___x_411_; lean_object* v_nanos_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_second_402_ = lean_ctor_get(v_t_400_, 0);
v_nano_403_ = lean_ctor_get(v_t_400_, 1);
v___x_404_ = lean_obj_once(&l_Std_Time_WallTime_addHours___closed__0, &l_Std_Time_WallTime_addHours___closed__0_once, _init_l_Std_Time_WallTime_addHours___closed__0);
v___x_405_ = lean_int_mul(v_h_401_, v___x_404_);
v___x_406_ = lean_int_neg(v___x_405_);
lean_dec(v___x_405_);
v___x_407_ = lean_obj_once(&l_Std_Time_WallTime_subSeconds___closed__0, &l_Std_Time_WallTime_subSeconds___closed__0_once, _init_l_Std_Time_WallTime_subSeconds___closed__0);
v___x_408_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_409_ = lean_int_mul(v_second_402_, v___x_408_);
v_nanos_410_ = lean_int_add(v___x_409_, v_nano_403_);
lean_dec(v___x_409_);
v___x_411_ = lean_int_mul(v___x_406_, v___x_408_);
lean_dec(v___x_406_);
v_nanos_412_ = lean_int_add(v___x_411_, v___x_407_);
lean_dec(v___x_411_);
v___x_413_ = lean_int_add(v_nanos_410_, v_nanos_412_);
lean_dec(v_nanos_412_);
lean_dec(v_nanos_410_);
v___x_414_ = l_Std_Time_Duration_ofNanoseconds(v___x_413_);
lean_dec(v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subHours___boxed(lean_object* v_t_415_, lean_object* v_h_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_Time_WallTime_subHours(v_t_415_, v_h_416_);
lean_dec(v_h_416_);
lean_dec_ref(v_t_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDays(lean_object* v_t_418_, lean_object* v_d_419_){
_start:
{
lean_object* v_second_420_; lean_object* v_nano_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_nanos_427_; lean_object* v___x_428_; lean_object* v_nanos_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_second_420_ = lean_ctor_get(v_t_418_, 0);
v_nano_421_ = lean_ctor_get(v_t_418_, 1);
v___x_422_ = lean_obj_once(&l_Std_Time_WallTime_toDays___closed__0, &l_Std_Time_WallTime_toDays___closed__0_once, _init_l_Std_Time_WallTime_toDays___closed__0);
v___x_423_ = lean_int_mul(v_d_419_, v___x_422_);
v___x_424_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_425_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_426_ = lean_int_mul(v_second_420_, v___x_425_);
v_nanos_427_ = lean_int_add(v___x_426_, v_nano_421_);
lean_dec(v___x_426_);
v___x_428_ = lean_int_mul(v___x_423_, v___x_425_);
lean_dec(v___x_423_);
v_nanos_429_ = lean_int_add(v___x_428_, v___x_424_);
lean_dec(v___x_428_);
v___x_430_ = lean_int_add(v_nanos_427_, v_nanos_429_);
lean_dec(v_nanos_429_);
lean_dec(v_nanos_427_);
v___x_431_ = l_Std_Time_Duration_ofNanoseconds(v___x_430_);
lean_dec(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDays___boxed(lean_object* v_t_432_, lean_object* v_d_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_Time_WallTime_addDays(v_t_432_, v_d_433_);
lean_dec(v_d_433_);
lean_dec_ref(v_t_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDays(lean_object* v_t_435_, lean_object* v_d_436_){
_start:
{
lean_object* v_second_437_; lean_object* v_nano_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v_nanos_445_; lean_object* v___x_446_; lean_object* v_nanos_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_second_437_ = lean_ctor_get(v_t_435_, 0);
v_nano_438_ = lean_ctor_get(v_t_435_, 1);
v___x_439_ = lean_obj_once(&l_Std_Time_WallTime_toDays___closed__0, &l_Std_Time_WallTime_toDays___closed__0_once, _init_l_Std_Time_WallTime_toDays___closed__0);
v___x_440_ = lean_int_mul(v_d_436_, v___x_439_);
v___x_441_ = lean_int_neg(v___x_440_);
lean_dec(v___x_440_);
v___x_442_ = lean_obj_once(&l_Std_Time_WallTime_subSeconds___closed__0, &l_Std_Time_WallTime_subSeconds___closed__0_once, _init_l_Std_Time_WallTime_subSeconds___closed__0);
v___x_443_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_444_ = lean_int_mul(v_second_437_, v___x_443_);
v_nanos_445_ = lean_int_add(v___x_444_, v_nano_438_);
lean_dec(v___x_444_);
v___x_446_ = lean_int_mul(v___x_441_, v___x_443_);
lean_dec(v___x_441_);
v_nanos_447_ = lean_int_add(v___x_446_, v___x_442_);
lean_dec(v___x_446_);
v___x_448_ = lean_int_add(v_nanos_445_, v_nanos_447_);
lean_dec(v_nanos_447_);
lean_dec(v_nanos_445_);
v___x_449_ = l_Std_Time_Duration_ofNanoseconds(v___x_448_);
lean_dec(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDays___boxed(lean_object* v_t_450_, lean_object* v_d_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_Time_WallTime_subDays(v_t_450_, v_d_451_);
lean_dec(v_d_451_);
lean_dec_ref(v_t_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addWeeks(lean_object* v_t_453_, lean_object* v_d_454_){
_start:
{
lean_object* v_second_455_; lean_object* v_nano_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_nanos_464_; lean_object* v___x_465_; lean_object* v_nanos_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_second_455_ = lean_ctor_get(v_t_453_, 0);
v_nano_456_ = lean_ctor_get(v_t_453_, 1);
v___x_457_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__7, &l_Std_Time_instReprWallTime_repr___redArg___closed__7_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7);
v___x_458_ = lean_int_mul(v_d_454_, v___x_457_);
v___x_459_ = lean_obj_once(&l_Std_Time_WallTime_toDays___closed__0, &l_Std_Time_WallTime_toDays___closed__0_once, _init_l_Std_Time_WallTime_toDays___closed__0);
v___x_460_ = lean_int_mul(v___x_458_, v___x_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_462_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_463_ = lean_int_mul(v_second_455_, v___x_462_);
v_nanos_464_ = lean_int_add(v___x_463_, v_nano_456_);
lean_dec(v___x_463_);
v___x_465_ = lean_int_mul(v___x_460_, v___x_462_);
lean_dec(v___x_460_);
v_nanos_466_ = lean_int_add(v___x_465_, v___x_461_);
lean_dec(v___x_465_);
v___x_467_ = lean_int_add(v_nanos_464_, v_nanos_466_);
lean_dec(v_nanos_466_);
lean_dec(v_nanos_464_);
v___x_468_ = l_Std_Time_Duration_ofNanoseconds(v___x_467_);
lean_dec(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addWeeks___boxed(lean_object* v_t_469_, lean_object* v_d_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Std_Time_WallTime_addWeeks(v_t_469_, v_d_470_);
lean_dec(v_d_470_);
lean_dec_ref(v_t_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subWeeks(lean_object* v_t_472_, lean_object* v_d_473_){
_start:
{
lean_object* v_second_474_; lean_object* v_nano_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v_nanos_484_; lean_object* v___x_485_; lean_object* v_nanos_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_second_474_ = lean_ctor_get(v_t_472_, 0);
v_nano_475_ = lean_ctor_get(v_t_472_, 1);
v___x_476_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__7, &l_Std_Time_instReprWallTime_repr___redArg___closed__7_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__7);
v___x_477_ = lean_int_mul(v_d_473_, v___x_476_);
v___x_478_ = lean_obj_once(&l_Std_Time_WallTime_toDays___closed__0, &l_Std_Time_WallTime_toDays___closed__0_once, _init_l_Std_Time_WallTime_toDays___closed__0);
v___x_479_ = lean_int_mul(v___x_477_, v___x_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_int_neg(v___x_479_);
lean_dec(v___x_479_);
v___x_481_ = lean_obj_once(&l_Std_Time_WallTime_subSeconds___closed__0, &l_Std_Time_WallTime_subSeconds___closed__0_once, _init_l_Std_Time_WallTime_subSeconds___closed__0);
v___x_482_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_483_ = lean_int_mul(v_second_474_, v___x_482_);
v_nanos_484_ = lean_int_add(v___x_483_, v_nano_475_);
lean_dec(v___x_483_);
v___x_485_ = lean_int_mul(v___x_480_, v___x_482_);
lean_dec(v___x_480_);
v_nanos_486_ = lean_int_add(v___x_485_, v___x_481_);
lean_dec(v___x_485_);
v___x_487_ = lean_int_add(v_nanos_484_, v_nanos_486_);
lean_dec(v_nanos_486_);
lean_dec(v_nanos_484_);
v___x_488_ = l_Std_Time_Duration_ofNanoseconds(v___x_487_);
lean_dec(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subWeeks___boxed(lean_object* v_t_489_, lean_object* v_d_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_Time_WallTime_subWeeks(v_t_489_, v_d_490_);
lean_dec(v_d_490_);
lean_dec_ref(v_t_489_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDuration(lean_object* v_t_492_, lean_object* v_d_493_){
_start:
{
lean_object* v_second_494_; lean_object* v_nano_495_; lean_object* v_second_496_; lean_object* v_nano_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_nanos_500_; lean_object* v___x_501_; lean_object* v_nanos_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_second_494_ = lean_ctor_get(v_t_492_, 0);
v_nano_495_ = lean_ctor_get(v_t_492_, 1);
v_second_496_ = lean_ctor_get(v_d_493_, 0);
v_nano_497_ = lean_ctor_get(v_d_493_, 1);
v___x_498_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_499_ = lean_int_mul(v_second_494_, v___x_498_);
v_nanos_500_ = lean_int_add(v___x_499_, v_nano_495_);
lean_dec(v___x_499_);
v___x_501_ = lean_int_mul(v_second_496_, v___x_498_);
v_nanos_502_ = lean_int_add(v___x_501_, v_nano_497_);
lean_dec(v___x_501_);
v___x_503_ = lean_int_add(v_nanos_500_, v_nanos_502_);
lean_dec(v_nanos_502_);
lean_dec(v_nanos_500_);
v___x_504_ = l_Std_Time_Duration_ofNanoseconds(v___x_503_);
lean_dec(v___x_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_addDuration___boxed(lean_object* v_t_505_, lean_object* v_d_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_Time_WallTime_addDuration(v_t_505_, v_d_506_);
lean_dec_ref(v_d_506_);
lean_dec_ref(v_t_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDuration(lean_object* v_t_508_, lean_object* v_d_509_){
_start:
{
lean_object* v_second_510_; lean_object* v_nano_511_; lean_object* v_second_512_; lean_object* v_nano_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_nanos_518_; lean_object* v___x_519_; lean_object* v_nanos_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_second_510_ = lean_ctor_get(v_d_509_, 0);
v_nano_511_ = lean_ctor_get(v_d_509_, 1);
v_second_512_ = lean_ctor_get(v_t_508_, 0);
v_nano_513_ = lean_ctor_get(v_t_508_, 1);
v___x_514_ = lean_int_neg(v_second_510_);
v___x_515_ = lean_int_neg(v_nano_511_);
v___x_516_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_517_ = lean_int_mul(v_second_512_, v___x_516_);
v_nanos_518_ = lean_int_add(v___x_517_, v_nano_513_);
lean_dec(v___x_517_);
v___x_519_ = lean_int_mul(v___x_514_, v___x_516_);
lean_dec(v___x_514_);
v_nanos_520_ = lean_int_add(v___x_519_, v___x_515_);
lean_dec(v___x_515_);
lean_dec(v___x_519_);
v___x_521_ = lean_int_add(v_nanos_518_, v_nanos_520_);
lean_dec(v_nanos_520_);
lean_dec(v_nanos_518_);
v___x_522_ = l_Std_Time_Duration_ofNanoseconds(v___x_521_);
lean_dec(v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_subDuration___boxed(lean_object* v_t_523_, lean_object* v_d_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_Time_WallTime_subDuration(v_t_523_, v_d_524_);
lean_dec_ref(v_d_524_);
lean_dec_ref(v_t_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDuration(lean_object* v_wt_526_){
_start:
{
lean_inc_ref(v_wt_526_);
return v_wt_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toDuration___boxed(lean_object* v_wt_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Time_WallTime_toDuration(v_wt_527_);
lean_dec_ref(v_wt_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_instHSubDuration__1___lam__0(lean_object* v_x_561_, lean_object* v_y_562_){
_start:
{
lean_object* v_second_563_; lean_object* v_nano_564_; lean_object* v_second_565_; lean_object* v_nano_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_nanos_571_; lean_object* v___x_572_; lean_object* v_nanos_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_second_563_ = lean_ctor_get(v_y_562_, 0);
v_nano_564_ = lean_ctor_get(v_y_562_, 1);
v_second_565_ = lean_ctor_get(v_x_561_, 0);
v_nano_566_ = lean_ctor_get(v_x_561_, 1);
v___x_567_ = lean_int_neg(v_second_563_);
v___x_568_ = lean_int_neg(v_nano_564_);
v___x_569_ = lean_obj_once(&l_Std_Time_instReprWallTime__1___lam__0___closed__2, &l_Std_Time_instReprWallTime__1___lam__0___closed__2_once, _init_l_Std_Time_instReprWallTime__1___lam__0___closed__2);
v___x_570_ = lean_int_mul(v_second_565_, v___x_569_);
v_nanos_571_ = lean_int_add(v___x_570_, v_nano_566_);
lean_dec(v___x_570_);
v___x_572_ = lean_int_mul(v___x_567_, v___x_569_);
lean_dec(v___x_567_);
v_nanos_573_ = lean_int_add(v___x_572_, v___x_568_);
lean_dec(v___x_568_);
lean_dec(v___x_572_);
v___x_574_ = lean_int_add(v_nanos_571_, v_nanos_573_);
lean_dec(v_nanos_573_);
lean_dec(v_nanos_571_);
v___x_575_ = l_Std_Time_Duration_ofNanoseconds(v___x_574_);
lean_dec(v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_instHSubDuration__1___lam__0___boxed(lean_object* v_x_576_, lean_object* v_y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Std_Time_WallTime_instHSubDuration__1___lam__0(v_x_576_, v_y_577_);
lean_dec_ref(v_y_577_);
lean_dec_ref(v_x_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_instOfNat(lean_object* v_n_581_){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = lean_nat_to_int(v_n_581_);
v___x_583_ = lean_obj_once(&l_Std_Time_instReprWallTime_repr___redArg___closed__14, &l_Std_Time_instReprWallTime_repr___redArg___closed__14_once, _init_l_Std_Time_instReprWallTime_repr___redArg___closed__14);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
return v___x_584_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Duration(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_DateTime_WallTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

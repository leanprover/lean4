// Lean compiler output
// Module: Std.Time.DateTime.Timestamp
// Imports: public import Init.System.IO public import Std.Time.Duration public import Std.Time.DateTime.WallTime
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
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
uint8_t l_Std_Time_Duration_instDecidableLt(lean_object*, lean_object*);
lean_object* l_Std_Time_Nanosecond_instReprOrdinal___lam__0(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l_Std_Time_instDecidableEqDuration_decEq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Int_repr(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_Time_instToStringDuration_leftPad(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
uint8_t l_Std_Time_Duration_instDecidableLe(lean_object*, lean_object*);
extern lean_object* l_Std_Time_instOrdDuration;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprTimestamp_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_instReprTimestamp_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_instReprTimestamp_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprTimestamp_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprTimestamp_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_instReprTimestamp_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprTimestamp_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_instReprTimestamp_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_instReprTimestamp_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__8_value;
static const lean_string_object l_Std_Time_instReprTimestamp_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__9_value;
static lean_once_cell_t l_Std_Time_instReprTimestamp_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__10;
static lean_once_cell_t l_Std_Time_instReprTimestamp_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__11;
static const lean_ctor_object l_Std_Time_instReprTimestamp_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Time_instReprTimestamp_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__9_value)}};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__13_value;
static lean_once_cell_t l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__14;
static const lean_string_object l_Std_Time_instReprTimestamp_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__15 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__15_value;
static const lean_string_object l_Std_Time_instReprTimestamp_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__16_value;
static const lean_string_object l_Std_Time_instReprTimestamp_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__17 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprTimestamp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprTimestamp_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprTimestamp___closed__0 = (const lean_object*)&l_Std_Time_instReprTimestamp___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprTimestamp = (const lean_object*)&l_Std_Time_instReprTimestamp___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimestamp_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimestamp_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimestamp___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_instInhabitedTimestamp_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedTimestamp_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedTimestamp_default;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedTimestamp_default_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedTimestamp;
LEAN_EXPORT lean_object* l_Std_Time_instLETimestamp;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLeTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instLTTimestamp;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLtTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_instToStringTimestamp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instToStringTimestamp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instToStringTimestamp___closed__0 = (const lean_object*)&l_Std_Time_instToStringTimestamp___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instToStringTimestamp = (const lean_object*)&l_Std_Time_instToStringTimestamp___closed__0_value;
static const lean_string_object l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Timestamp.ofNanoseconds "};
static const lean_object* l_Std_Time_instReprTimestamp__1___lam__0___closed__0 = (const lean_object*)&l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprTimestamp__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value)}};
static const lean_object* l_Std_Time_instReprTimestamp__1___lam__0___closed__1 = (const lean_object*)&l_Std_Time_instReprTimestamp__1___lam__0___closed__1_value;
static lean_once_cell_t l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimestamp__1___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprTimestamp__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprTimestamp__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprTimestamp__1___closed__0 = (const lean_object*)&l_Std_Time_instReprTimestamp__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprTimestamp__1 = (const lean_object*)&l_Std_Time_instReprTimestamp__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_instOrdTimestamp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instOrdTimestamp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instOrdTimestamp___closed__0 = (const lean_object*)&l_Std_Time_instOrdTimestamp___closed__0_value;
static lean_once_cell_t l_Std_Time_instOrdTimestamp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instOrdTimestamp___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp;
lean_object* lean_get_current_time();
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_now___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutesSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDaysSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDaysSinceUnixEpoch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofSecondsSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofDurationSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofDurationSinceUnixEpoch___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_subSeconds___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_subSeconds___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_addHours___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_addHours___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Timestamp_instHAddDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_addDuration___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHAddDuration___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHAddDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHAddDuration = (const lean_object*)&l_Std_Time_Timestamp_instHAddDuration___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHSubDuration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_subDuration___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHSubDuration___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHSubDuration___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHSubDuration = (const lean_object*)&l_Std_Time_Timestamp_instHSubDuration___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHAddOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_addDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHAddOffset___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHAddOffset = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHSubOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_subDays___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHSubOffset___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHSubOffset = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHAddOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_addWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHAddOffset__1___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHAddOffset__1 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHSubOffset__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_subWeeks___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHSubOffset__1___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHSubOffset__1 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__1___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHAddOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_addHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHAddOffset__2___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHAddOffset__2 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHSubOffset__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_subHours___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHSubOffset__2___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__2___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHSubOffset__2 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__2___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHAddOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_addMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHAddOffset__3___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHAddOffset__3 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHSubOffset__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_subMinutes___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHSubOffset__3___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__3___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHSubOffset__3 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__3___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHAddOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_addSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHAddOffset__4___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHAddOffset__4 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHSubOffset__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_subSeconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHSubOffset__4___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__4___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHSubOffset__4 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__4___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHAddOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_addMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHAddOffset__5___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHAddOffset__5 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHSubOffset__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_subMilliseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHSubOffset__5___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__5___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHSubOffset__5 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__5___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHAddOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_addNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHAddOffset__6___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHAddOffset__6 = (const lean_object*)&l_Std_Time_Timestamp_instHAddOffset__6___closed__0_value;
static const lean_closure_object l_Std_Time_Timestamp_instHSubOffset__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_subNanoseconds___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHSubOffset__6___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__6___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHSubOffset__6 = (const lean_object*)&l_Std_Time_Timestamp_instHSubOffset__6___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_Timestamp_instHSubDuration__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_Timestamp_instHSubDuration__1___closed__0 = (const lean_object*)&l_Std_Time_Timestamp_instHSubDuration__1___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_Timestamp_instHSubDuration__1 = (const lean_object*)&l_Std_Time_Timestamp_instHSubDuration__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instReprTimestamp_repr_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(7u);
v___x_17_ = lean_nat_to_int(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__0));
v___x_21_ = lean_string_length(v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__10, &l_Std_Time_instReprTimestamp_repr___redArg___closed__10_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__10);
v___x_23_ = lean_nat_to_int(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v___x_29_ = lean_nat_to_int(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp_repr___redArg(lean_object* v_x_33_){
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
v___x_39_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__6));
v___x_40_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_76_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
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
v___x_80_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__16));
lean_inc(v_nano_35_);
v_fst_63_ = v___x_80_;
v_fst_64_ = v_second_34_;
v_snd_65_ = v_nano_35_;
goto v___jp_62_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_81_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__17));
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
v___x_84_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__17));
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
v___x_87_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__16));
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
v___x_45_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__8));
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
v___x_54_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__11, &l_Std_Time_instReprTimestamp_repr___redArg___closed__11_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__11);
v___x_55_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__12));
v___x_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
lean_ctor_set(v___x_56_, 1, v___x_53_);
v___x_57_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__13));
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
v___x_68_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_69_ = lean_int_dec_eq(v_nano_35_, v___x_68_);
lean_dec(v_nano_35_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_70_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__15));
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
v___x_75_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__16));
v___y_42_ = v___x_67_;
v___y_43_ = v___x_75_;
goto v___jp_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp_repr(lean_object* v_x_89_, lean_object* v_prec_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Std_Time_instReprTimestamp_repr___redArg(v_x_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp_repr___boxed(lean_object* v_x_92_, lean_object* v_prec_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Time_instReprTimestamp_repr(v_x_92_, v_prec_93_);
lean_dec(v_prec_93_);
return v_res_94_;
}
}
uint8_t l_Std_Time_instDecidableEqTimestamp_decEq(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_97_, v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqTimestamp_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_97_ = stack[0].m_obj;
lean_object* v_x_98_ = stack[1].m_obj;
uint8_t v_res_100_;
v_res_100_ = l_Std_Time_instDecidableEqTimestamp_decEq(v_x_97_, v_x_98_);
stack->m_num = v_res_100_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimestamp_decEq___boxed(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Std_Time_instDecidableEqTimestamp_decEq(v_x_101_, v_x_102_);
lean_dec_ref(v_x_102_);
lean_dec_ref(v_x_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
uint8_t l_Std_Time_instDecidableEqTimestamp(lean_object* v_x_105_, lean_object* v_x_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_105_, v_x_106_);
return v___x_107_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqTimestamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_105_ = stack[0].m_obj;
lean_object* v_x_106_ = stack[1].m_obj;
uint8_t v_res_108_;
v_res_108_ = l_Std_Time_instDecidableEqTimestamp(v_x_105_, v_x_106_);
stack->m_num = v_res_108_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimestamp___boxed(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Std_Time_instDecidableEqTimestamp(v_x_109_, v_x_110_);
lean_dec_ref(v_x_110_);
lean_dec_ref(v_x_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimestamp_default___closed__0(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimestamp_default(void){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Std_Time_instInhabitedTimestamp_default___closed__0, &l_Std_Time_instInhabitedTimestamp_default___closed__0_once, _init_l_Std_Time_instInhabitedTimestamp_default___closed__0);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedTimestamp_default_spec__0(lean_object* v_a_116_){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_nat_to_int(v_a_116_);
v___x_118_ = l_Rat_ofInt(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimestamp(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Std_Time_instInhabitedTimestamp_default;
return v___x_119_;
}
}
static lean_object* _init_l_Std_Time_instLETimestamp(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = lean_box(0);
return v___x_120_;
}
}
uint8_t l_Std_Time_instDecidableLeTimestamp(lean_object* v_x_121_, lean_object* v_y_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = l_Std_Time_Duration_instDecidableLe(v_x_121_, v_y_122_);
return v___x_123_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableLeTimestamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_121_ = stack[0].m_obj;
lean_object* v_y_122_ = stack[1].m_obj;
uint8_t v_res_124_;
v_res_124_ = l_Std_Time_instDecidableLeTimestamp(v_x_121_, v_y_122_);
stack->m_num = v_res_124_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeTimestamp___boxed(lean_object* v_x_125_, lean_object* v_y_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Std_Time_instDecidableLeTimestamp(v_x_125_, v_y_126_);
lean_dec_ref(v_y_126_);
lean_dec_ref(v_x_125_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
static lean_object* _init_l_Std_Time_instLTTimestamp(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_box(0);
return v___x_129_;
}
}
uint8_t l_Std_Time_instDecidableLtTimestamp(lean_object* v_x_130_, lean_object* v_y_131_){
_start:
{
uint8_t v___x_132_; 
v___x_132_ = l_Std_Time_Duration_instDecidableLt(v_x_130_, v_y_131_);
return v___x_132_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableLtTimestamp_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_130_ = stack[0].m_obj;
lean_object* v_y_131_ = stack[1].m_obj;
uint8_t v_res_133_;
v_res_133_ = l_Std_Time_instDecidableLtTimestamp(v_x_130_, v_y_131_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtTimestamp___boxed(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Std_Time_instDecidableLtTimestamp(v_x_134_, v_y_135_);
lean_dec_ref(v_y_135_);
lean_dec_ref(v_x_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0(lean_object* v_s_138_){
_start:
{
lean_object* v_second_139_; lean_object* v___x_140_; 
v_second_139_ = lean_ctor_get(v_s_138_, 0);
v___x_140_ = l_Int_repr(v_second_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0___boxed(lean_object* v_s_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_Time_instToStringTimestamp___lam__0(v_s_141_);
lean_dec_ref(v_s_141_);
return v_res_142_;
}
}
static lean_object* _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = lean_unsigned_to_nat(1000000000u);
v___x_149_ = lean_nat_to_int(v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp__1___lam__0(lean_object* v_s_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_second_152_; lean_object* v_nano_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_167_; 
v_second_152_ = lean_ctor_get(v_s_150_, 0);
v_nano_153_ = lean_ctor_get(v_s_150_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_s_150_);
if (v_isSharedCheck_167_ == 0)
{
v___x_155_ = v_s_150_;
v_isShared_156_ = v_isSharedCheck_167_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_nano_153_);
lean_inc(v_second_152_);
lean_dec(v_s_150_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_167_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_nanos_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_157_ = ((lean_object*)(l_Std_Time_instReprTimestamp__1___lam__0___closed__1));
v___x_158_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_159_ = lean_int_mul(v_second_152_, v___x_158_);
lean_dec(v_second_152_);
v_nanos_160_ = lean_int_add(v___x_159_, v_nano_153_);
lean_dec(v_nano_153_);
lean_dec(v___x_159_);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanos_160_, v___x_161_);
lean_dec(v_nanos_160_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 5);
lean_ctor_set(v___x_155_, 1, v___x_162_);
lean_ctor_set(v___x_155_, 0, v___x_157_);
v___x_164_ = v___x_155_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_166_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; 
v___x_165_ = l_Repr_addAppParen(v___x_164_, v___y_151_);
return v___x_165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp__1___lam__0___boxed(lean_object* v_s_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Std_Time_instReprTimestamp__1___lam__0(v_s_168_, v___y_169_);
lean_dec(v___y_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp___lam__0(lean_object* v_x_173_){
_start:
{
lean_inc_ref(v_x_173_);
return v_x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp___lam__0___boxed(lean_object* v_x_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_Time_instOrdTimestamp___lam__0(v_x_174_);
lean_dec_ref(v_x_174_);
return v_res_175_;
}
}
static lean_object* _init_l_Std_Time_instOrdTimestamp___closed__1(void){
_start:
{
lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___f_177_ = ((lean_object*)(l_Std_Time_instOrdTimestamp___closed__0));
v___x_178_ = l_Std_Time_instOrdDuration;
v___x_179_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_179_, 0, lean_box(0));
lean_closure_set(v___x_179_, 1, lean_box(0));
lean_closure_set(v___x_179_, 2, v___x_178_);
lean_closure_set(v___x_179_, 3, v___f_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_Time_instOrdTimestamp(void){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_obj_once(&l_Std_Time_instOrdTimestamp___closed__1, &l_Std_Time_instOrdTimestamp___closed__1_once, _init_l_Std_Time_instOrdTimestamp___closed__1);
return v___x_180_;
}
}
LEAN_EXPORT void l_Std_Time_Timestamp_now_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_182_;
v_res_182_ = lean_get_current_time();
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_now___boxed(lean_object* v_a_00___x40___internal___hyg_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = lean_get_current_time();
return v_res_184_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(60u);
v___x_186_ = lean_nat_to_int(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutesSinceUnixEpoch(lean_object* v_tm_187_){
_start:
{
lean_object* v_second_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_second_188_ = lean_ctor_get(v_tm_187_, 0);
v___x_189_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0);
v___x_190_ = lean_int_div(v_second_188_, v___x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___boxed(lean_object* v_tm_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_Time_Timestamp_toMinutesSinceUnixEpoch(v_tm_191_);
lean_dec_ref(v_tm_191_);
return v_res_192_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_unsigned_to_nat(86400u);
v___x_194_ = lean_nat_to_int(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDaysSinceUnixEpoch(lean_object* v_tm_195_){
_start:
{
lean_object* v_second_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_second_196_ = lean_ctor_get(v_tm_195_, 0);
v___x_197_ = lean_obj_once(&l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0);
v___x_198_ = lean_int_div(v_second_196_, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDaysSinceUnixEpoch___boxed(lean_object* v_tm_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Std_Time_Timestamp_toDaysSinceUnixEpoch(v_tm_199_);
lean_dec_ref(v_tm_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofSecondsSinceUnixEpoch(lean_object* v_secs_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v_secs_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(lean_object* v_nanos_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch___boxed(lean_object* v_nanos_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(v_nanos_206_);
lean_dec(v_nanos_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofDurationSinceUnixEpoch(lean_object* v_duration_208_){
_start:
{
lean_inc_ref(v_duration_208_);
return v_duration_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofDurationSinceUnixEpoch___boxed(lean_object* v_duration_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Std_Time_Timestamp_ofDurationSinceUnixEpoch(v_duration_209_);
lean_dec_ref(v_duration_209_);
return v_res_210_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(1000000u);
v___x_212_ = lean_nat_to_int(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(lean_object* v_milli_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_214_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_215_ = lean_int_mul(v_milli_213_, v___x_214_);
v___x_216_ = l_Std_Time_Duration_ofNanoseconds(v___x_215_);
lean_dec(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___boxed(lean_object* v_milli_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(v_milli_217_);
lean_dec(v_milli_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(lean_object* v_t_219_){
_start:
{
lean_object* v_second_220_; 
v_second_220_ = lean_ctor_get(v_t_219_, 0);
lean_inc(v_second_220_);
return v_second_220_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch___boxed(lean_object* v_t_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(v_t_221_);
lean_dec_ref(v_t_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(lean_object* v_tm_223_){
_start:
{
lean_object* v_second_224_; lean_object* v_nano_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v_nanos_228_; 
v_second_224_ = lean_ctor_get(v_tm_223_, 0);
v_nano_225_ = lean_ctor_get(v_tm_223_, 1);
v___x_226_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_227_ = lean_int_mul(v_second_224_, v___x_226_);
v_nanos_228_ = lean_int_add(v___x_227_, v_nano_225_);
lean_dec(v___x_227_);
return v_nanos_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch___boxed(lean_object* v_tm_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(v_tm_229_);
lean_dec_ref(v_tm_229_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(lean_object* v_tm_231_){
_start:
{
lean_object* v_second_232_; lean_object* v_nano_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_second_232_ = lean_ctor_get(v_tm_231_, 0);
v_nano_233_ = lean_ctor_get(v_tm_231_, 1);
v___x_234_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_235_ = lean_int_mul(v_second_232_, v___x_234_);
v___x_236_ = lean_int_add(v___x_235_, v_nano_233_);
lean_dec(v___x_235_);
v___x_237_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_238_ = lean_int_div(v___x_236_, v___x_237_);
lean_dec(v___x_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch___boxed(lean_object* v_tm_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(v_tm_239_);
lean_dec_ref(v_tm_239_);
return v_res_240_;
}
}
lean_object* l_Std_Time_Timestamp_since(lean_object* v_f_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_get_current_time();
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_264_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_264_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_264_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_264_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_second_248_; lean_object* v_nano_249_; lean_object* v_second_250_; lean_object* v_nano_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_nanos_256_; lean_object* v___x_257_; lean_object* v_nanos_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v_second_248_ = lean_ctor_get(v_f_241_, 0);
v_nano_249_ = lean_ctor_get(v_f_241_, 1);
v_second_250_ = lean_ctor_get(v_a_244_, 0);
lean_inc(v_second_250_);
v_nano_251_ = lean_ctor_get(v_a_244_, 1);
lean_inc(v_nano_251_);
lean_dec(v_a_244_);
v___x_252_ = lean_int_neg(v_second_248_);
v___x_253_ = lean_int_neg(v_nano_249_);
v___x_254_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_255_ = lean_int_mul(v_second_250_, v___x_254_);
lean_dec(v_second_250_);
v_nanos_256_ = lean_int_add(v___x_255_, v_nano_251_);
lean_dec(v_nano_251_);
lean_dec(v___x_255_);
v___x_257_ = lean_int_mul(v___x_252_, v___x_254_);
lean_dec(v___x_252_);
v_nanos_258_ = lean_int_add(v___x_257_, v___x_253_);
lean_dec(v___x_253_);
lean_dec(v___x_257_);
v___x_259_ = lean_int_add(v_nanos_256_, v_nanos_258_);
lean_dec(v_nanos_258_);
lean_dec(v_nanos_256_);
v___x_260_ = l_Std_Time_Duration_ofNanoseconds(v___x_259_);
lean_dec(v___x_259_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_260_);
v___x_262_ = v___x_246_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
v_a_265_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_243_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_243_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_Timestamp_since_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_241_ = stack[0].m_obj;
lean_object* v_res_273_;
v_res_273_ = l_Std_Time_Timestamp_since(v_f_241_);
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since___boxed(lean_object* v_f_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_Time_Timestamp_since(v_f_274_);
lean_dec_ref(v_f_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch(lean_object* v_tm_277_){
_start:
{
lean_inc_ref(v_tm_277_);
return v_tm_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch___boxed(lean_object* v_tm_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Std_Time_Timestamp_toDurationSinceUnixEpoch(v_tm_278_);
lean_dec_ref(v_tm_278_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds(lean_object* v_t_280_, lean_object* v_s_281_){
_start:
{
lean_object* v_second_282_; lean_object* v_nano_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_second_287_; lean_object* v_nano_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v_nanos_291_; lean_object* v___x_292_; lean_object* v_nanos_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_second_282_ = lean_ctor_get(v_t_280_, 0);
v_nano_283_ = lean_ctor_get(v_t_280_, 1);
v___x_284_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_285_ = lean_int_mul(v_s_281_, v___x_284_);
v___x_286_ = l_Std_Time_Duration_ofNanoseconds(v___x_285_);
lean_dec(v___x_285_);
v_second_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_second_287_);
v_nano_288_ = lean_ctor_get(v___x_286_, 1);
lean_inc(v_nano_288_);
lean_dec_ref(v___x_286_);
v___x_289_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_290_ = lean_int_mul(v_second_282_, v___x_289_);
v_nanos_291_ = lean_int_add(v___x_290_, v_nano_283_);
lean_dec(v___x_290_);
v___x_292_ = lean_int_mul(v_second_287_, v___x_289_);
lean_dec(v_second_287_);
v_nanos_293_ = lean_int_add(v___x_292_, v_nano_288_);
lean_dec(v_nano_288_);
lean_dec(v___x_292_);
v___x_294_ = lean_int_add(v_nanos_291_, v_nanos_293_);
lean_dec(v_nanos_293_);
lean_dec(v_nanos_291_);
v___x_295_ = l_Std_Time_Duration_ofNanoseconds(v___x_294_);
lean_dec(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds___boxed(lean_object* v_t_296_, lean_object* v_s_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Std_Time_Timestamp_addMilliseconds(v_t_296_, v_s_297_);
lean_dec(v_s_297_);
lean_dec_ref(v_t_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds(lean_object* v_t_299_, lean_object* v_s_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_second_304_; lean_object* v_nano_305_; lean_object* v_second_306_; lean_object* v_nano_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_nanos_312_; lean_object* v___x_313_; lean_object* v_nanos_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_301_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_302_ = lean_int_mul(v_s_300_, v___x_301_);
v___x_303_ = l_Std_Time_Duration_ofNanoseconds(v___x_302_);
lean_dec(v___x_302_);
v_second_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_second_304_);
v_nano_305_ = lean_ctor_get(v___x_303_, 1);
lean_inc(v_nano_305_);
lean_dec_ref(v___x_303_);
v_second_306_ = lean_ctor_get(v_t_299_, 0);
v_nano_307_ = lean_ctor_get(v_t_299_, 1);
v___x_308_ = lean_int_neg(v_second_304_);
lean_dec(v_second_304_);
v___x_309_ = lean_int_neg(v_nano_305_);
lean_dec(v_nano_305_);
v___x_310_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_311_ = lean_int_mul(v_second_306_, v___x_310_);
v_nanos_312_ = lean_int_add(v___x_311_, v_nano_307_);
lean_dec(v___x_311_);
v___x_313_ = lean_int_mul(v___x_308_, v___x_310_);
lean_dec(v___x_308_);
v_nanos_314_ = lean_int_add(v___x_313_, v___x_309_);
lean_dec(v___x_309_);
lean_dec(v___x_313_);
v___x_315_ = lean_int_add(v_nanos_312_, v_nanos_314_);
lean_dec(v_nanos_314_);
lean_dec(v_nanos_312_);
v___x_316_ = l_Std_Time_Duration_ofNanoseconds(v___x_315_);
lean_dec(v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds___boxed(lean_object* v_t_317_, lean_object* v_s_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_Time_Timestamp_subMilliseconds(v_t_317_, v_s_318_);
lean_dec(v_s_318_);
lean_dec_ref(v_t_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds(lean_object* v_t_320_, lean_object* v_s_321_){
_start:
{
lean_object* v_second_322_; lean_object* v_nano_323_; lean_object* v___x_324_; lean_object* v_second_325_; lean_object* v_nano_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_nanos_329_; lean_object* v___x_330_; lean_object* v_nanos_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v_second_322_ = lean_ctor_get(v_t_320_, 0);
v_nano_323_ = lean_ctor_get(v_t_320_, 1);
v___x_324_ = l_Std_Time_Duration_ofNanoseconds(v_s_321_);
v_second_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_second_325_);
v_nano_326_ = lean_ctor_get(v___x_324_, 1);
lean_inc(v_nano_326_);
lean_dec_ref(v___x_324_);
v___x_327_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_328_ = lean_int_mul(v_second_322_, v___x_327_);
v_nanos_329_ = lean_int_add(v___x_328_, v_nano_323_);
lean_dec(v___x_328_);
v___x_330_ = lean_int_mul(v_second_325_, v___x_327_);
lean_dec(v_second_325_);
v_nanos_331_ = lean_int_add(v___x_330_, v_nano_326_);
lean_dec(v_nano_326_);
lean_dec(v___x_330_);
v___x_332_ = lean_int_add(v_nanos_329_, v_nanos_331_);
lean_dec(v_nanos_331_);
lean_dec(v_nanos_329_);
v___x_333_ = l_Std_Time_Duration_ofNanoseconds(v___x_332_);
lean_dec(v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds___boxed(lean_object* v_t_334_, lean_object* v_s_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_Time_Timestamp_addNanoseconds(v_t_334_, v_s_335_);
lean_dec(v_s_335_);
lean_dec_ref(v_t_334_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds(lean_object* v_t_337_, lean_object* v_s_338_){
_start:
{
lean_object* v___x_339_; lean_object* v_second_340_; lean_object* v_nano_341_; lean_object* v_second_342_; lean_object* v_nano_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_nanos_348_; lean_object* v___x_349_; lean_object* v_nanos_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_339_ = l_Std_Time_Duration_ofNanoseconds(v_s_338_);
v_second_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_second_340_);
v_nano_341_ = lean_ctor_get(v___x_339_, 1);
lean_inc(v_nano_341_);
lean_dec_ref(v___x_339_);
v_second_342_ = lean_ctor_get(v_t_337_, 0);
v_nano_343_ = lean_ctor_get(v_t_337_, 1);
v___x_344_ = lean_int_neg(v_second_340_);
lean_dec(v_second_340_);
v___x_345_ = lean_int_neg(v_nano_341_);
lean_dec(v_nano_341_);
v___x_346_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_347_ = lean_int_mul(v_second_342_, v___x_346_);
v_nanos_348_ = lean_int_add(v___x_347_, v_nano_343_);
lean_dec(v___x_347_);
v___x_349_ = lean_int_mul(v___x_344_, v___x_346_);
lean_dec(v___x_344_);
v_nanos_350_ = lean_int_add(v___x_349_, v___x_345_);
lean_dec(v___x_345_);
lean_dec(v___x_349_);
v___x_351_ = lean_int_add(v_nanos_348_, v_nanos_350_);
lean_dec(v_nanos_350_);
lean_dec(v_nanos_348_);
v___x_352_ = l_Std_Time_Duration_ofNanoseconds(v___x_351_);
lean_dec(v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds___boxed(lean_object* v_t_353_, lean_object* v_s_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Std_Time_Timestamp_subNanoseconds(v_t_353_, v_s_354_);
lean_dec(v_s_354_);
lean_dec_ref(v_t_353_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds(lean_object* v_t_356_, lean_object* v_s_357_){
_start:
{
lean_object* v_second_358_; lean_object* v_nano_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v_nanos_363_; lean_object* v___x_364_; lean_object* v_nanos_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_second_358_ = lean_ctor_get(v_t_356_, 0);
v_nano_359_ = lean_ctor_get(v_t_356_, 1);
v___x_360_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_361_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_362_ = lean_int_mul(v_second_358_, v___x_361_);
v_nanos_363_ = lean_int_add(v___x_362_, v_nano_359_);
lean_dec(v___x_362_);
v___x_364_ = lean_int_mul(v_s_357_, v___x_361_);
v_nanos_365_ = lean_int_add(v___x_364_, v___x_360_);
lean_dec(v___x_364_);
v___x_366_ = lean_int_add(v_nanos_363_, v_nanos_365_);
lean_dec(v_nanos_365_);
lean_dec(v_nanos_363_);
v___x_367_ = l_Std_Time_Duration_ofNanoseconds(v___x_366_);
lean_dec(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds___boxed(lean_object* v_t_368_, lean_object* v_s_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_Time_Timestamp_addSeconds(v_t_368_, v_s_369_);
lean_dec(v_s_369_);
lean_dec_ref(v_t_368_);
return v_res_370_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_subSeconds___closed__0(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_372_ = lean_int_neg(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds(lean_object* v_t_373_, lean_object* v_s_374_){
_start:
{
lean_object* v_second_375_; lean_object* v_nano_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_nanos_381_; lean_object* v___x_382_; lean_object* v_nanos_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_second_375_ = lean_ctor_get(v_t_373_, 0);
v_nano_376_ = lean_ctor_get(v_t_373_, 1);
v___x_377_ = lean_int_neg(v_s_374_);
v___x_378_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_379_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_380_ = lean_int_mul(v_second_375_, v___x_379_);
v_nanos_381_ = lean_int_add(v___x_380_, v_nano_376_);
lean_dec(v___x_380_);
v___x_382_ = lean_int_mul(v___x_377_, v___x_379_);
lean_dec(v___x_377_);
v_nanos_383_ = lean_int_add(v___x_382_, v___x_378_);
lean_dec(v___x_382_);
v___x_384_ = lean_int_add(v_nanos_381_, v_nanos_383_);
lean_dec(v_nanos_383_);
lean_dec(v_nanos_381_);
v___x_385_ = l_Std_Time_Duration_ofNanoseconds(v___x_384_);
lean_dec(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds___boxed(lean_object* v_t_386_, lean_object* v_s_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_Time_Timestamp_subSeconds(v_t_386_, v_s_387_);
lean_dec(v_s_387_);
lean_dec_ref(v_t_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes(lean_object* v_t_389_, lean_object* v_m_390_){
_start:
{
lean_object* v_second_391_; lean_object* v_nano_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_nanos_398_; lean_object* v___x_399_; lean_object* v_nanos_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_second_391_ = lean_ctor_get(v_t_389_, 0);
v_nano_392_ = lean_ctor_get(v_t_389_, 1);
v___x_393_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0);
v___x_394_ = lean_int_mul(v_m_390_, v___x_393_);
v___x_395_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_396_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_397_ = lean_int_mul(v_second_391_, v___x_396_);
v_nanos_398_ = lean_int_add(v___x_397_, v_nano_392_);
lean_dec(v___x_397_);
v___x_399_ = lean_int_mul(v___x_394_, v___x_396_);
lean_dec(v___x_394_);
v_nanos_400_ = lean_int_add(v___x_399_, v___x_395_);
lean_dec(v___x_399_);
v___x_401_ = lean_int_add(v_nanos_398_, v_nanos_400_);
lean_dec(v_nanos_400_);
lean_dec(v_nanos_398_);
v___x_402_ = l_Std_Time_Duration_ofNanoseconds(v___x_401_);
lean_dec(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes___boxed(lean_object* v_t_403_, lean_object* v_m_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_Time_Timestamp_addMinutes(v_t_403_, v_m_404_);
lean_dec(v_m_404_);
lean_dec_ref(v_t_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes(lean_object* v_t_406_, lean_object* v_m_407_){
_start:
{
lean_object* v_second_408_; lean_object* v_nano_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v_nanos_416_; lean_object* v___x_417_; lean_object* v_nanos_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v_second_408_ = lean_ctor_get(v_t_406_, 0);
v_nano_409_ = lean_ctor_get(v_t_406_, 1);
v___x_410_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0);
v___x_411_ = lean_int_mul(v_m_407_, v___x_410_);
v___x_412_ = lean_int_neg(v___x_411_);
lean_dec(v___x_411_);
v___x_413_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_414_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_415_ = lean_int_mul(v_second_408_, v___x_414_);
v_nanos_416_ = lean_int_add(v___x_415_, v_nano_409_);
lean_dec(v___x_415_);
v___x_417_ = lean_int_mul(v___x_412_, v___x_414_);
lean_dec(v___x_412_);
v_nanos_418_ = lean_int_add(v___x_417_, v___x_413_);
lean_dec(v___x_417_);
v___x_419_ = lean_int_add(v_nanos_416_, v_nanos_418_);
lean_dec(v_nanos_418_);
lean_dec(v_nanos_416_);
v___x_420_ = l_Std_Time_Duration_ofNanoseconds(v___x_419_);
lean_dec(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes___boxed(lean_object* v_t_421_, lean_object* v_m_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_Time_Timestamp_subMinutes(v_t_421_, v_m_422_);
lean_dec(v_m_422_);
lean_dec_ref(v_t_421_);
return v_res_423_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_addHours___closed__0(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(3600u);
v___x_425_ = lean_nat_to_int(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours(lean_object* v_t_426_, lean_object* v_h_427_){
_start:
{
lean_object* v_second_428_; lean_object* v_nano_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_nanos_435_; lean_object* v___x_436_; lean_object* v_nanos_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v_second_428_ = lean_ctor_get(v_t_426_, 0);
v_nano_429_ = lean_ctor_get(v_t_426_, 1);
v___x_430_ = lean_obj_once(&l_Std_Time_Timestamp_addHours___closed__0, &l_Std_Time_Timestamp_addHours___closed__0_once, _init_l_Std_Time_Timestamp_addHours___closed__0);
v___x_431_ = lean_int_mul(v_h_427_, v___x_430_);
v___x_432_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_433_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_434_ = lean_int_mul(v_second_428_, v___x_433_);
v_nanos_435_ = lean_int_add(v___x_434_, v_nano_429_);
lean_dec(v___x_434_);
v___x_436_ = lean_int_mul(v___x_431_, v___x_433_);
lean_dec(v___x_431_);
v_nanos_437_ = lean_int_add(v___x_436_, v___x_432_);
lean_dec(v___x_436_);
v___x_438_ = lean_int_add(v_nanos_435_, v_nanos_437_);
lean_dec(v_nanos_437_);
lean_dec(v_nanos_435_);
v___x_439_ = l_Std_Time_Duration_ofNanoseconds(v___x_438_);
lean_dec(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours___boxed(lean_object* v_t_440_, lean_object* v_h_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_Time_Timestamp_addHours(v_t_440_, v_h_441_);
lean_dec(v_h_441_);
lean_dec_ref(v_t_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours(lean_object* v_t_443_, lean_object* v_h_444_){
_start:
{
lean_object* v_second_445_; lean_object* v_nano_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v_nanos_453_; lean_object* v___x_454_; lean_object* v_nanos_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_second_445_ = lean_ctor_get(v_t_443_, 0);
v_nano_446_ = lean_ctor_get(v_t_443_, 1);
v___x_447_ = lean_obj_once(&l_Std_Time_Timestamp_addHours___closed__0, &l_Std_Time_Timestamp_addHours___closed__0_once, _init_l_Std_Time_Timestamp_addHours___closed__0);
v___x_448_ = lean_int_mul(v_h_444_, v___x_447_);
v___x_449_ = lean_int_neg(v___x_448_);
lean_dec(v___x_448_);
v___x_450_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_451_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_452_ = lean_int_mul(v_second_445_, v___x_451_);
v_nanos_453_ = lean_int_add(v___x_452_, v_nano_446_);
lean_dec(v___x_452_);
v___x_454_ = lean_int_mul(v___x_449_, v___x_451_);
lean_dec(v___x_449_);
v_nanos_455_ = lean_int_add(v___x_454_, v___x_450_);
lean_dec(v___x_454_);
v___x_456_ = lean_int_add(v_nanos_453_, v_nanos_455_);
lean_dec(v_nanos_455_);
lean_dec(v_nanos_453_);
v___x_457_ = l_Std_Time_Duration_ofNanoseconds(v___x_456_);
lean_dec(v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours___boxed(lean_object* v_t_458_, lean_object* v_h_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_Time_Timestamp_subHours(v_t_458_, v_h_459_);
lean_dec(v_h_459_);
lean_dec_ref(v_t_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays(lean_object* v_t_461_, lean_object* v_d_462_){
_start:
{
lean_object* v_second_463_; lean_object* v_nano_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v_nanos_470_; lean_object* v___x_471_; lean_object* v_nanos_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v_second_463_ = lean_ctor_get(v_t_461_, 0);
v_nano_464_ = lean_ctor_get(v_t_461_, 1);
v___x_465_ = lean_obj_once(&l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0);
v___x_466_ = lean_int_mul(v_d_462_, v___x_465_);
v___x_467_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_468_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_469_ = lean_int_mul(v_second_463_, v___x_468_);
v_nanos_470_ = lean_int_add(v___x_469_, v_nano_464_);
lean_dec(v___x_469_);
v___x_471_ = lean_int_mul(v___x_466_, v___x_468_);
lean_dec(v___x_466_);
v_nanos_472_ = lean_int_add(v___x_471_, v___x_467_);
lean_dec(v___x_471_);
v___x_473_ = lean_int_add(v_nanos_470_, v_nanos_472_);
lean_dec(v_nanos_472_);
lean_dec(v_nanos_470_);
v___x_474_ = l_Std_Time_Duration_ofNanoseconds(v___x_473_);
lean_dec(v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays___boxed(lean_object* v_t_475_, lean_object* v_d_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_Time_Timestamp_addDays(v_t_475_, v_d_476_);
lean_dec(v_d_476_);
lean_dec_ref(v_t_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays(lean_object* v_t_478_, lean_object* v_d_479_){
_start:
{
lean_object* v_second_480_; lean_object* v_nano_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_nanos_488_; lean_object* v___x_489_; lean_object* v_nanos_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v_second_480_ = lean_ctor_get(v_t_478_, 0);
v_nano_481_ = lean_ctor_get(v_t_478_, 1);
v___x_482_ = lean_obj_once(&l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0);
v___x_483_ = lean_int_mul(v_d_479_, v___x_482_);
v___x_484_ = lean_int_neg(v___x_483_);
lean_dec(v___x_483_);
v___x_485_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_486_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_487_ = lean_int_mul(v_second_480_, v___x_486_);
v_nanos_488_ = lean_int_add(v___x_487_, v_nano_481_);
lean_dec(v___x_487_);
v___x_489_ = lean_int_mul(v___x_484_, v___x_486_);
lean_dec(v___x_484_);
v_nanos_490_ = lean_int_add(v___x_489_, v___x_485_);
lean_dec(v___x_489_);
v___x_491_ = lean_int_add(v_nanos_488_, v_nanos_490_);
lean_dec(v_nanos_490_);
lean_dec(v_nanos_488_);
v___x_492_ = l_Std_Time_Duration_ofNanoseconds(v___x_491_);
lean_dec(v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays___boxed(lean_object* v_t_493_, lean_object* v_d_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_Time_Timestamp_subDays(v_t_493_, v_d_494_);
lean_dec(v_d_494_);
lean_dec_ref(v_t_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks(lean_object* v_t_496_, lean_object* v_d_497_){
_start:
{
lean_object* v_second_498_; lean_object* v_nano_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v_nanos_507_; lean_object* v___x_508_; lean_object* v_nanos_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v_second_498_ = lean_ctor_get(v_t_496_, 0);
v_nano_499_ = lean_ctor_get(v_t_496_, 1);
v___x_500_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_501_ = lean_int_mul(v_d_497_, v___x_500_);
v___x_502_ = lean_obj_once(&l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0);
v___x_503_ = lean_int_mul(v___x_501_, v___x_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_505_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_506_ = lean_int_mul(v_second_498_, v___x_505_);
v_nanos_507_ = lean_int_add(v___x_506_, v_nano_499_);
lean_dec(v___x_506_);
v___x_508_ = lean_int_mul(v___x_503_, v___x_505_);
lean_dec(v___x_503_);
v_nanos_509_ = lean_int_add(v___x_508_, v___x_504_);
lean_dec(v___x_508_);
v___x_510_ = lean_int_add(v_nanos_507_, v_nanos_509_);
lean_dec(v_nanos_509_);
lean_dec(v_nanos_507_);
v___x_511_ = l_Std_Time_Duration_ofNanoseconds(v___x_510_);
lean_dec(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks___boxed(lean_object* v_t_512_, lean_object* v_d_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_Time_Timestamp_addWeeks(v_t_512_, v_d_513_);
lean_dec(v_d_513_);
lean_dec_ref(v_t_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks(lean_object* v_t_515_, lean_object* v_d_516_){
_start:
{
lean_object* v_second_517_; lean_object* v_nano_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_nanos_527_; lean_object* v___x_528_; lean_object* v_nanos_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_second_517_ = lean_ctor_get(v_t_515_, 0);
v_nano_518_ = lean_ctor_get(v_t_515_, 1);
v___x_519_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_520_ = lean_int_mul(v_d_516_, v___x_519_);
v___x_521_ = lean_obj_once(&l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0);
v___x_522_ = lean_int_mul(v___x_520_, v___x_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_int_neg(v___x_522_);
lean_dec(v___x_522_);
v___x_524_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_525_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_526_ = lean_int_mul(v_second_517_, v___x_525_);
v_nanos_527_ = lean_int_add(v___x_526_, v_nano_518_);
lean_dec(v___x_526_);
v___x_528_ = lean_int_mul(v___x_523_, v___x_525_);
lean_dec(v___x_523_);
v_nanos_529_ = lean_int_add(v___x_528_, v___x_524_);
lean_dec(v___x_528_);
v___x_530_ = lean_int_add(v_nanos_527_, v_nanos_529_);
lean_dec(v_nanos_529_);
lean_dec(v_nanos_527_);
v___x_531_ = l_Std_Time_Duration_ofNanoseconds(v___x_530_);
lean_dec(v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks___boxed(lean_object* v_t_532_, lean_object* v_d_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_Time_Timestamp_subWeeks(v_t_532_, v_d_533_);
lean_dec(v_d_533_);
lean_dec_ref(v_t_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration(lean_object* v_t_535_, lean_object* v_d_536_){
_start:
{
lean_object* v_second_537_; lean_object* v_nano_538_; lean_object* v_second_539_; lean_object* v_nano_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_nanos_543_; lean_object* v___x_544_; lean_object* v_nanos_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_second_537_ = lean_ctor_get(v_t_535_, 0);
v_nano_538_ = lean_ctor_get(v_t_535_, 1);
v_second_539_ = lean_ctor_get(v_d_536_, 0);
v_nano_540_ = lean_ctor_get(v_d_536_, 1);
v___x_541_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_542_ = lean_int_mul(v_second_537_, v___x_541_);
v_nanos_543_ = lean_int_add(v___x_542_, v_nano_538_);
lean_dec(v___x_542_);
v___x_544_ = lean_int_mul(v_second_539_, v___x_541_);
v_nanos_545_ = lean_int_add(v___x_544_, v_nano_540_);
lean_dec(v___x_544_);
v___x_546_ = lean_int_add(v_nanos_543_, v_nanos_545_);
lean_dec(v_nanos_545_);
lean_dec(v_nanos_543_);
v___x_547_ = l_Std_Time_Duration_ofNanoseconds(v___x_546_);
lean_dec(v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration___boxed(lean_object* v_t_548_, lean_object* v_d_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_Time_Timestamp_addDuration(v_t_548_, v_d_549_);
lean_dec_ref(v_d_549_);
lean_dec_ref(v_t_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration(lean_object* v_t_551_, lean_object* v_d_552_){
_start:
{
lean_object* v_second_553_; lean_object* v_nano_554_; lean_object* v_second_555_; lean_object* v_nano_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v_nanos_561_; lean_object* v___x_562_; lean_object* v_nanos_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_second_553_ = lean_ctor_get(v_d_552_, 0);
v_nano_554_ = lean_ctor_get(v_d_552_, 1);
v_second_555_ = lean_ctor_get(v_t_551_, 0);
v_nano_556_ = lean_ctor_get(v_t_551_, 1);
v___x_557_ = lean_int_neg(v_second_553_);
v___x_558_ = lean_int_neg(v_nano_554_);
v___x_559_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_560_ = lean_int_mul(v_second_555_, v___x_559_);
v_nanos_561_ = lean_int_add(v___x_560_, v_nano_556_);
lean_dec(v___x_560_);
v___x_562_ = lean_int_mul(v___x_557_, v___x_559_);
lean_dec(v___x_557_);
v_nanos_563_ = lean_int_add(v___x_562_, v___x_558_);
lean_dec(v___x_558_);
lean_dec(v___x_562_);
v___x_564_ = lean_int_add(v_nanos_561_, v_nanos_563_);
lean_dec(v_nanos_563_);
lean_dec(v_nanos_561_);
v___x_565_ = l_Std_Time_Duration_ofNanoseconds(v___x_564_);
lean_dec(v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration___boxed(lean_object* v_t_566_, lean_object* v_d_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_Time_Timestamp_subDuration(v_t_566_, v_d_567_);
lean_dec_ref(v_d_567_);
lean_dec_ref(v_t_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0(lean_object* v_x_601_, lean_object* v_y_602_){
_start:
{
lean_object* v_second_603_; lean_object* v_nano_604_; lean_object* v_second_605_; lean_object* v_nano_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v_nanos_611_; lean_object* v___x_612_; lean_object* v_nanos_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_second_603_ = lean_ctor_get(v_y_602_, 0);
v_nano_604_ = lean_ctor_get(v_y_602_, 1);
v_second_605_ = lean_ctor_get(v_x_601_, 0);
v_nano_606_ = lean_ctor_get(v_x_601_, 1);
v___x_607_ = lean_int_neg(v_second_603_);
v___x_608_ = lean_int_neg(v_nano_604_);
v___x_609_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_610_ = lean_int_mul(v_second_605_, v___x_609_);
v_nanos_611_ = lean_int_add(v___x_610_, v_nano_606_);
lean_dec(v___x_610_);
v___x_612_ = lean_int_mul(v___x_607_, v___x_609_);
lean_dec(v___x_607_);
v_nanos_613_ = lean_int_add(v___x_612_, v___x_608_);
lean_dec(v___x_608_);
lean_dec(v___x_612_);
v___x_614_ = lean_int_add(v_nanos_611_, v_nanos_613_);
lean_dec(v_nanos_613_);
lean_dec(v_nanos_611_);
v___x_615_ = l_Std_Time_Duration_ofNanoseconds(v___x_614_);
lean_dec(v___x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed(lean_object* v_x_616_, lean_object* v_y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_Time_Timestamp_instHSubDuration__1___lam__0(v_x_616_, v_y_617_);
lean_dec_ref(v_y_617_);
lean_dec_ref(v_x_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instOfNat(lean_object* v_n_621_){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_nat_to_int(v_n_621_);
v___x_623_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_622_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
return v___x_624_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Duration(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_WallTime(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_DateTime_Timestamp(uint8_t builtin) {
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
res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedTimestamp_default = _init_l_Std_Time_instInhabitedTimestamp_default();
lean_mark_persistent(l_Std_Time_instInhabitedTimestamp_default);
l_Std_Time_instInhabitedTimestamp = _init_l_Std_Time_instInhabitedTimestamp();
lean_mark_persistent(l_Std_Time_instInhabitedTimestamp);
l_Std_Time_instLETimestamp = _init_l_Std_Time_instLETimestamp();
lean_mark_persistent(l_Std_Time_instLETimestamp);
l_Std_Time_instLTTimestamp = _init_l_Std_Time_instLTTimestamp();
lean_mark_persistent(l_Std_Time_instLTTimestamp);
l_Std_Time_instOrdTimestamp = _init_l_Std_Time_instOrdTimestamp();
lean_mark_persistent(l_Std_Time_instOrdTimestamp);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_DateTime_Timestamp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Std_Time_Duration(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_WallTime(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_DateTime_Timestamp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Duration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_WallTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_Timestamp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_DateTime_Timestamp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_DateTime_Timestamp(builtin);
}
#ifdef __cplusplus
}
#endif

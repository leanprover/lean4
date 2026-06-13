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
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimestamp_decEq(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_97_, v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimestamp_decEq___boxed(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Std_Time_instDecidableEqTimestamp_decEq(v_x_100_, v_x_101_);
lean_dec_ref(v_x_101_);
lean_dec_ref(v_x_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimestamp(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
uint8_t v___x_106_; 
v___x_106_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_104_, v_x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimestamp___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_Time_instDecidableEqTimestamp(v_x_107_, v_x_108_);
lean_dec_ref(v_x_108_);
lean_dec_ref(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimestamp_default___closed__0(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimestamp_default(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Std_Time_instInhabitedTimestamp_default___closed__0, &l_Std_Time_instInhabitedTimestamp_default___closed__0_once, _init_l_Std_Time_instInhabitedTimestamp_default___closed__0);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedTimestamp_default_spec__0(lean_object* v_a_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_nat_to_int(v_a_114_);
v___x_116_ = l_Rat_ofInt(v___x_115_);
return v___x_116_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimestamp(void){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_Time_instInhabitedTimestamp_default;
return v___x_117_;
}
}
static lean_object* _init_l_Std_Time_instLETimestamp(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_box(0);
return v___x_118_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLeTimestamp(lean_object* v_x_119_, lean_object* v_y_120_){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = l_Std_Time_Duration_instDecidableLe(v_x_119_, v_y_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeTimestamp___boxed(lean_object* v_x_122_, lean_object* v_y_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Std_Time_instDecidableLeTimestamp(v_x_122_, v_y_123_);
lean_dec_ref(v_y_123_);
lean_dec_ref(v_x_122_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
static lean_object* _init_l_Std_Time_instLTTimestamp(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLtTimestamp(lean_object* v_x_127_, lean_object* v_y_128_){
_start:
{
uint8_t v___x_129_; 
v___x_129_ = l_Std_Time_Duration_instDecidableLt(v_x_127_, v_y_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtTimestamp___boxed(lean_object* v_x_130_, lean_object* v_y_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Std_Time_instDecidableLtTimestamp(v_x_130_, v_y_131_);
lean_dec_ref(v_y_131_);
lean_dec_ref(v_x_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0(lean_object* v_s_134_){
_start:
{
lean_object* v_second_135_; lean_object* v___x_136_; 
v_second_135_ = lean_ctor_get(v_s_134_, 0);
v___x_136_ = l_Int_repr(v_second_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0___boxed(lean_object* v_s_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Std_Time_instToStringTimestamp___lam__0(v_s_137_);
lean_dec_ref(v_s_137_);
return v_res_138_;
}
}
static lean_object* _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_unsigned_to_nat(1000000000u);
v___x_145_ = lean_nat_to_int(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp__1___lam__0(lean_object* v_s_146_, lean_object* v___y_147_){
_start:
{
lean_object* v_second_148_; lean_object* v_nano_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_163_; 
v_second_148_ = lean_ctor_get(v_s_146_, 0);
v_nano_149_ = lean_ctor_get(v_s_146_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_s_146_);
if (v_isSharedCheck_163_ == 0)
{
v___x_151_ = v_s_146_;
v_isShared_152_ = v_isSharedCheck_163_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_nano_149_);
lean_inc(v_second_148_);
lean_dec(v_s_146_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_163_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v_nanos_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_153_ = ((lean_object*)(l_Std_Time_instReprTimestamp__1___lam__0___closed__1));
v___x_154_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_155_ = lean_int_mul(v_second_148_, v___x_154_);
lean_dec(v_second_148_);
v_nanos_156_ = lean_int_add(v___x_155_, v_nano_149_);
lean_dec(v_nano_149_);
lean_dec(v___x_155_);
v___x_157_ = lean_unsigned_to_nat(0u);
v___x_158_ = l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanos_156_, v___x_157_);
lean_dec(v_nanos_156_);
if (v_isShared_152_ == 0)
{
lean_ctor_set_tag(v___x_151_, 5);
lean_ctor_set(v___x_151_, 1, v___x_158_);
lean_ctor_set(v___x_151_, 0, v___x_153_);
v___x_160_ = v___x_151_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___x_158_);
v___x_160_ = v_reuseFailAlloc_162_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; 
v___x_161_ = l_Repr_addAppParen(v___x_160_, v___y_147_);
return v___x_161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp__1___lam__0___boxed(lean_object* v_s_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_Time_instReprTimestamp__1___lam__0(v_s_164_, v___y_165_);
lean_dec(v___y_165_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp___lam__0(lean_object* v_x_169_){
_start:
{
lean_inc_ref(v_x_169_);
return v_x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp___lam__0___boxed(lean_object* v_x_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_Time_instOrdTimestamp___lam__0(v_x_170_);
lean_dec_ref(v_x_170_);
return v_res_171_;
}
}
static lean_object* _init_l_Std_Time_instOrdTimestamp___closed__1(void){
_start:
{
lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___f_173_ = ((lean_object*)(l_Std_Time_instOrdTimestamp___closed__0));
v___x_174_ = l_Std_Time_instOrdDuration;
v___x_175_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_175_, 0, lean_box(0));
lean_closure_set(v___x_175_, 1, lean_box(0));
lean_closure_set(v___x_175_, 2, v___x_174_);
lean_closure_set(v___x_175_, 3, v___f_173_);
return v___x_175_;
}
}
static lean_object* _init_l_Std_Time_instOrdTimestamp(void){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l_Std_Time_instOrdTimestamp___closed__1, &l_Std_Time_instOrdTimestamp___closed__1_once, _init_l_Std_Time_instOrdTimestamp___closed__1);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_now___boxed(lean_object* v_a_00___x40___internal___hyg_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = lean_get_current_time();
return v_res_179_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(60u);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutesSinceUnixEpoch(lean_object* v_tm_182_){
_start:
{
lean_object* v_second_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_second_183_ = lean_ctor_get(v_tm_182_, 0);
v___x_184_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0);
v___x_185_ = lean_int_div(v_second_183_, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___boxed(lean_object* v_tm_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Std_Time_Timestamp_toMinutesSinceUnixEpoch(v_tm_186_);
lean_dec_ref(v_tm_186_);
return v_res_187_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_unsigned_to_nat(86400u);
v___x_189_ = lean_nat_to_int(v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDaysSinceUnixEpoch(lean_object* v_tm_190_){
_start:
{
lean_object* v_second_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_second_191_ = lean_ctor_get(v_tm_190_, 0);
v___x_192_ = lean_obj_once(&l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0);
v___x_193_ = lean_int_div(v_second_191_, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDaysSinceUnixEpoch___boxed(lean_object* v_tm_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_Time_Timestamp_toDaysSinceUnixEpoch(v_tm_194_);
lean_dec_ref(v_tm_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofSecondsSinceUnixEpoch(lean_object* v_secs_196_){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v_secs_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(lean_object* v_nanos_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch___boxed(lean_object* v_nanos_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(v_nanos_201_);
lean_dec(v_nanos_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofDurationSinceUnixEpoch(lean_object* v_duration_203_){
_start:
{
lean_inc_ref(v_duration_203_);
return v_duration_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofDurationSinceUnixEpoch___boxed(lean_object* v_duration_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_Time_Timestamp_ofDurationSinceUnixEpoch(v_duration_204_);
lean_dec_ref(v_duration_204_);
return v_res_205_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(1000000u);
v___x_207_ = lean_nat_to_int(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(lean_object* v_milli_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_210_ = lean_int_mul(v_milli_208_, v___x_209_);
v___x_211_ = l_Std_Time_Duration_ofNanoseconds(v___x_210_);
lean_dec(v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___boxed(lean_object* v_milli_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(v_milli_212_);
lean_dec(v_milli_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(lean_object* v_t_214_){
_start:
{
lean_object* v_second_215_; 
v_second_215_ = lean_ctor_get(v_t_214_, 0);
lean_inc(v_second_215_);
return v_second_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch___boxed(lean_object* v_t_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(v_t_216_);
lean_dec_ref(v_t_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(lean_object* v_tm_218_){
_start:
{
lean_object* v_second_219_; lean_object* v_nano_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_nanos_223_; 
v_second_219_ = lean_ctor_get(v_tm_218_, 0);
v_nano_220_ = lean_ctor_get(v_tm_218_, 1);
v___x_221_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_222_ = lean_int_mul(v_second_219_, v___x_221_);
v_nanos_223_ = lean_int_add(v___x_222_, v_nano_220_);
lean_dec(v___x_222_);
return v_nanos_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch___boxed(lean_object* v_tm_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(v_tm_224_);
lean_dec_ref(v_tm_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(lean_object* v_tm_226_){
_start:
{
lean_object* v_second_227_; lean_object* v_nano_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_second_227_ = lean_ctor_get(v_tm_226_, 0);
v_nano_228_ = lean_ctor_get(v_tm_226_, 1);
v___x_229_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_230_ = lean_int_mul(v_second_227_, v___x_229_);
v___x_231_ = lean_int_add(v___x_230_, v_nano_228_);
lean_dec(v___x_230_);
v___x_232_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_233_ = lean_int_div(v___x_231_, v___x_232_);
lean_dec(v___x_231_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch___boxed(lean_object* v_tm_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(v_tm_234_);
lean_dec_ref(v_tm_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since(lean_object* v_f_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_get_current_time();
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_259_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_259_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_259_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_259_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v_second_243_; lean_object* v_nano_244_; lean_object* v_second_245_; lean_object* v_nano_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v_second_243_ = lean_ctor_get(v_f_236_, 0);
v_nano_244_ = lean_ctor_get(v_f_236_, 1);
v_second_245_ = lean_ctor_get(v_a_239_, 0);
lean_inc(v_second_245_);
v_nano_246_ = lean_ctor_get(v_a_239_, 1);
lean_inc(v_nano_246_);
lean_dec(v_a_239_);
v___x_247_ = lean_int_neg(v_second_243_);
v___x_248_ = lean_int_neg(v_nano_244_);
v___x_249_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_250_ = lean_int_mul(v_second_245_, v___x_249_);
lean_dec(v_second_245_);
v___x_251_ = lean_int_add(v___x_250_, v_nano_246_);
lean_dec(v_nano_246_);
lean_dec(v___x_250_);
v___x_252_ = lean_int_mul(v___x_247_, v___x_249_);
lean_dec(v___x_247_);
v___x_253_ = lean_int_add(v___x_252_, v___x_248_);
lean_dec(v___x_248_);
lean_dec(v___x_252_);
v___x_254_ = lean_int_add(v___x_251_, v___x_253_);
lean_dec(v___x_253_);
lean_dec(v___x_251_);
v___x_255_ = l_Std_Time_Duration_ofNanoseconds(v___x_254_);
lean_dec(v___x_254_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_255_);
v___x_257_ = v___x_241_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
v_a_260_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_238_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_238_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since___boxed(lean_object* v_f_268_, lean_object* v_a_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_Time_Timestamp_since(v_f_268_);
lean_dec_ref(v_f_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch(lean_object* v_tm_271_){
_start:
{
lean_inc_ref(v_tm_271_);
return v_tm_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch___boxed(lean_object* v_tm_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_Time_Timestamp_toDurationSinceUnixEpoch(v_tm_272_);
lean_dec_ref(v_tm_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds(lean_object* v_t_274_, lean_object* v_s_275_){
_start:
{
lean_object* v_second_276_; lean_object* v_nano_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v_second_281_; lean_object* v_nano_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_second_276_ = lean_ctor_get(v_t_274_, 0);
v_nano_277_ = lean_ctor_get(v_t_274_, 1);
v___x_278_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_279_ = lean_int_mul(v_s_275_, v___x_278_);
v___x_280_ = l_Std_Time_Duration_ofNanoseconds(v___x_279_);
lean_dec(v___x_279_);
v_second_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_second_281_);
v_nano_282_ = lean_ctor_get(v___x_280_, 1);
lean_inc(v_nano_282_);
lean_dec_ref(v___x_280_);
v___x_283_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_284_ = lean_int_mul(v_second_276_, v___x_283_);
v___x_285_ = lean_int_add(v___x_284_, v_nano_277_);
lean_dec(v___x_284_);
v___x_286_ = lean_int_mul(v_second_281_, v___x_283_);
lean_dec(v_second_281_);
v___x_287_ = lean_int_add(v___x_286_, v_nano_282_);
lean_dec(v_nano_282_);
lean_dec(v___x_286_);
v___x_288_ = lean_int_add(v___x_285_, v___x_287_);
lean_dec(v___x_287_);
lean_dec(v___x_285_);
v___x_289_ = l_Std_Time_Duration_ofNanoseconds(v___x_288_);
lean_dec(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds___boxed(lean_object* v_t_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Std_Time_Timestamp_addMilliseconds(v_t_290_, v_s_291_);
lean_dec(v_s_291_);
lean_dec_ref(v_t_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds(lean_object* v_t_293_, lean_object* v_s_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v_second_298_; lean_object* v_nano_299_; lean_object* v_second_300_; lean_object* v_nano_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_295_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_296_ = lean_int_mul(v_s_294_, v___x_295_);
v___x_297_ = l_Std_Time_Duration_ofNanoseconds(v___x_296_);
lean_dec(v___x_296_);
v_second_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_second_298_);
v_nano_299_ = lean_ctor_get(v___x_297_, 1);
lean_inc(v_nano_299_);
lean_dec_ref(v___x_297_);
v_second_300_ = lean_ctor_get(v_t_293_, 0);
v_nano_301_ = lean_ctor_get(v_t_293_, 1);
v___x_302_ = lean_int_neg(v_second_298_);
lean_dec(v_second_298_);
v___x_303_ = lean_int_neg(v_nano_299_);
lean_dec(v_nano_299_);
v___x_304_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_305_ = lean_int_mul(v_second_300_, v___x_304_);
v___x_306_ = lean_int_add(v___x_305_, v_nano_301_);
lean_dec(v___x_305_);
v___x_307_ = lean_int_mul(v___x_302_, v___x_304_);
lean_dec(v___x_302_);
v___x_308_ = lean_int_add(v___x_307_, v___x_303_);
lean_dec(v___x_303_);
lean_dec(v___x_307_);
v___x_309_ = lean_int_add(v___x_306_, v___x_308_);
lean_dec(v___x_308_);
lean_dec(v___x_306_);
v___x_310_ = l_Std_Time_Duration_ofNanoseconds(v___x_309_);
lean_dec(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds___boxed(lean_object* v_t_311_, lean_object* v_s_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_Time_Timestamp_subMilliseconds(v_t_311_, v_s_312_);
lean_dec(v_s_312_);
lean_dec_ref(v_t_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds(lean_object* v_t_314_, lean_object* v_s_315_){
_start:
{
lean_object* v_second_316_; lean_object* v_nano_317_; lean_object* v___x_318_; lean_object* v_second_319_; lean_object* v_nano_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_second_316_ = lean_ctor_get(v_t_314_, 0);
v_nano_317_ = lean_ctor_get(v_t_314_, 1);
v___x_318_ = l_Std_Time_Duration_ofNanoseconds(v_s_315_);
v_second_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_second_319_);
v_nano_320_ = lean_ctor_get(v___x_318_, 1);
lean_inc(v_nano_320_);
lean_dec_ref(v___x_318_);
v___x_321_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_322_ = lean_int_mul(v_second_316_, v___x_321_);
v___x_323_ = lean_int_add(v___x_322_, v_nano_317_);
lean_dec(v___x_322_);
v___x_324_ = lean_int_mul(v_second_319_, v___x_321_);
lean_dec(v_second_319_);
v___x_325_ = lean_int_add(v___x_324_, v_nano_320_);
lean_dec(v_nano_320_);
lean_dec(v___x_324_);
v___x_326_ = lean_int_add(v___x_323_, v___x_325_);
lean_dec(v___x_325_);
lean_dec(v___x_323_);
v___x_327_ = l_Std_Time_Duration_ofNanoseconds(v___x_326_);
lean_dec(v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds___boxed(lean_object* v_t_328_, lean_object* v_s_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_Time_Timestamp_addNanoseconds(v_t_328_, v_s_329_);
lean_dec(v_s_329_);
lean_dec_ref(v_t_328_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds(lean_object* v_t_331_, lean_object* v_s_332_){
_start:
{
lean_object* v___x_333_; lean_object* v_second_334_; lean_object* v_nano_335_; lean_object* v_second_336_; lean_object* v_nano_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_333_ = l_Std_Time_Duration_ofNanoseconds(v_s_332_);
v_second_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_second_334_);
v_nano_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_nano_335_);
lean_dec_ref(v___x_333_);
v_second_336_ = lean_ctor_get(v_t_331_, 0);
v_nano_337_ = lean_ctor_get(v_t_331_, 1);
v___x_338_ = lean_int_neg(v_second_334_);
lean_dec(v_second_334_);
v___x_339_ = lean_int_neg(v_nano_335_);
lean_dec(v_nano_335_);
v___x_340_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_341_ = lean_int_mul(v_second_336_, v___x_340_);
v___x_342_ = lean_int_add(v___x_341_, v_nano_337_);
lean_dec(v___x_341_);
v___x_343_ = lean_int_mul(v___x_338_, v___x_340_);
lean_dec(v___x_338_);
v___x_344_ = lean_int_add(v___x_343_, v___x_339_);
lean_dec(v___x_339_);
lean_dec(v___x_343_);
v___x_345_ = lean_int_add(v___x_342_, v___x_344_);
lean_dec(v___x_344_);
lean_dec(v___x_342_);
v___x_346_ = l_Std_Time_Duration_ofNanoseconds(v___x_345_);
lean_dec(v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds___boxed(lean_object* v_t_347_, lean_object* v_s_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Std_Time_Timestamp_subNanoseconds(v_t_347_, v_s_348_);
lean_dec(v_s_348_);
lean_dec_ref(v_t_347_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds(lean_object* v_t_350_, lean_object* v_s_351_){
_start:
{
lean_object* v_second_352_; lean_object* v_nano_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_second_352_ = lean_ctor_get(v_t_350_, 0);
v_nano_353_ = lean_ctor_get(v_t_350_, 1);
v___x_354_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_355_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_356_ = lean_int_mul(v_second_352_, v___x_355_);
v___x_357_ = lean_int_add(v___x_356_, v_nano_353_);
lean_dec(v___x_356_);
v___x_358_ = lean_int_mul(v_s_351_, v___x_355_);
v___x_359_ = lean_int_add(v___x_358_, v___x_354_);
lean_dec(v___x_358_);
v___x_360_ = lean_int_add(v___x_357_, v___x_359_);
lean_dec(v___x_359_);
lean_dec(v___x_357_);
v___x_361_ = l_Std_Time_Duration_ofNanoseconds(v___x_360_);
lean_dec(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds___boxed(lean_object* v_t_362_, lean_object* v_s_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_Time_Timestamp_addSeconds(v_t_362_, v_s_363_);
lean_dec(v_s_363_);
lean_dec_ref(v_t_362_);
return v_res_364_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_subSeconds___closed__0(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_366_ = lean_int_neg(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds(lean_object* v_t_367_, lean_object* v_s_368_){
_start:
{
lean_object* v_second_369_; lean_object* v_nano_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_second_369_ = lean_ctor_get(v_t_367_, 0);
v_nano_370_ = lean_ctor_get(v_t_367_, 1);
v___x_371_ = lean_int_neg(v_s_368_);
v___x_372_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_373_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_374_ = lean_int_mul(v_second_369_, v___x_373_);
v___x_375_ = lean_int_add(v___x_374_, v_nano_370_);
lean_dec(v___x_374_);
v___x_376_ = lean_int_mul(v___x_371_, v___x_373_);
lean_dec(v___x_371_);
v___x_377_ = lean_int_add(v___x_376_, v___x_372_);
lean_dec(v___x_376_);
v___x_378_ = lean_int_add(v___x_375_, v___x_377_);
lean_dec(v___x_377_);
lean_dec(v___x_375_);
v___x_379_ = l_Std_Time_Duration_ofNanoseconds(v___x_378_);
lean_dec(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds___boxed(lean_object* v_t_380_, lean_object* v_s_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Std_Time_Timestamp_subSeconds(v_t_380_, v_s_381_);
lean_dec(v_s_381_);
lean_dec_ref(v_t_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes(lean_object* v_t_383_, lean_object* v_m_384_){
_start:
{
lean_object* v_second_385_; lean_object* v_nano_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_second_385_ = lean_ctor_get(v_t_383_, 0);
v_nano_386_ = lean_ctor_get(v_t_383_, 1);
v___x_387_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0);
v___x_388_ = lean_int_mul(v_m_384_, v___x_387_);
v___x_389_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_390_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_391_ = lean_int_mul(v_second_385_, v___x_390_);
v___x_392_ = lean_int_add(v___x_391_, v_nano_386_);
lean_dec(v___x_391_);
v___x_393_ = lean_int_mul(v___x_388_, v___x_390_);
lean_dec(v___x_388_);
v___x_394_ = lean_int_add(v___x_393_, v___x_389_);
lean_dec(v___x_393_);
v___x_395_ = lean_int_add(v___x_392_, v___x_394_);
lean_dec(v___x_394_);
lean_dec(v___x_392_);
v___x_396_ = l_Std_Time_Duration_ofNanoseconds(v___x_395_);
lean_dec(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes___boxed(lean_object* v_t_397_, lean_object* v_m_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_Time_Timestamp_addMinutes(v_t_397_, v_m_398_);
lean_dec(v_m_398_);
lean_dec_ref(v_t_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes(lean_object* v_t_400_, lean_object* v_m_401_){
_start:
{
lean_object* v_second_402_; lean_object* v_nano_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_second_402_ = lean_ctor_get(v_t_400_, 0);
v_nano_403_ = lean_ctor_get(v_t_400_, 1);
v___x_404_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toMinutesSinceUnixEpoch___closed__0);
v___x_405_ = lean_int_mul(v_m_401_, v___x_404_);
v___x_406_ = lean_int_neg(v___x_405_);
lean_dec(v___x_405_);
v___x_407_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_408_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_409_ = lean_int_mul(v_second_402_, v___x_408_);
v___x_410_ = lean_int_add(v___x_409_, v_nano_403_);
lean_dec(v___x_409_);
v___x_411_ = lean_int_mul(v___x_406_, v___x_408_);
lean_dec(v___x_406_);
v___x_412_ = lean_int_add(v___x_411_, v___x_407_);
lean_dec(v___x_411_);
v___x_413_ = lean_int_add(v___x_410_, v___x_412_);
lean_dec(v___x_412_);
lean_dec(v___x_410_);
v___x_414_ = l_Std_Time_Duration_ofNanoseconds(v___x_413_);
lean_dec(v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes___boxed(lean_object* v_t_415_, lean_object* v_m_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_Time_Timestamp_subMinutes(v_t_415_, v_m_416_);
lean_dec(v_m_416_);
lean_dec_ref(v_t_415_);
return v_res_417_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_addHours___closed__0(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_418_ = lean_unsigned_to_nat(3600u);
v___x_419_ = lean_nat_to_int(v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours(lean_object* v_t_420_, lean_object* v_h_421_){
_start:
{
lean_object* v_second_422_; lean_object* v_nano_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_second_422_ = lean_ctor_get(v_t_420_, 0);
v_nano_423_ = lean_ctor_get(v_t_420_, 1);
v___x_424_ = lean_obj_once(&l_Std_Time_Timestamp_addHours___closed__0, &l_Std_Time_Timestamp_addHours___closed__0_once, _init_l_Std_Time_Timestamp_addHours___closed__0);
v___x_425_ = lean_int_mul(v_h_421_, v___x_424_);
v___x_426_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_427_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_428_ = lean_int_mul(v_second_422_, v___x_427_);
v___x_429_ = lean_int_add(v___x_428_, v_nano_423_);
lean_dec(v___x_428_);
v___x_430_ = lean_int_mul(v___x_425_, v___x_427_);
lean_dec(v___x_425_);
v___x_431_ = lean_int_add(v___x_430_, v___x_426_);
lean_dec(v___x_430_);
v___x_432_ = lean_int_add(v___x_429_, v___x_431_);
lean_dec(v___x_431_);
lean_dec(v___x_429_);
v___x_433_ = l_Std_Time_Duration_ofNanoseconds(v___x_432_);
lean_dec(v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours___boxed(lean_object* v_t_434_, lean_object* v_h_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_Time_Timestamp_addHours(v_t_434_, v_h_435_);
lean_dec(v_h_435_);
lean_dec_ref(v_t_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours(lean_object* v_t_437_, lean_object* v_h_438_){
_start:
{
lean_object* v_second_439_; lean_object* v_nano_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_second_439_ = lean_ctor_get(v_t_437_, 0);
v_nano_440_ = lean_ctor_get(v_t_437_, 1);
v___x_441_ = lean_obj_once(&l_Std_Time_Timestamp_addHours___closed__0, &l_Std_Time_Timestamp_addHours___closed__0_once, _init_l_Std_Time_Timestamp_addHours___closed__0);
v___x_442_ = lean_int_mul(v_h_438_, v___x_441_);
v___x_443_ = lean_int_neg(v___x_442_);
lean_dec(v___x_442_);
v___x_444_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_445_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_446_ = lean_int_mul(v_second_439_, v___x_445_);
v___x_447_ = lean_int_add(v___x_446_, v_nano_440_);
lean_dec(v___x_446_);
v___x_448_ = lean_int_mul(v___x_443_, v___x_445_);
lean_dec(v___x_443_);
v___x_449_ = lean_int_add(v___x_448_, v___x_444_);
lean_dec(v___x_448_);
v___x_450_ = lean_int_add(v___x_447_, v___x_449_);
lean_dec(v___x_449_);
lean_dec(v___x_447_);
v___x_451_ = l_Std_Time_Duration_ofNanoseconds(v___x_450_);
lean_dec(v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours___boxed(lean_object* v_t_452_, lean_object* v_h_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_Time_Timestamp_subHours(v_t_452_, v_h_453_);
lean_dec(v_h_453_);
lean_dec_ref(v_t_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays(lean_object* v_t_455_, lean_object* v_d_456_){
_start:
{
lean_object* v_second_457_; lean_object* v_nano_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_second_457_ = lean_ctor_get(v_t_455_, 0);
v_nano_458_ = lean_ctor_get(v_t_455_, 1);
v___x_459_ = lean_obj_once(&l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0);
v___x_460_ = lean_int_mul(v_d_456_, v___x_459_);
v___x_461_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_462_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_463_ = lean_int_mul(v_second_457_, v___x_462_);
v___x_464_ = lean_int_add(v___x_463_, v_nano_458_);
lean_dec(v___x_463_);
v___x_465_ = lean_int_mul(v___x_460_, v___x_462_);
lean_dec(v___x_460_);
v___x_466_ = lean_int_add(v___x_465_, v___x_461_);
lean_dec(v___x_465_);
v___x_467_ = lean_int_add(v___x_464_, v___x_466_);
lean_dec(v___x_466_);
lean_dec(v___x_464_);
v___x_468_ = l_Std_Time_Duration_ofNanoseconds(v___x_467_);
lean_dec(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays___boxed(lean_object* v_t_469_, lean_object* v_d_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Std_Time_Timestamp_addDays(v_t_469_, v_d_470_);
lean_dec(v_d_470_);
lean_dec_ref(v_t_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays(lean_object* v_t_472_, lean_object* v_d_473_){
_start:
{
lean_object* v_second_474_; lean_object* v_nano_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_second_474_ = lean_ctor_get(v_t_472_, 0);
v_nano_475_ = lean_ctor_get(v_t_472_, 1);
v___x_476_ = lean_obj_once(&l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0);
v___x_477_ = lean_int_mul(v_d_473_, v___x_476_);
v___x_478_ = lean_int_neg(v___x_477_);
lean_dec(v___x_477_);
v___x_479_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_480_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_481_ = lean_int_mul(v_second_474_, v___x_480_);
v___x_482_ = lean_int_add(v___x_481_, v_nano_475_);
lean_dec(v___x_481_);
v___x_483_ = lean_int_mul(v___x_478_, v___x_480_);
lean_dec(v___x_478_);
v___x_484_ = lean_int_add(v___x_483_, v___x_479_);
lean_dec(v___x_483_);
v___x_485_ = lean_int_add(v___x_482_, v___x_484_);
lean_dec(v___x_484_);
lean_dec(v___x_482_);
v___x_486_ = l_Std_Time_Duration_ofNanoseconds(v___x_485_);
lean_dec(v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays___boxed(lean_object* v_t_487_, lean_object* v_d_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_Time_Timestamp_subDays(v_t_487_, v_d_488_);
lean_dec(v_d_488_);
lean_dec_ref(v_t_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks(lean_object* v_t_490_, lean_object* v_d_491_){
_start:
{
lean_object* v_second_492_; lean_object* v_nano_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_second_492_ = lean_ctor_get(v_t_490_, 0);
v_nano_493_ = lean_ctor_get(v_t_490_, 1);
v___x_494_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_495_ = lean_int_mul(v_d_491_, v___x_494_);
v___x_496_ = lean_obj_once(&l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0);
v___x_497_ = lean_int_mul(v___x_495_, v___x_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_499_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_500_ = lean_int_mul(v_second_492_, v___x_499_);
v___x_501_ = lean_int_add(v___x_500_, v_nano_493_);
lean_dec(v___x_500_);
v___x_502_ = lean_int_mul(v___x_497_, v___x_499_);
lean_dec(v___x_497_);
v___x_503_ = lean_int_add(v___x_502_, v___x_498_);
lean_dec(v___x_502_);
v___x_504_ = lean_int_add(v___x_501_, v___x_503_);
lean_dec(v___x_503_);
lean_dec(v___x_501_);
v___x_505_ = l_Std_Time_Duration_ofNanoseconds(v___x_504_);
lean_dec(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks___boxed(lean_object* v_t_506_, lean_object* v_d_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_Time_Timestamp_addWeeks(v_t_506_, v_d_507_);
lean_dec(v_d_507_);
lean_dec_ref(v_t_506_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks(lean_object* v_t_509_, lean_object* v_d_510_){
_start:
{
lean_object* v_second_511_; lean_object* v_nano_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_second_511_ = lean_ctor_get(v_t_509_, 0);
v_nano_512_ = lean_ctor_get(v_t_509_, 1);
v___x_513_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_514_ = lean_int_mul(v_d_510_, v___x_513_);
v___x_515_ = lean_obj_once(&l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_toDaysSinceUnixEpoch___closed__0);
v___x_516_ = lean_int_mul(v___x_514_, v___x_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_int_neg(v___x_516_);
lean_dec(v___x_516_);
v___x_518_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_519_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_520_ = lean_int_mul(v_second_511_, v___x_519_);
v___x_521_ = lean_int_add(v___x_520_, v_nano_512_);
lean_dec(v___x_520_);
v___x_522_ = lean_int_mul(v___x_517_, v___x_519_);
lean_dec(v___x_517_);
v___x_523_ = lean_int_add(v___x_522_, v___x_518_);
lean_dec(v___x_522_);
v___x_524_ = lean_int_add(v___x_521_, v___x_523_);
lean_dec(v___x_523_);
lean_dec(v___x_521_);
v___x_525_ = l_Std_Time_Duration_ofNanoseconds(v___x_524_);
lean_dec(v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks___boxed(lean_object* v_t_526_, lean_object* v_d_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Time_Timestamp_subWeeks(v_t_526_, v_d_527_);
lean_dec(v_d_527_);
lean_dec_ref(v_t_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration(lean_object* v_t_529_, lean_object* v_d_530_){
_start:
{
lean_object* v_second_531_; lean_object* v_nano_532_; lean_object* v_second_533_; lean_object* v_nano_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v_second_531_ = lean_ctor_get(v_t_529_, 0);
v_nano_532_ = lean_ctor_get(v_t_529_, 1);
v_second_533_ = lean_ctor_get(v_d_530_, 0);
v_nano_534_ = lean_ctor_get(v_d_530_, 1);
v___x_535_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_536_ = lean_int_mul(v_second_531_, v___x_535_);
v___x_537_ = lean_int_add(v___x_536_, v_nano_532_);
lean_dec(v___x_536_);
v___x_538_ = lean_int_mul(v_second_533_, v___x_535_);
v___x_539_ = lean_int_add(v___x_538_, v_nano_534_);
lean_dec(v___x_538_);
v___x_540_ = lean_int_add(v___x_537_, v___x_539_);
lean_dec(v___x_539_);
lean_dec(v___x_537_);
v___x_541_ = l_Std_Time_Duration_ofNanoseconds(v___x_540_);
lean_dec(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration___boxed(lean_object* v_t_542_, lean_object* v_d_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_Time_Timestamp_addDuration(v_t_542_, v_d_543_);
lean_dec_ref(v_d_543_);
lean_dec_ref(v_t_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration(lean_object* v_t_545_, lean_object* v_d_546_){
_start:
{
lean_object* v_second_547_; lean_object* v_nano_548_; lean_object* v_second_549_; lean_object* v_nano_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_second_547_ = lean_ctor_get(v_d_546_, 0);
v_nano_548_ = lean_ctor_get(v_d_546_, 1);
v_second_549_ = lean_ctor_get(v_t_545_, 0);
v_nano_550_ = lean_ctor_get(v_t_545_, 1);
v___x_551_ = lean_int_neg(v_second_547_);
v___x_552_ = lean_int_neg(v_nano_548_);
v___x_553_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_554_ = lean_int_mul(v_second_549_, v___x_553_);
v___x_555_ = lean_int_add(v___x_554_, v_nano_550_);
lean_dec(v___x_554_);
v___x_556_ = lean_int_mul(v___x_551_, v___x_553_);
lean_dec(v___x_551_);
v___x_557_ = lean_int_add(v___x_556_, v___x_552_);
lean_dec(v___x_552_);
lean_dec(v___x_556_);
v___x_558_ = lean_int_add(v___x_555_, v___x_557_);
lean_dec(v___x_557_);
lean_dec(v___x_555_);
v___x_559_ = l_Std_Time_Duration_ofNanoseconds(v___x_558_);
lean_dec(v___x_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration___boxed(lean_object* v_t_560_, lean_object* v_d_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_Time_Timestamp_subDuration(v_t_560_, v_d_561_);
lean_dec_ref(v_d_561_);
lean_dec_ref(v_t_560_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0(lean_object* v_x_595_, lean_object* v_y_596_){
_start:
{
lean_object* v_second_597_; lean_object* v_nano_598_; lean_object* v_second_599_; lean_object* v_nano_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_second_597_ = lean_ctor_get(v_y_596_, 0);
v_nano_598_ = lean_ctor_get(v_y_596_, 1);
v_second_599_ = lean_ctor_get(v_x_595_, 0);
v_nano_600_ = lean_ctor_get(v_x_595_, 1);
v___x_601_ = lean_int_neg(v_second_597_);
v___x_602_ = lean_int_neg(v_nano_598_);
v___x_603_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_604_ = lean_int_mul(v_second_599_, v___x_603_);
v___x_605_ = lean_int_add(v___x_604_, v_nano_600_);
lean_dec(v___x_604_);
v___x_606_ = lean_int_mul(v___x_601_, v___x_603_);
lean_dec(v___x_601_);
v___x_607_ = lean_int_add(v___x_606_, v___x_602_);
lean_dec(v___x_602_);
lean_dec(v___x_606_);
v___x_608_ = lean_int_add(v___x_605_, v___x_607_);
lean_dec(v___x_607_);
lean_dec(v___x_605_);
v___x_609_ = l_Std_Time_Duration_ofNanoseconds(v___x_608_);
lean_dec(v___x_608_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed(lean_object* v_x_610_, lean_object* v_y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_Time_Timestamp_instHSubDuration__1___lam__0(v_x_610_, v_y_611_);
lean_dec_ref(v_y_611_);
lean_dec_ref(v_x_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instOfNat(lean_object* v_n_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = lean_nat_to_int(v_n_615_);
v___x_617_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
return v___x_618_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Duration(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_WallTime(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_DateTime_Timestamp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

// Lean compiler output
// Module: Std.Time.DateTime.Timestamp
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t lean_int_dec_nonneg(lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
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
extern lean_object* l_Std_Time_instOrdDuration;
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLeTimestamp___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeTimestamp___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLeTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instLTTimestamp;
static lean_once_cell_t l_Std_Time_instDecidableLtTimestamp___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instDecidableLtTimestamp___aux__1___closed__0;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLtTimestamp___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtTimestamp___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLtTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOfNatTimestamp(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_instToStringTimestamp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instToStringTimestamp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instToStringTimestamp___closed__0 = (const lean_object*)&l_Std_Time_instToStringTimestamp___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instToStringTimestamp = (const lean_object*)&l_Std_Time_instToStringTimestamp___closed__0_value;
static const lean_string_object l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Timestamp.ofNanosecondsSinceUnixEpoch "};
static const lean_object* l_Std_Time_instReprTimestamp__1___lam__0___closed__0 = (const lean_object*)&l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprTimestamp__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimestamp__1___lam__0___closed__0_value)}};
static const lean_object* l_Std_Time_instReprTimestamp__1___lam__0___closed__1 = (const lean_object*)&l_Std_Time_instReprTimestamp__1___lam__0___closed__1_value;
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
static lean_once_cell_t l_Std_Time_Timestamp_toMinutes___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_toMinutes___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutes___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_toDays___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_toDays___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDays(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDays___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofSecondsSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch___boxed(lean_object*);
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
static lean_object* _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(1000000000u);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLeTimestamp___aux__1(lean_object* v_x_121_, lean_object* v_y_122_){
_start:
{
lean_object* v_second_123_; lean_object* v_nano_124_; lean_object* v_second_125_; lean_object* v_nano_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v_second_123_ = lean_ctor_get(v_y_122_, 0);
v_nano_124_ = lean_ctor_get(v_y_122_, 1);
v_second_125_ = lean_ctor_get(v_x_121_, 0);
v_nano_126_ = lean_ctor_get(v_x_121_, 1);
v___x_127_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_128_ = lean_int_mul(v_second_123_, v___x_127_);
v___x_129_ = lean_int_add(v___x_128_, v_nano_124_);
lean_dec(v___x_128_);
v___x_130_ = lean_int_mul(v_second_125_, v___x_127_);
v___x_131_ = lean_int_add(v___x_130_, v_nano_126_);
lean_dec(v___x_130_);
v___x_132_ = lean_int_sub(v___x_129_, v___x_131_);
lean_dec(v___x_131_);
lean_dec(v___x_129_);
v___x_133_ = lean_int_dec_nonneg(v___x_132_);
lean_dec(v___x_132_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeTimestamp___aux__1___boxed(lean_object* v_x_134_, lean_object* v_y_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Std_Time_instDecidableLeTimestamp___aux__1(v_x_134_, v_y_135_);
lean_dec_ref(v_y_135_);
lean_dec_ref(v_x_134_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLeTimestamp(lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
uint8_t v___x_140_; 
v___x_140_ = l_Std_Time_instDecidableLeTimestamp___aux__1(v___y_138_, v___y_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeTimestamp___boxed(lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Std_Time_instDecidableLeTimestamp(v___y_141_, v___y_142_);
lean_dec_ref(v___y_142_);
lean_dec_ref(v___y_141_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
static lean_object* _init_l_Std_Time_instLTTimestamp(void){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_box(0);
return v___x_145_;
}
}
static lean_object* _init_l_Std_Time_instDecidableLtTimestamp___aux__1___closed__0(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_to_int(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLtTimestamp___aux__1(lean_object* v_x_148_, lean_object* v_y_149_){
_start:
{
lean_object* v_second_150_; lean_object* v_nano_151_; lean_object* v_second_152_; lean_object* v_nano_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_second_150_ = lean_ctor_get(v_y_149_, 0);
v_nano_151_ = lean_ctor_get(v_y_149_, 1);
v_second_152_ = lean_ctor_get(v_x_148_, 0);
v_nano_153_ = lean_ctor_get(v_x_148_, 1);
v___x_154_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_155_ = lean_int_mul(v_second_150_, v___x_154_);
v___x_156_ = lean_int_add(v___x_155_, v_nano_151_);
lean_dec(v___x_155_);
v___x_157_ = lean_int_mul(v_second_152_, v___x_154_);
v___x_158_ = lean_int_add(v___x_157_, v_nano_153_);
lean_dec(v___x_157_);
v___x_159_ = lean_obj_once(&l_Std_Time_instDecidableLtTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLtTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLtTimestamp___aux__1___closed__0);
v___x_160_ = lean_int_add(v___x_158_, v___x_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_int_sub(v___x_156_, v___x_160_);
lean_dec(v___x_160_);
lean_dec(v___x_156_);
v___x_162_ = lean_int_dec_nonneg(v___x_161_);
lean_dec(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtTimestamp___aux__1___boxed(lean_object* v_x_163_, lean_object* v_y_164_){
_start:
{
uint8_t v_res_165_; lean_object* v_r_166_; 
v_res_165_ = l_Std_Time_instDecidableLtTimestamp___aux__1(v_x_163_, v_y_164_);
lean_dec_ref(v_y_164_);
lean_dec_ref(v_x_163_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLtTimestamp(lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
uint8_t v___x_169_; 
v___x_169_ = l_Std_Time_instDecidableLtTimestamp___aux__1(v___y_167_, v___y_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtTimestamp___boxed(lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Std_Time_instDecidableLtTimestamp(v___y_170_, v___y_171_);
lean_dec_ref(v___y_171_);
lean_dec_ref(v___y_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOfNatTimestamp(lean_object* v_n_174_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_nat_to_int(v_n_174_);
v___x_176_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_175_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0(lean_object* v_s_178_){
_start:
{
lean_object* v_second_179_; lean_object* v___x_180_; 
v_second_179_ = lean_ctor_get(v_s_178_, 0);
v___x_180_ = l_Int_repr(v_second_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0___boxed(lean_object* v_s_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Std_Time_instToStringTimestamp___lam__0(v_s_181_);
lean_dec_ref(v_s_181_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp__1___lam__0(lean_object* v_s_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_second_190_; lean_object* v_nano_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_205_; 
v_second_190_ = lean_ctor_get(v_s_188_, 0);
v_nano_191_ = lean_ctor_get(v_s_188_, 1);
v_isSharedCheck_205_ = !lean_is_exclusive(v_s_188_);
if (v_isSharedCheck_205_ == 0)
{
v___x_193_ = v_s_188_;
v_isShared_194_ = v_isSharedCheck_205_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_nano_191_);
lean_inc(v_second_190_);
lean_dec(v_s_188_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_205_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v_nanos_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_195_ = ((lean_object*)(l_Std_Time_instReprTimestamp__1___lam__0___closed__1));
v___x_196_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_197_ = lean_int_mul(v_second_190_, v___x_196_);
lean_dec(v_second_190_);
v_nanos_198_ = lean_int_add(v___x_197_, v_nano_191_);
lean_dec(v_nano_191_);
lean_dec(v___x_197_);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = l_Std_Time_Nanosecond_instReprOrdinal___lam__0(v_nanos_198_, v___x_199_);
lean_dec(v_nanos_198_);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 5);
lean_ctor_set(v___x_193_, 1, v___x_200_);
lean_ctor_set(v___x_193_, 0, v___x_195_);
v___x_202_ = v___x_193_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_200_);
v___x_202_ = v_reuseFailAlloc_204_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; 
v___x_203_ = l_Repr_addAppParen(v___x_202_, v___y_189_);
return v___x_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp__1___lam__0___boxed(lean_object* v_s_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Time_instReprTimestamp__1___lam__0(v_s_206_, v___y_207_);
lean_dec(v___y_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp___lam__0(lean_object* v_x_211_){
_start:
{
lean_inc_ref(v_x_211_);
return v_x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp___lam__0___boxed(lean_object* v_x_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Time_instOrdTimestamp___lam__0(v_x_212_);
lean_dec_ref(v_x_212_);
return v_res_213_;
}
}
static lean_object* _init_l_Std_Time_instOrdTimestamp___closed__1(void){
_start:
{
lean_object* v___f_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___f_215_ = ((lean_object*)(l_Std_Time_instOrdTimestamp___closed__0));
v___x_216_ = l_Std_Time_instOrdDuration;
v___x_217_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_217_, 0, lean_box(0));
lean_closure_set(v___x_217_, 1, lean_box(0));
lean_closure_set(v___x_217_, 2, v___x_216_);
lean_closure_set(v___x_217_, 3, v___f_215_);
return v___x_217_;
}
}
static lean_object* _init_l_Std_Time_instOrdTimestamp(void){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Std_Time_instOrdTimestamp___closed__1, &l_Std_Time_instOrdTimestamp___closed__1_once, _init_l_Std_Time_instOrdTimestamp___closed__1);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_now___boxed(lean_object* v_a_00___x40___internal___hyg_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = lean_get_current_time();
return v_res_221_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(60u);
v___x_223_ = lean_nat_to_int(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutes(lean_object* v_tm_224_){
_start:
{
lean_object* v_second_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_second_225_ = lean_ctor_get(v_tm_224_, 0);
v___x_226_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutes___closed__0, &l_Std_Time_Timestamp_toMinutes___closed__0_once, _init_l_Std_Time_Timestamp_toMinutes___closed__0);
v___x_227_ = lean_int_div(v_second_225_, v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutes___boxed(lean_object* v_tm_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Std_Time_Timestamp_toMinutes(v_tm_228_);
lean_dec_ref(v_tm_228_);
return v_res_229_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toDays___closed__0(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(86400u);
v___x_231_ = lean_nat_to_int(v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDays(lean_object* v_tm_232_){
_start:
{
lean_object* v_second_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_second_233_ = lean_ctor_get(v_tm_232_, 0);
v___x_234_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_235_ = lean_int_div(v_second_233_, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDays___boxed(lean_object* v_tm_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Std_Time_Timestamp_toDays(v_tm_236_);
lean_dec_ref(v_tm_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofSecondsSinceUnixEpoch(lean_object* v_secs_238_){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_240_, 0, v_secs_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(lean_object* v_nanos_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch___boxed(lean_object* v_nanos_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(v_nanos_243_);
lean_dec(v_nanos_243_);
return v_res_244_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(1000000u);
v___x_246_ = lean_nat_to_int(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(lean_object* v_milli_247_){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_248_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_249_ = lean_int_mul(v_milli_247_, v___x_248_);
v___x_250_ = l_Std_Time_Duration_ofNanoseconds(v___x_249_);
lean_dec(v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___boxed(lean_object* v_milli_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(v_milli_251_);
lean_dec(v_milli_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(lean_object* v_t_253_){
_start:
{
lean_object* v_second_254_; 
v_second_254_ = lean_ctor_get(v_t_253_, 0);
lean_inc(v_second_254_);
return v_second_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch___boxed(lean_object* v_t_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(v_t_255_);
lean_dec_ref(v_t_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(lean_object* v_tm_257_){
_start:
{
lean_object* v_second_258_; lean_object* v_nano_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v_nanos_262_; 
v_second_258_ = lean_ctor_get(v_tm_257_, 0);
v_nano_259_ = lean_ctor_get(v_tm_257_, 1);
v___x_260_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_261_ = lean_int_mul(v_second_258_, v___x_260_);
v_nanos_262_ = lean_int_add(v___x_261_, v_nano_259_);
lean_dec(v___x_261_);
return v_nanos_262_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch___boxed(lean_object* v_tm_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(v_tm_263_);
lean_dec_ref(v_tm_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(lean_object* v_tm_265_){
_start:
{
lean_object* v_second_266_; lean_object* v_nano_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_second_266_ = lean_ctor_get(v_tm_265_, 0);
v_nano_267_ = lean_ctor_get(v_tm_265_, 1);
v___x_268_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_269_ = lean_int_mul(v_second_266_, v___x_268_);
v___x_270_ = lean_int_add(v___x_269_, v_nano_267_);
lean_dec(v___x_269_);
v___x_271_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_272_ = lean_int_div(v___x_270_, v___x_271_);
lean_dec(v___x_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch___boxed(lean_object* v_tm_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(v_tm_273_);
lean_dec_ref(v_tm_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since(lean_object* v_f_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = lean_get_current_time();
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_298_; 
v_a_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_298_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_298_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_298_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v_second_282_; lean_object* v_nano_283_; lean_object* v_second_284_; lean_object* v_nano_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v_second_282_ = lean_ctor_get(v_f_275_, 0);
v_nano_283_ = lean_ctor_get(v_f_275_, 1);
v_second_284_ = lean_ctor_get(v_a_278_, 0);
lean_inc(v_second_284_);
v_nano_285_ = lean_ctor_get(v_a_278_, 1);
lean_inc(v_nano_285_);
lean_dec(v_a_278_);
v___x_286_ = lean_int_neg(v_second_282_);
v___x_287_ = lean_int_neg(v_nano_283_);
v___x_288_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_289_ = lean_int_mul(v_second_284_, v___x_288_);
lean_dec(v_second_284_);
v___x_290_ = lean_int_add(v___x_289_, v_nano_285_);
lean_dec(v_nano_285_);
lean_dec(v___x_289_);
v___x_291_ = lean_int_mul(v___x_286_, v___x_288_);
lean_dec(v___x_286_);
v___x_292_ = lean_int_add(v___x_291_, v___x_287_);
lean_dec(v___x_287_);
lean_dec(v___x_291_);
v___x_293_ = lean_int_add(v___x_290_, v___x_292_);
lean_dec(v___x_292_);
lean_dec(v___x_290_);
v___x_294_ = l_Std_Time_Duration_ofNanoseconds(v___x_293_);
lean_dec(v___x_293_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_294_);
v___x_296_ = v___x_280_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_a_299_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_277_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_277_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since___boxed(lean_object* v_f_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Std_Time_Timestamp_since(v_f_307_);
lean_dec_ref(v_f_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch(lean_object* v_tm_310_){
_start:
{
lean_inc_ref(v_tm_310_);
return v_tm_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch___boxed(lean_object* v_tm_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Std_Time_Timestamp_toDurationSinceUnixEpoch(v_tm_311_);
lean_dec_ref(v_tm_311_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds(lean_object* v_t_313_, lean_object* v_s_314_){
_start:
{
lean_object* v_second_315_; lean_object* v_nano_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_second_320_; lean_object* v_nano_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_second_315_ = lean_ctor_get(v_t_313_, 0);
v_nano_316_ = lean_ctor_get(v_t_313_, 1);
v___x_317_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_318_ = lean_int_mul(v_s_314_, v___x_317_);
v___x_319_ = l_Std_Time_Duration_ofNanoseconds(v___x_318_);
lean_dec(v___x_318_);
v_second_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_second_320_);
v_nano_321_ = lean_ctor_get(v___x_319_, 1);
lean_inc(v_nano_321_);
lean_dec_ref(v___x_319_);
v___x_322_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_323_ = lean_int_mul(v_second_315_, v___x_322_);
v___x_324_ = lean_int_add(v___x_323_, v_nano_316_);
lean_dec(v___x_323_);
v___x_325_ = lean_int_mul(v_second_320_, v___x_322_);
lean_dec(v_second_320_);
v___x_326_ = lean_int_add(v___x_325_, v_nano_321_);
lean_dec(v_nano_321_);
lean_dec(v___x_325_);
v___x_327_ = lean_int_add(v___x_324_, v___x_326_);
lean_dec(v___x_326_);
lean_dec(v___x_324_);
v___x_328_ = l_Std_Time_Duration_ofNanoseconds(v___x_327_);
lean_dec(v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds___boxed(lean_object* v_t_329_, lean_object* v_s_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_Time_Timestamp_addMilliseconds(v_t_329_, v_s_330_);
lean_dec(v_s_330_);
lean_dec_ref(v_t_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds(lean_object* v_t_332_, lean_object* v_s_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_second_337_; lean_object* v_nano_338_; lean_object* v_second_339_; lean_object* v_nano_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_334_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_335_ = lean_int_mul(v_s_333_, v___x_334_);
v___x_336_ = l_Std_Time_Duration_ofNanoseconds(v___x_335_);
lean_dec(v___x_335_);
v_second_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_second_337_);
v_nano_338_ = lean_ctor_get(v___x_336_, 1);
lean_inc(v_nano_338_);
lean_dec_ref(v___x_336_);
v_second_339_ = lean_ctor_get(v_t_332_, 0);
v_nano_340_ = lean_ctor_get(v_t_332_, 1);
v___x_341_ = lean_int_neg(v_second_337_);
lean_dec(v_second_337_);
v___x_342_ = lean_int_neg(v_nano_338_);
lean_dec(v_nano_338_);
v___x_343_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_344_ = lean_int_mul(v_second_339_, v___x_343_);
v___x_345_ = lean_int_add(v___x_344_, v_nano_340_);
lean_dec(v___x_344_);
v___x_346_ = lean_int_mul(v___x_341_, v___x_343_);
lean_dec(v___x_341_);
v___x_347_ = lean_int_add(v___x_346_, v___x_342_);
lean_dec(v___x_342_);
lean_dec(v___x_346_);
v___x_348_ = lean_int_add(v___x_345_, v___x_347_);
lean_dec(v___x_347_);
lean_dec(v___x_345_);
v___x_349_ = l_Std_Time_Duration_ofNanoseconds(v___x_348_);
lean_dec(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds___boxed(lean_object* v_t_350_, lean_object* v_s_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_Time_Timestamp_subMilliseconds(v_t_350_, v_s_351_);
lean_dec(v_s_351_);
lean_dec_ref(v_t_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds(lean_object* v_t_353_, lean_object* v_s_354_){
_start:
{
lean_object* v_second_355_; lean_object* v_nano_356_; lean_object* v___x_357_; lean_object* v_second_358_; lean_object* v_nano_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_second_355_ = lean_ctor_get(v_t_353_, 0);
v_nano_356_ = lean_ctor_get(v_t_353_, 1);
v___x_357_ = l_Std_Time_Duration_ofNanoseconds(v_s_354_);
v_second_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_second_358_);
v_nano_359_ = lean_ctor_get(v___x_357_, 1);
lean_inc(v_nano_359_);
lean_dec_ref(v___x_357_);
v___x_360_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_361_ = lean_int_mul(v_second_355_, v___x_360_);
v___x_362_ = lean_int_add(v___x_361_, v_nano_356_);
lean_dec(v___x_361_);
v___x_363_ = lean_int_mul(v_second_358_, v___x_360_);
lean_dec(v_second_358_);
v___x_364_ = lean_int_add(v___x_363_, v_nano_359_);
lean_dec(v_nano_359_);
lean_dec(v___x_363_);
v___x_365_ = lean_int_add(v___x_362_, v___x_364_);
lean_dec(v___x_364_);
lean_dec(v___x_362_);
v___x_366_ = l_Std_Time_Duration_ofNanoseconds(v___x_365_);
lean_dec(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds___boxed(lean_object* v_t_367_, lean_object* v_s_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Time_Timestamp_addNanoseconds(v_t_367_, v_s_368_);
lean_dec(v_s_368_);
lean_dec_ref(v_t_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds(lean_object* v_t_370_, lean_object* v_s_371_){
_start:
{
lean_object* v___x_372_; lean_object* v_second_373_; lean_object* v_nano_374_; lean_object* v_second_375_; lean_object* v_nano_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_372_ = l_Std_Time_Duration_ofNanoseconds(v_s_371_);
v_second_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_second_373_);
v_nano_374_ = lean_ctor_get(v___x_372_, 1);
lean_inc(v_nano_374_);
lean_dec_ref(v___x_372_);
v_second_375_ = lean_ctor_get(v_t_370_, 0);
v_nano_376_ = lean_ctor_get(v_t_370_, 1);
v___x_377_ = lean_int_neg(v_second_373_);
lean_dec(v_second_373_);
v___x_378_ = lean_int_neg(v_nano_374_);
lean_dec(v_nano_374_);
v___x_379_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_380_ = lean_int_mul(v_second_375_, v___x_379_);
v___x_381_ = lean_int_add(v___x_380_, v_nano_376_);
lean_dec(v___x_380_);
v___x_382_ = lean_int_mul(v___x_377_, v___x_379_);
lean_dec(v___x_377_);
v___x_383_ = lean_int_add(v___x_382_, v___x_378_);
lean_dec(v___x_378_);
lean_dec(v___x_382_);
v___x_384_ = lean_int_add(v___x_381_, v___x_383_);
lean_dec(v___x_383_);
lean_dec(v___x_381_);
v___x_385_ = l_Std_Time_Duration_ofNanoseconds(v___x_384_);
lean_dec(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds___boxed(lean_object* v_t_386_, lean_object* v_s_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_Time_Timestamp_subNanoseconds(v_t_386_, v_s_387_);
lean_dec(v_s_387_);
lean_dec_ref(v_t_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds(lean_object* v_t_389_, lean_object* v_s_390_){
_start:
{
lean_object* v_second_391_; lean_object* v_nano_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_second_391_ = lean_ctor_get(v_t_389_, 0);
v_nano_392_ = lean_ctor_get(v_t_389_, 1);
v___x_393_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_394_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_395_ = lean_int_mul(v_second_391_, v___x_394_);
v___x_396_ = lean_int_add(v___x_395_, v_nano_392_);
lean_dec(v___x_395_);
v___x_397_ = lean_int_mul(v_s_390_, v___x_394_);
v___x_398_ = lean_int_add(v___x_397_, v___x_393_);
lean_dec(v___x_397_);
v___x_399_ = lean_int_add(v___x_396_, v___x_398_);
lean_dec(v___x_398_);
lean_dec(v___x_396_);
v___x_400_ = l_Std_Time_Duration_ofNanoseconds(v___x_399_);
lean_dec(v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds___boxed(lean_object* v_t_401_, lean_object* v_s_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Std_Time_Timestamp_addSeconds(v_t_401_, v_s_402_);
lean_dec(v_s_402_);
lean_dec_ref(v_t_401_);
return v_res_403_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_subSeconds___closed__0(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_405_ = lean_int_neg(v___x_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds(lean_object* v_t_406_, lean_object* v_s_407_){
_start:
{
lean_object* v_second_408_; lean_object* v_nano_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_second_408_ = lean_ctor_get(v_t_406_, 0);
v_nano_409_ = lean_ctor_get(v_t_406_, 1);
v___x_410_ = lean_int_neg(v_s_407_);
v___x_411_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_412_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_413_ = lean_int_mul(v_second_408_, v___x_412_);
v___x_414_ = lean_int_add(v___x_413_, v_nano_409_);
lean_dec(v___x_413_);
v___x_415_ = lean_int_mul(v___x_410_, v___x_412_);
lean_dec(v___x_410_);
v___x_416_ = lean_int_add(v___x_415_, v___x_411_);
lean_dec(v___x_415_);
v___x_417_ = lean_int_add(v___x_414_, v___x_416_);
lean_dec(v___x_416_);
lean_dec(v___x_414_);
v___x_418_ = l_Std_Time_Duration_ofNanoseconds(v___x_417_);
lean_dec(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds___boxed(lean_object* v_t_419_, lean_object* v_s_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_Time_Timestamp_subSeconds(v_t_419_, v_s_420_);
lean_dec(v_s_420_);
lean_dec_ref(v_t_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes(lean_object* v_t_422_, lean_object* v_m_423_){
_start:
{
lean_object* v_second_424_; lean_object* v_nano_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_second_424_ = lean_ctor_get(v_t_422_, 0);
v_nano_425_ = lean_ctor_get(v_t_422_, 1);
v___x_426_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutes___closed__0, &l_Std_Time_Timestamp_toMinutes___closed__0_once, _init_l_Std_Time_Timestamp_toMinutes___closed__0);
v___x_427_ = lean_int_mul(v_m_423_, v___x_426_);
v___x_428_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_429_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_430_ = lean_int_mul(v_second_424_, v___x_429_);
v___x_431_ = lean_int_add(v___x_430_, v_nano_425_);
lean_dec(v___x_430_);
v___x_432_ = lean_int_mul(v___x_427_, v___x_429_);
lean_dec(v___x_427_);
v___x_433_ = lean_int_add(v___x_432_, v___x_428_);
lean_dec(v___x_432_);
v___x_434_ = lean_int_add(v___x_431_, v___x_433_);
lean_dec(v___x_433_);
lean_dec(v___x_431_);
v___x_435_ = l_Std_Time_Duration_ofNanoseconds(v___x_434_);
lean_dec(v___x_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes___boxed(lean_object* v_t_436_, lean_object* v_m_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_Time_Timestamp_addMinutes(v_t_436_, v_m_437_);
lean_dec(v_m_437_);
lean_dec_ref(v_t_436_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes(lean_object* v_t_439_, lean_object* v_m_440_){
_start:
{
lean_object* v_second_441_; lean_object* v_nano_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_second_441_ = lean_ctor_get(v_t_439_, 0);
v_nano_442_ = lean_ctor_get(v_t_439_, 1);
v___x_443_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutes___closed__0, &l_Std_Time_Timestamp_toMinutes___closed__0_once, _init_l_Std_Time_Timestamp_toMinutes___closed__0);
v___x_444_ = lean_int_mul(v_m_440_, v___x_443_);
v___x_445_ = lean_int_neg(v___x_444_);
lean_dec(v___x_444_);
v___x_446_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_447_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_448_ = lean_int_mul(v_second_441_, v___x_447_);
v___x_449_ = lean_int_add(v___x_448_, v_nano_442_);
lean_dec(v___x_448_);
v___x_450_ = lean_int_mul(v___x_445_, v___x_447_);
lean_dec(v___x_445_);
v___x_451_ = lean_int_add(v___x_450_, v___x_446_);
lean_dec(v___x_450_);
v___x_452_ = lean_int_add(v___x_449_, v___x_451_);
lean_dec(v___x_451_);
lean_dec(v___x_449_);
v___x_453_ = l_Std_Time_Duration_ofNanoseconds(v___x_452_);
lean_dec(v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes___boxed(lean_object* v_t_454_, lean_object* v_m_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_Time_Timestamp_subMinutes(v_t_454_, v_m_455_);
lean_dec(v_m_455_);
lean_dec_ref(v_t_454_);
return v_res_456_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_addHours___closed__0(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_unsigned_to_nat(3600u);
v___x_458_ = lean_nat_to_int(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours(lean_object* v_t_459_, lean_object* v_h_460_){
_start:
{
lean_object* v_second_461_; lean_object* v_nano_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_second_461_ = lean_ctor_get(v_t_459_, 0);
v_nano_462_ = lean_ctor_get(v_t_459_, 1);
v___x_463_ = lean_obj_once(&l_Std_Time_Timestamp_addHours___closed__0, &l_Std_Time_Timestamp_addHours___closed__0_once, _init_l_Std_Time_Timestamp_addHours___closed__0);
v___x_464_ = lean_int_mul(v_h_460_, v___x_463_);
v___x_465_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_466_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_467_ = lean_int_mul(v_second_461_, v___x_466_);
v___x_468_ = lean_int_add(v___x_467_, v_nano_462_);
lean_dec(v___x_467_);
v___x_469_ = lean_int_mul(v___x_464_, v___x_466_);
lean_dec(v___x_464_);
v___x_470_ = lean_int_add(v___x_469_, v___x_465_);
lean_dec(v___x_469_);
v___x_471_ = lean_int_add(v___x_468_, v___x_470_);
lean_dec(v___x_470_);
lean_dec(v___x_468_);
v___x_472_ = l_Std_Time_Duration_ofNanoseconds(v___x_471_);
lean_dec(v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours___boxed(lean_object* v_t_473_, lean_object* v_h_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_Time_Timestamp_addHours(v_t_473_, v_h_474_);
lean_dec(v_h_474_);
lean_dec_ref(v_t_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours(lean_object* v_t_476_, lean_object* v_h_477_){
_start:
{
lean_object* v_second_478_; lean_object* v_nano_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_second_478_ = lean_ctor_get(v_t_476_, 0);
v_nano_479_ = lean_ctor_get(v_t_476_, 1);
v___x_480_ = lean_obj_once(&l_Std_Time_Timestamp_addHours___closed__0, &l_Std_Time_Timestamp_addHours___closed__0_once, _init_l_Std_Time_Timestamp_addHours___closed__0);
v___x_481_ = lean_int_mul(v_h_477_, v___x_480_);
v___x_482_ = lean_int_neg(v___x_481_);
lean_dec(v___x_481_);
v___x_483_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_484_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_485_ = lean_int_mul(v_second_478_, v___x_484_);
v___x_486_ = lean_int_add(v___x_485_, v_nano_479_);
lean_dec(v___x_485_);
v___x_487_ = lean_int_mul(v___x_482_, v___x_484_);
lean_dec(v___x_482_);
v___x_488_ = lean_int_add(v___x_487_, v___x_483_);
lean_dec(v___x_487_);
v___x_489_ = lean_int_add(v___x_486_, v___x_488_);
lean_dec(v___x_488_);
lean_dec(v___x_486_);
v___x_490_ = l_Std_Time_Duration_ofNanoseconds(v___x_489_);
lean_dec(v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours___boxed(lean_object* v_t_491_, lean_object* v_h_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_Time_Timestamp_subHours(v_t_491_, v_h_492_);
lean_dec(v_h_492_);
lean_dec_ref(v_t_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays(lean_object* v_t_494_, lean_object* v_d_495_){
_start:
{
lean_object* v_second_496_; lean_object* v_nano_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_second_496_ = lean_ctor_get(v_t_494_, 0);
v_nano_497_ = lean_ctor_get(v_t_494_, 1);
v___x_498_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_499_ = lean_int_mul(v_d_495_, v___x_498_);
v___x_500_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_501_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_502_ = lean_int_mul(v_second_496_, v___x_501_);
v___x_503_ = lean_int_add(v___x_502_, v_nano_497_);
lean_dec(v___x_502_);
v___x_504_ = lean_int_mul(v___x_499_, v___x_501_);
lean_dec(v___x_499_);
v___x_505_ = lean_int_add(v___x_504_, v___x_500_);
lean_dec(v___x_504_);
v___x_506_ = lean_int_add(v___x_503_, v___x_505_);
lean_dec(v___x_505_);
lean_dec(v___x_503_);
v___x_507_ = l_Std_Time_Duration_ofNanoseconds(v___x_506_);
lean_dec(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays___boxed(lean_object* v_t_508_, lean_object* v_d_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_Time_Timestamp_addDays(v_t_508_, v_d_509_);
lean_dec(v_d_509_);
lean_dec_ref(v_t_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays(lean_object* v_t_511_, lean_object* v_d_512_){
_start:
{
lean_object* v_second_513_; lean_object* v_nano_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_second_513_ = lean_ctor_get(v_t_511_, 0);
v_nano_514_ = lean_ctor_get(v_t_511_, 1);
v___x_515_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_516_ = lean_int_mul(v_d_512_, v___x_515_);
v___x_517_ = lean_int_neg(v___x_516_);
lean_dec(v___x_516_);
v___x_518_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_519_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_520_ = lean_int_mul(v_second_513_, v___x_519_);
v___x_521_ = lean_int_add(v___x_520_, v_nano_514_);
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
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays___boxed(lean_object* v_t_526_, lean_object* v_d_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Std_Time_Timestamp_subDays(v_t_526_, v_d_527_);
lean_dec(v_d_527_);
lean_dec_ref(v_t_526_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks(lean_object* v_t_529_, lean_object* v_d_530_){
_start:
{
lean_object* v_second_531_; lean_object* v_nano_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v_second_531_ = lean_ctor_get(v_t_529_, 0);
v_nano_532_ = lean_ctor_get(v_t_529_, 1);
v___x_533_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_534_ = lean_int_mul(v_d_530_, v___x_533_);
v___x_535_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_536_ = lean_int_mul(v___x_534_, v___x_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_538_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_539_ = lean_int_mul(v_second_531_, v___x_538_);
v___x_540_ = lean_int_add(v___x_539_, v_nano_532_);
lean_dec(v___x_539_);
v___x_541_ = lean_int_mul(v___x_536_, v___x_538_);
lean_dec(v___x_536_);
v___x_542_ = lean_int_add(v___x_541_, v___x_537_);
lean_dec(v___x_541_);
v___x_543_ = lean_int_add(v___x_540_, v___x_542_);
lean_dec(v___x_542_);
lean_dec(v___x_540_);
v___x_544_ = l_Std_Time_Duration_ofNanoseconds(v___x_543_);
lean_dec(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks___boxed(lean_object* v_t_545_, lean_object* v_d_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_Time_Timestamp_addWeeks(v_t_545_, v_d_546_);
lean_dec(v_d_546_);
lean_dec_ref(v_t_545_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks(lean_object* v_t_548_, lean_object* v_d_549_){
_start:
{
lean_object* v_second_550_; lean_object* v_nano_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_second_550_ = lean_ctor_get(v_t_548_, 0);
v_nano_551_ = lean_ctor_get(v_t_548_, 1);
v___x_552_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_553_ = lean_int_mul(v_d_549_, v___x_552_);
v___x_554_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_555_ = lean_int_mul(v___x_553_, v___x_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_int_neg(v___x_555_);
lean_dec(v___x_555_);
v___x_557_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_558_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_559_ = lean_int_mul(v_second_550_, v___x_558_);
v___x_560_ = lean_int_add(v___x_559_, v_nano_551_);
lean_dec(v___x_559_);
v___x_561_ = lean_int_mul(v___x_556_, v___x_558_);
lean_dec(v___x_556_);
v___x_562_ = lean_int_add(v___x_561_, v___x_557_);
lean_dec(v___x_561_);
v___x_563_ = lean_int_add(v___x_560_, v___x_562_);
lean_dec(v___x_562_);
lean_dec(v___x_560_);
v___x_564_ = l_Std_Time_Duration_ofNanoseconds(v___x_563_);
lean_dec(v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks___boxed(lean_object* v_t_565_, lean_object* v_d_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_Time_Timestamp_subWeeks(v_t_565_, v_d_566_);
lean_dec(v_d_566_);
lean_dec_ref(v_t_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration(lean_object* v_t_568_, lean_object* v_d_569_){
_start:
{
lean_object* v_second_570_; lean_object* v_nano_571_; lean_object* v_second_572_; lean_object* v_nano_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_second_570_ = lean_ctor_get(v_t_568_, 0);
v_nano_571_ = lean_ctor_get(v_t_568_, 1);
v_second_572_ = lean_ctor_get(v_d_569_, 0);
v_nano_573_ = lean_ctor_get(v_d_569_, 1);
v___x_574_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_575_ = lean_int_mul(v_second_570_, v___x_574_);
v___x_576_ = lean_int_add(v___x_575_, v_nano_571_);
lean_dec(v___x_575_);
v___x_577_ = lean_int_mul(v_second_572_, v___x_574_);
v___x_578_ = lean_int_add(v___x_577_, v_nano_573_);
lean_dec(v___x_577_);
v___x_579_ = lean_int_add(v___x_576_, v___x_578_);
lean_dec(v___x_578_);
lean_dec(v___x_576_);
v___x_580_ = l_Std_Time_Duration_ofNanoseconds(v___x_579_);
lean_dec(v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration___boxed(lean_object* v_t_581_, lean_object* v_d_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Std_Time_Timestamp_addDuration(v_t_581_, v_d_582_);
lean_dec_ref(v_d_582_);
lean_dec_ref(v_t_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration(lean_object* v_t_584_, lean_object* v_d_585_){
_start:
{
lean_object* v_second_586_; lean_object* v_nano_587_; lean_object* v_second_588_; lean_object* v_nano_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_second_586_ = lean_ctor_get(v_d_585_, 0);
v_nano_587_ = lean_ctor_get(v_d_585_, 1);
v_second_588_ = lean_ctor_get(v_t_584_, 0);
v_nano_589_ = lean_ctor_get(v_t_584_, 1);
v___x_590_ = lean_int_neg(v_second_586_);
v___x_591_ = lean_int_neg(v_nano_587_);
v___x_592_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_593_ = lean_int_mul(v_second_588_, v___x_592_);
v___x_594_ = lean_int_add(v___x_593_, v_nano_589_);
lean_dec(v___x_593_);
v___x_595_ = lean_int_mul(v___x_590_, v___x_592_);
lean_dec(v___x_590_);
v___x_596_ = lean_int_add(v___x_595_, v___x_591_);
lean_dec(v___x_591_);
lean_dec(v___x_595_);
v___x_597_ = lean_int_add(v___x_594_, v___x_596_);
lean_dec(v___x_596_);
lean_dec(v___x_594_);
v___x_598_ = l_Std_Time_Duration_ofNanoseconds(v___x_597_);
lean_dec(v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration___boxed(lean_object* v_t_599_, lean_object* v_d_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_Time_Timestamp_subDuration(v_t_599_, v_d_600_);
lean_dec_ref(v_d_600_);
lean_dec_ref(v_t_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0(lean_object* v_x_634_, lean_object* v_y_635_){
_start:
{
lean_object* v_second_636_; lean_object* v_nano_637_; lean_object* v_second_638_; lean_object* v_nano_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_second_636_ = lean_ctor_get(v_y_635_, 0);
v_nano_637_ = lean_ctor_get(v_y_635_, 1);
v_second_638_ = lean_ctor_get(v_x_634_, 0);
v_nano_639_ = lean_ctor_get(v_x_634_, 1);
v___x_640_ = lean_int_neg(v_second_636_);
v___x_641_ = lean_int_neg(v_nano_637_);
v___x_642_ = lean_obj_once(&l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0, &l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0_once, _init_l_Std_Time_instDecidableLeTimestamp___aux__1___closed__0);
v___x_643_ = lean_int_mul(v_second_638_, v___x_642_);
v___x_644_ = lean_int_add(v___x_643_, v_nano_639_);
lean_dec(v___x_643_);
v___x_645_ = lean_int_mul(v___x_640_, v___x_642_);
lean_dec(v___x_640_);
v___x_646_ = lean_int_add(v___x_645_, v___x_641_);
lean_dec(v___x_641_);
lean_dec(v___x_645_);
v___x_647_ = lean_int_add(v___x_644_, v___x_646_);
lean_dec(v___x_646_);
lean_dec(v___x_644_);
v___x_648_ = l_Std_Time_Duration_ofNanoseconds(v___x_647_);
lean_dec(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed(lean_object* v_x_649_, lean_object* v_y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_Time_Timestamp_instHSubDuration__1___lam__0(v_x_649_, v_y_650_);
lean_dec_ref(v_y_650_);
lean_dec_ref(v_x_649_);
return v_res_651_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_Duration(uint8_t builtin);
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

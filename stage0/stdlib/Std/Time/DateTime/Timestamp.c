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
uint8_t l_Std_Time_Duration_instDecidableLt(lean_object*, lean_object*);
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
uint8_t l_Std_Time_Duration_instDecidableLe(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLeTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instLTTimestamp;
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
LEAN_EXPORT lean_object* l_Std_Time_instOfNatTimestamp(lean_object* v_n_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_135_ = lean_nat_to_int(v_n_134_);
v___x_136_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
return v___x_137_;
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
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_now___boxed(lean_object* v_a_00___x40___internal___hyg_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = lean_get_current_time();
return v_res_183_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(60u);
v___x_185_ = lean_nat_to_int(v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutes(lean_object* v_tm_186_){
_start:
{
lean_object* v_second_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_second_187_ = lean_ctor_get(v_tm_186_, 0);
v___x_188_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutes___closed__0, &l_Std_Time_Timestamp_toMinutes___closed__0_once, _init_l_Std_Time_Timestamp_toMinutes___closed__0);
v___x_189_ = lean_int_div(v_second_187_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutes___boxed(lean_object* v_tm_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Std_Time_Timestamp_toMinutes(v_tm_190_);
lean_dec_ref(v_tm_190_);
return v_res_191_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toDays___closed__0(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(86400u);
v___x_193_ = lean_nat_to_int(v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDays(lean_object* v_tm_194_){
_start:
{
lean_object* v_second_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_second_195_ = lean_ctor_get(v_tm_194_, 0);
v___x_196_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_197_ = lean_int_div(v_second_195_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDays___boxed(lean_object* v_tm_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Std_Time_Timestamp_toDays(v_tm_198_);
lean_dec_ref(v_tm_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofSecondsSinceUnixEpoch(lean_object* v_secs_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_secs_200_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(lean_object* v_nanos_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch___boxed(lean_object* v_nanos_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(v_nanos_205_);
lean_dec(v_nanos_205_);
return v_res_206_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_unsigned_to_nat(1000000u);
v___x_208_ = lean_nat_to_int(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(lean_object* v_milli_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_211_ = lean_int_mul(v_milli_209_, v___x_210_);
v___x_212_ = l_Std_Time_Duration_ofNanoseconds(v___x_211_);
lean_dec(v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___boxed(lean_object* v_milli_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(v_milli_213_);
lean_dec(v_milli_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(lean_object* v_t_215_){
_start:
{
lean_object* v_second_216_; 
v_second_216_ = lean_ctor_get(v_t_215_, 0);
lean_inc(v_second_216_);
return v_second_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch___boxed(lean_object* v_t_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(v_t_217_);
lean_dec_ref(v_t_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(lean_object* v_tm_219_){
_start:
{
lean_object* v_second_220_; lean_object* v_nano_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_nanos_224_; 
v_second_220_ = lean_ctor_get(v_tm_219_, 0);
v_nano_221_ = lean_ctor_get(v_tm_219_, 1);
v___x_222_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_223_ = lean_int_mul(v_second_220_, v___x_222_);
v_nanos_224_ = lean_int_add(v___x_223_, v_nano_221_);
lean_dec(v___x_223_);
return v_nanos_224_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch___boxed(lean_object* v_tm_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(v_tm_225_);
lean_dec_ref(v_tm_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(lean_object* v_tm_227_){
_start:
{
lean_object* v_second_228_; lean_object* v_nano_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_second_228_ = lean_ctor_get(v_tm_227_, 0);
v_nano_229_ = lean_ctor_get(v_tm_227_, 1);
v___x_230_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_231_ = lean_int_mul(v_second_228_, v___x_230_);
v___x_232_ = lean_int_add(v___x_231_, v_nano_229_);
lean_dec(v___x_231_);
v___x_233_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_234_ = lean_int_div(v___x_232_, v___x_233_);
lean_dec(v___x_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch___boxed(lean_object* v_tm_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(v_tm_235_);
lean_dec_ref(v_tm_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since(lean_object* v_f_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = lean_get_current_time();
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_260_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_260_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_260_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_260_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_second_244_; lean_object* v_nano_245_; lean_object* v_second_246_; lean_object* v_nano_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v_second_244_ = lean_ctor_get(v_f_237_, 0);
v_nano_245_ = lean_ctor_get(v_f_237_, 1);
v_second_246_ = lean_ctor_get(v_a_240_, 0);
lean_inc(v_second_246_);
v_nano_247_ = lean_ctor_get(v_a_240_, 1);
lean_inc(v_nano_247_);
lean_dec(v_a_240_);
v___x_248_ = lean_int_neg(v_second_244_);
v___x_249_ = lean_int_neg(v_nano_245_);
v___x_250_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_251_ = lean_int_mul(v_second_246_, v___x_250_);
lean_dec(v_second_246_);
v___x_252_ = lean_int_add(v___x_251_, v_nano_247_);
lean_dec(v_nano_247_);
lean_dec(v___x_251_);
v___x_253_ = lean_int_mul(v___x_248_, v___x_250_);
lean_dec(v___x_248_);
v___x_254_ = lean_int_add(v___x_253_, v___x_249_);
lean_dec(v___x_249_);
lean_dec(v___x_253_);
v___x_255_ = lean_int_add(v___x_252_, v___x_254_);
lean_dec(v___x_254_);
lean_dec(v___x_252_);
v___x_256_ = l_Std_Time_Duration_ofNanoseconds(v___x_255_);
lean_dec(v___x_255_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_256_);
v___x_258_ = v___x_242_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_239_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_239_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since___boxed(lean_object* v_f_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_Time_Timestamp_since(v_f_269_);
lean_dec_ref(v_f_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch(lean_object* v_tm_272_){
_start:
{
lean_inc_ref(v_tm_272_);
return v_tm_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch___boxed(lean_object* v_tm_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_Time_Timestamp_toDurationSinceUnixEpoch(v_tm_273_);
lean_dec_ref(v_tm_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds(lean_object* v_t_275_, lean_object* v_s_276_){
_start:
{
lean_object* v_second_277_; lean_object* v_nano_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v_second_282_; lean_object* v_nano_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_second_277_ = lean_ctor_get(v_t_275_, 0);
v_nano_278_ = lean_ctor_get(v_t_275_, 1);
v___x_279_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_280_ = lean_int_mul(v_s_276_, v___x_279_);
v___x_281_ = l_Std_Time_Duration_ofNanoseconds(v___x_280_);
lean_dec(v___x_280_);
v_second_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_second_282_);
v_nano_283_ = lean_ctor_get(v___x_281_, 1);
lean_inc(v_nano_283_);
lean_dec_ref(v___x_281_);
v___x_284_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_285_ = lean_int_mul(v_second_277_, v___x_284_);
v___x_286_ = lean_int_add(v___x_285_, v_nano_278_);
lean_dec(v___x_285_);
v___x_287_ = lean_int_mul(v_second_282_, v___x_284_);
lean_dec(v_second_282_);
v___x_288_ = lean_int_add(v___x_287_, v_nano_283_);
lean_dec(v_nano_283_);
lean_dec(v___x_287_);
v___x_289_ = lean_int_add(v___x_286_, v___x_288_);
lean_dec(v___x_288_);
lean_dec(v___x_286_);
v___x_290_ = l_Std_Time_Duration_ofNanoseconds(v___x_289_);
lean_dec(v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds___boxed(lean_object* v_t_291_, lean_object* v_s_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Std_Time_Timestamp_addMilliseconds(v_t_291_, v_s_292_);
lean_dec(v_s_292_);
lean_dec_ref(v_t_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds(lean_object* v_t_294_, lean_object* v_s_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_second_299_; lean_object* v_nano_300_; lean_object* v_second_301_; lean_object* v_nano_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_296_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_297_ = lean_int_mul(v_s_295_, v___x_296_);
v___x_298_ = l_Std_Time_Duration_ofNanoseconds(v___x_297_);
lean_dec(v___x_297_);
v_second_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_second_299_);
v_nano_300_ = lean_ctor_get(v___x_298_, 1);
lean_inc(v_nano_300_);
lean_dec_ref(v___x_298_);
v_second_301_ = lean_ctor_get(v_t_294_, 0);
v_nano_302_ = lean_ctor_get(v_t_294_, 1);
v___x_303_ = lean_int_neg(v_second_299_);
lean_dec(v_second_299_);
v___x_304_ = lean_int_neg(v_nano_300_);
lean_dec(v_nano_300_);
v___x_305_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_306_ = lean_int_mul(v_second_301_, v___x_305_);
v___x_307_ = lean_int_add(v___x_306_, v_nano_302_);
lean_dec(v___x_306_);
v___x_308_ = lean_int_mul(v___x_303_, v___x_305_);
lean_dec(v___x_303_);
v___x_309_ = lean_int_add(v___x_308_, v___x_304_);
lean_dec(v___x_304_);
lean_dec(v___x_308_);
v___x_310_ = lean_int_add(v___x_307_, v___x_309_);
lean_dec(v___x_309_);
lean_dec(v___x_307_);
v___x_311_ = l_Std_Time_Duration_ofNanoseconds(v___x_310_);
lean_dec(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds___boxed(lean_object* v_t_312_, lean_object* v_s_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_Time_Timestamp_subMilliseconds(v_t_312_, v_s_313_);
lean_dec(v_s_313_);
lean_dec_ref(v_t_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds(lean_object* v_t_315_, lean_object* v_s_316_){
_start:
{
lean_object* v_second_317_; lean_object* v_nano_318_; lean_object* v___x_319_; lean_object* v_second_320_; lean_object* v_nano_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_second_317_ = lean_ctor_get(v_t_315_, 0);
v_nano_318_ = lean_ctor_get(v_t_315_, 1);
v___x_319_ = l_Std_Time_Duration_ofNanoseconds(v_s_316_);
v_second_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_second_320_);
v_nano_321_ = lean_ctor_get(v___x_319_, 1);
lean_inc(v_nano_321_);
lean_dec_ref(v___x_319_);
v___x_322_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_323_ = lean_int_mul(v_second_317_, v___x_322_);
v___x_324_ = lean_int_add(v___x_323_, v_nano_318_);
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
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds___boxed(lean_object* v_t_329_, lean_object* v_s_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_Time_Timestamp_addNanoseconds(v_t_329_, v_s_330_);
lean_dec(v_s_330_);
lean_dec_ref(v_t_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds(lean_object* v_t_332_, lean_object* v_s_333_){
_start:
{
lean_object* v___x_334_; lean_object* v_second_335_; lean_object* v_nano_336_; lean_object* v_second_337_; lean_object* v_nano_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_334_ = l_Std_Time_Duration_ofNanoseconds(v_s_333_);
v_second_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_second_335_);
v_nano_336_ = lean_ctor_get(v___x_334_, 1);
lean_inc(v_nano_336_);
lean_dec_ref(v___x_334_);
v_second_337_ = lean_ctor_get(v_t_332_, 0);
v_nano_338_ = lean_ctor_get(v_t_332_, 1);
v___x_339_ = lean_int_neg(v_second_335_);
lean_dec(v_second_335_);
v___x_340_ = lean_int_neg(v_nano_336_);
lean_dec(v_nano_336_);
v___x_341_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_342_ = lean_int_mul(v_second_337_, v___x_341_);
v___x_343_ = lean_int_add(v___x_342_, v_nano_338_);
lean_dec(v___x_342_);
v___x_344_ = lean_int_mul(v___x_339_, v___x_341_);
lean_dec(v___x_339_);
v___x_345_ = lean_int_add(v___x_344_, v___x_340_);
lean_dec(v___x_340_);
lean_dec(v___x_344_);
v___x_346_ = lean_int_add(v___x_343_, v___x_345_);
lean_dec(v___x_345_);
lean_dec(v___x_343_);
v___x_347_ = l_Std_Time_Duration_ofNanoseconds(v___x_346_);
lean_dec(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds___boxed(lean_object* v_t_348_, lean_object* v_s_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Time_Timestamp_subNanoseconds(v_t_348_, v_s_349_);
lean_dec(v_s_349_);
lean_dec_ref(v_t_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds(lean_object* v_t_351_, lean_object* v_s_352_){
_start:
{
lean_object* v_second_353_; lean_object* v_nano_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_second_353_ = lean_ctor_get(v_t_351_, 0);
v_nano_354_ = lean_ctor_get(v_t_351_, 1);
v___x_355_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_356_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_357_ = lean_int_mul(v_second_353_, v___x_356_);
v___x_358_ = lean_int_add(v___x_357_, v_nano_354_);
lean_dec(v___x_357_);
v___x_359_ = lean_int_mul(v_s_352_, v___x_356_);
v___x_360_ = lean_int_add(v___x_359_, v___x_355_);
lean_dec(v___x_359_);
v___x_361_ = lean_int_add(v___x_358_, v___x_360_);
lean_dec(v___x_360_);
lean_dec(v___x_358_);
v___x_362_ = l_Std_Time_Duration_ofNanoseconds(v___x_361_);
lean_dec(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds___boxed(lean_object* v_t_363_, lean_object* v_s_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Std_Time_Timestamp_addSeconds(v_t_363_, v_s_364_);
lean_dec(v_s_364_);
lean_dec_ref(v_t_363_);
return v_res_365_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_subSeconds___closed__0(void){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_367_ = lean_int_neg(v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds(lean_object* v_t_368_, lean_object* v_s_369_){
_start:
{
lean_object* v_second_370_; lean_object* v_nano_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_second_370_ = lean_ctor_get(v_t_368_, 0);
v_nano_371_ = lean_ctor_get(v_t_368_, 1);
v___x_372_ = lean_int_neg(v_s_369_);
v___x_373_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_374_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_375_ = lean_int_mul(v_second_370_, v___x_374_);
v___x_376_ = lean_int_add(v___x_375_, v_nano_371_);
lean_dec(v___x_375_);
v___x_377_ = lean_int_mul(v___x_372_, v___x_374_);
lean_dec(v___x_372_);
v___x_378_ = lean_int_add(v___x_377_, v___x_373_);
lean_dec(v___x_377_);
v___x_379_ = lean_int_add(v___x_376_, v___x_378_);
lean_dec(v___x_378_);
lean_dec(v___x_376_);
v___x_380_ = l_Std_Time_Duration_ofNanoseconds(v___x_379_);
lean_dec(v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds___boxed(lean_object* v_t_381_, lean_object* v_s_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Time_Timestamp_subSeconds(v_t_381_, v_s_382_);
lean_dec(v_s_382_);
lean_dec_ref(v_t_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes(lean_object* v_t_384_, lean_object* v_m_385_){
_start:
{
lean_object* v_second_386_; lean_object* v_nano_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_second_386_ = lean_ctor_get(v_t_384_, 0);
v_nano_387_ = lean_ctor_get(v_t_384_, 1);
v___x_388_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutes___closed__0, &l_Std_Time_Timestamp_toMinutes___closed__0_once, _init_l_Std_Time_Timestamp_toMinutes___closed__0);
v___x_389_ = lean_int_mul(v_m_385_, v___x_388_);
v___x_390_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_391_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_392_ = lean_int_mul(v_second_386_, v___x_391_);
v___x_393_ = lean_int_add(v___x_392_, v_nano_387_);
lean_dec(v___x_392_);
v___x_394_ = lean_int_mul(v___x_389_, v___x_391_);
lean_dec(v___x_389_);
v___x_395_ = lean_int_add(v___x_394_, v___x_390_);
lean_dec(v___x_394_);
v___x_396_ = lean_int_add(v___x_393_, v___x_395_);
lean_dec(v___x_395_);
lean_dec(v___x_393_);
v___x_397_ = l_Std_Time_Duration_ofNanoseconds(v___x_396_);
lean_dec(v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes___boxed(lean_object* v_t_398_, lean_object* v_m_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Std_Time_Timestamp_addMinutes(v_t_398_, v_m_399_);
lean_dec(v_m_399_);
lean_dec_ref(v_t_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes(lean_object* v_t_401_, lean_object* v_m_402_){
_start:
{
lean_object* v_second_403_; lean_object* v_nano_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_second_403_ = lean_ctor_get(v_t_401_, 0);
v_nano_404_ = lean_ctor_get(v_t_401_, 1);
v___x_405_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutes___closed__0, &l_Std_Time_Timestamp_toMinutes___closed__0_once, _init_l_Std_Time_Timestamp_toMinutes___closed__0);
v___x_406_ = lean_int_mul(v_m_402_, v___x_405_);
v___x_407_ = lean_int_neg(v___x_406_);
lean_dec(v___x_406_);
v___x_408_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_409_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_410_ = lean_int_mul(v_second_403_, v___x_409_);
v___x_411_ = lean_int_add(v___x_410_, v_nano_404_);
lean_dec(v___x_410_);
v___x_412_ = lean_int_mul(v___x_407_, v___x_409_);
lean_dec(v___x_407_);
v___x_413_ = lean_int_add(v___x_412_, v___x_408_);
lean_dec(v___x_412_);
v___x_414_ = lean_int_add(v___x_411_, v___x_413_);
lean_dec(v___x_413_);
lean_dec(v___x_411_);
v___x_415_ = l_Std_Time_Duration_ofNanoseconds(v___x_414_);
lean_dec(v___x_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes___boxed(lean_object* v_t_416_, lean_object* v_m_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Std_Time_Timestamp_subMinutes(v_t_416_, v_m_417_);
lean_dec(v_m_417_);
lean_dec_ref(v_t_416_);
return v_res_418_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_addHours___closed__0(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_unsigned_to_nat(3600u);
v___x_420_ = lean_nat_to_int(v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours(lean_object* v_t_421_, lean_object* v_h_422_){
_start:
{
lean_object* v_second_423_; lean_object* v_nano_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_second_423_ = lean_ctor_get(v_t_421_, 0);
v_nano_424_ = lean_ctor_get(v_t_421_, 1);
v___x_425_ = lean_obj_once(&l_Std_Time_Timestamp_addHours___closed__0, &l_Std_Time_Timestamp_addHours___closed__0_once, _init_l_Std_Time_Timestamp_addHours___closed__0);
v___x_426_ = lean_int_mul(v_h_422_, v___x_425_);
v___x_427_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_428_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_429_ = lean_int_mul(v_second_423_, v___x_428_);
v___x_430_ = lean_int_add(v___x_429_, v_nano_424_);
lean_dec(v___x_429_);
v___x_431_ = lean_int_mul(v___x_426_, v___x_428_);
lean_dec(v___x_426_);
v___x_432_ = lean_int_add(v___x_431_, v___x_427_);
lean_dec(v___x_431_);
v___x_433_ = lean_int_add(v___x_430_, v___x_432_);
lean_dec(v___x_432_);
lean_dec(v___x_430_);
v___x_434_ = l_Std_Time_Duration_ofNanoseconds(v___x_433_);
lean_dec(v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours___boxed(lean_object* v_t_435_, lean_object* v_h_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_Time_Timestamp_addHours(v_t_435_, v_h_436_);
lean_dec(v_h_436_);
lean_dec_ref(v_t_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours(lean_object* v_t_438_, lean_object* v_h_439_){
_start:
{
lean_object* v_second_440_; lean_object* v_nano_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_second_440_ = lean_ctor_get(v_t_438_, 0);
v_nano_441_ = lean_ctor_get(v_t_438_, 1);
v___x_442_ = lean_obj_once(&l_Std_Time_Timestamp_addHours___closed__0, &l_Std_Time_Timestamp_addHours___closed__0_once, _init_l_Std_Time_Timestamp_addHours___closed__0);
v___x_443_ = lean_int_mul(v_h_439_, v___x_442_);
v___x_444_ = lean_int_neg(v___x_443_);
lean_dec(v___x_443_);
v___x_445_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_446_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_447_ = lean_int_mul(v_second_440_, v___x_446_);
v___x_448_ = lean_int_add(v___x_447_, v_nano_441_);
lean_dec(v___x_447_);
v___x_449_ = lean_int_mul(v___x_444_, v___x_446_);
lean_dec(v___x_444_);
v___x_450_ = lean_int_add(v___x_449_, v___x_445_);
lean_dec(v___x_449_);
v___x_451_ = lean_int_add(v___x_448_, v___x_450_);
lean_dec(v___x_450_);
lean_dec(v___x_448_);
v___x_452_ = l_Std_Time_Duration_ofNanoseconds(v___x_451_);
lean_dec(v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours___boxed(lean_object* v_t_453_, lean_object* v_h_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_Time_Timestamp_subHours(v_t_453_, v_h_454_);
lean_dec(v_h_454_);
lean_dec_ref(v_t_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays(lean_object* v_t_456_, lean_object* v_d_457_){
_start:
{
lean_object* v_second_458_; lean_object* v_nano_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_second_458_ = lean_ctor_get(v_t_456_, 0);
v_nano_459_ = lean_ctor_get(v_t_456_, 1);
v___x_460_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_461_ = lean_int_mul(v_d_457_, v___x_460_);
v___x_462_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_463_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_464_ = lean_int_mul(v_second_458_, v___x_463_);
v___x_465_ = lean_int_add(v___x_464_, v_nano_459_);
lean_dec(v___x_464_);
v___x_466_ = lean_int_mul(v___x_461_, v___x_463_);
lean_dec(v___x_461_);
v___x_467_ = lean_int_add(v___x_466_, v___x_462_);
lean_dec(v___x_466_);
v___x_468_ = lean_int_add(v___x_465_, v___x_467_);
lean_dec(v___x_467_);
lean_dec(v___x_465_);
v___x_469_ = l_Std_Time_Duration_ofNanoseconds(v___x_468_);
lean_dec(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays___boxed(lean_object* v_t_470_, lean_object* v_d_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_Time_Timestamp_addDays(v_t_470_, v_d_471_);
lean_dec(v_d_471_);
lean_dec_ref(v_t_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays(lean_object* v_t_473_, lean_object* v_d_474_){
_start:
{
lean_object* v_second_475_; lean_object* v_nano_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_second_475_ = lean_ctor_get(v_t_473_, 0);
v_nano_476_ = lean_ctor_get(v_t_473_, 1);
v___x_477_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_478_ = lean_int_mul(v_d_474_, v___x_477_);
v___x_479_ = lean_int_neg(v___x_478_);
lean_dec(v___x_478_);
v___x_480_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_481_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_482_ = lean_int_mul(v_second_475_, v___x_481_);
v___x_483_ = lean_int_add(v___x_482_, v_nano_476_);
lean_dec(v___x_482_);
v___x_484_ = lean_int_mul(v___x_479_, v___x_481_);
lean_dec(v___x_479_);
v___x_485_ = lean_int_add(v___x_484_, v___x_480_);
lean_dec(v___x_484_);
v___x_486_ = lean_int_add(v___x_483_, v___x_485_);
lean_dec(v___x_485_);
lean_dec(v___x_483_);
v___x_487_ = l_Std_Time_Duration_ofNanoseconds(v___x_486_);
lean_dec(v___x_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays___boxed(lean_object* v_t_488_, lean_object* v_d_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_Time_Timestamp_subDays(v_t_488_, v_d_489_);
lean_dec(v_d_489_);
lean_dec_ref(v_t_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks(lean_object* v_t_491_, lean_object* v_d_492_){
_start:
{
lean_object* v_second_493_; lean_object* v_nano_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_second_493_ = lean_ctor_get(v_t_491_, 0);
v_nano_494_ = lean_ctor_get(v_t_491_, 1);
v___x_495_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_496_ = lean_int_mul(v_d_492_, v___x_495_);
v___x_497_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_498_ = lean_int_mul(v___x_496_, v___x_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_500_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_501_ = lean_int_mul(v_second_493_, v___x_500_);
v___x_502_ = lean_int_add(v___x_501_, v_nano_494_);
lean_dec(v___x_501_);
v___x_503_ = lean_int_mul(v___x_498_, v___x_500_);
lean_dec(v___x_498_);
v___x_504_ = lean_int_add(v___x_503_, v___x_499_);
lean_dec(v___x_503_);
v___x_505_ = lean_int_add(v___x_502_, v___x_504_);
lean_dec(v___x_504_);
lean_dec(v___x_502_);
v___x_506_ = l_Std_Time_Duration_ofNanoseconds(v___x_505_);
lean_dec(v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks___boxed(lean_object* v_t_507_, lean_object* v_d_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Std_Time_Timestamp_addWeeks(v_t_507_, v_d_508_);
lean_dec(v_d_508_);
lean_dec_ref(v_t_507_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks(lean_object* v_t_510_, lean_object* v_d_511_){
_start:
{
lean_object* v_second_512_; lean_object* v_nano_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_second_512_ = lean_ctor_get(v_t_510_, 0);
v_nano_513_ = lean_ctor_get(v_t_510_, 1);
v___x_514_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_515_ = lean_int_mul(v_d_511_, v___x_514_);
v___x_516_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_517_ = lean_int_mul(v___x_515_, v___x_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_int_neg(v___x_517_);
lean_dec(v___x_517_);
v___x_519_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_520_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_521_ = lean_int_mul(v_second_512_, v___x_520_);
v___x_522_ = lean_int_add(v___x_521_, v_nano_513_);
lean_dec(v___x_521_);
v___x_523_ = lean_int_mul(v___x_518_, v___x_520_);
lean_dec(v___x_518_);
v___x_524_ = lean_int_add(v___x_523_, v___x_519_);
lean_dec(v___x_523_);
v___x_525_ = lean_int_add(v___x_522_, v___x_524_);
lean_dec(v___x_524_);
lean_dec(v___x_522_);
v___x_526_ = l_Std_Time_Duration_ofNanoseconds(v___x_525_);
lean_dec(v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks___boxed(lean_object* v_t_527_, lean_object* v_d_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Std_Time_Timestamp_subWeeks(v_t_527_, v_d_528_);
lean_dec(v_d_528_);
lean_dec_ref(v_t_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration(lean_object* v_t_530_, lean_object* v_d_531_){
_start:
{
lean_object* v_second_532_; lean_object* v_nano_533_; lean_object* v_second_534_; lean_object* v_nano_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_second_532_ = lean_ctor_get(v_t_530_, 0);
v_nano_533_ = lean_ctor_get(v_t_530_, 1);
v_second_534_ = lean_ctor_get(v_d_531_, 0);
v_nano_535_ = lean_ctor_get(v_d_531_, 1);
v___x_536_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_537_ = lean_int_mul(v_second_532_, v___x_536_);
v___x_538_ = lean_int_add(v___x_537_, v_nano_533_);
lean_dec(v___x_537_);
v___x_539_ = lean_int_mul(v_second_534_, v___x_536_);
v___x_540_ = lean_int_add(v___x_539_, v_nano_535_);
lean_dec(v___x_539_);
v___x_541_ = lean_int_add(v___x_538_, v___x_540_);
lean_dec(v___x_540_);
lean_dec(v___x_538_);
v___x_542_ = l_Std_Time_Duration_ofNanoseconds(v___x_541_);
lean_dec(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration___boxed(lean_object* v_t_543_, lean_object* v_d_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Std_Time_Timestamp_addDuration(v_t_543_, v_d_544_);
lean_dec_ref(v_d_544_);
lean_dec_ref(v_t_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration(lean_object* v_t_546_, lean_object* v_d_547_){
_start:
{
lean_object* v_second_548_; lean_object* v_nano_549_; lean_object* v_second_550_; lean_object* v_nano_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v_second_548_ = lean_ctor_get(v_d_547_, 0);
v_nano_549_ = lean_ctor_get(v_d_547_, 1);
v_second_550_ = lean_ctor_get(v_t_546_, 0);
v_nano_551_ = lean_ctor_get(v_t_546_, 1);
v___x_552_ = lean_int_neg(v_second_548_);
v___x_553_ = lean_int_neg(v_nano_549_);
v___x_554_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_555_ = lean_int_mul(v_second_550_, v___x_554_);
v___x_556_ = lean_int_add(v___x_555_, v_nano_551_);
lean_dec(v___x_555_);
v___x_557_ = lean_int_mul(v___x_552_, v___x_554_);
lean_dec(v___x_552_);
v___x_558_ = lean_int_add(v___x_557_, v___x_553_);
lean_dec(v___x_553_);
lean_dec(v___x_557_);
v___x_559_ = lean_int_add(v___x_556_, v___x_558_);
lean_dec(v___x_558_);
lean_dec(v___x_556_);
v___x_560_ = l_Std_Time_Duration_ofNanoseconds(v___x_559_);
lean_dec(v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration___boxed(lean_object* v_t_561_, lean_object* v_d_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Std_Time_Timestamp_subDuration(v_t_561_, v_d_562_);
lean_dec_ref(v_d_562_);
lean_dec_ref(v_t_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0(lean_object* v_x_596_, lean_object* v_y_597_){
_start:
{
lean_object* v_second_598_; lean_object* v_nano_599_; lean_object* v_second_600_; lean_object* v_nano_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_second_598_ = lean_ctor_get(v_y_597_, 0);
v_nano_599_ = lean_ctor_get(v_y_597_, 1);
v_second_600_ = lean_ctor_get(v_x_596_, 0);
v_nano_601_ = lean_ctor_get(v_x_596_, 1);
v___x_602_ = lean_int_neg(v_second_598_);
v___x_603_ = lean_int_neg(v_nano_599_);
v___x_604_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_605_ = lean_int_mul(v_second_600_, v___x_604_);
v___x_606_ = lean_int_add(v___x_605_, v_nano_601_);
lean_dec(v___x_605_);
v___x_607_ = lean_int_mul(v___x_602_, v___x_604_);
lean_dec(v___x_602_);
v___x_608_ = lean_int_add(v___x_607_, v___x_603_);
lean_dec(v___x_603_);
lean_dec(v___x_607_);
v___x_609_ = lean_int_add(v___x_606_, v___x_608_);
lean_dec(v___x_608_);
lean_dec(v___x_606_);
v___x_610_ = l_Std_Time_Duration_ofNanoseconds(v___x_609_);
lean_dec(v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed(lean_object* v_x_611_, lean_object* v_y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Std_Time_Timestamp_instHSubDuration__1___lam__0(v_x_611_, v_y_612_);
lean_dec_ref(v_y_612_);
lean_dec_ref(v_x_611_);
return v_res_613_;
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

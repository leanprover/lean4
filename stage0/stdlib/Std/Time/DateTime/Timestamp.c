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
lean_object* l_Std_Time_Internal_UnitVal_instRepr___lam__0(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l_Std_Time_instDecidableEqDuration_decEq(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Time_instToStringDuration_leftPad(lean_object*, lean_object*);
lean_object* l_Std_Time_Internal_UnitVal_instToString___lam__0(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
static const lean_string_object l_Std_Time_instReprTimestamp_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Time_instReprTimestamp_repr___redArg___closed__16 = (const lean_object*)&l_Std_Time_instReprTimestamp_repr___redArg___closed__16_value;
static const lean_string_object l_Std_Time_instReprTimestamp_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
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
lean_object* v_second_34_; lean_object* v_nano_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_102_; 
v_second_34_ = lean_ctor_get(v_x_33_, 0);
v_nano_35_ = lean_ctor_get(v_x_33_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_33_);
if (v_isSharedCheck_102_ == 0)
{
v___x_37_ = v_x_33_;
v_isShared_38_ = v_isSharedCheck_102_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_nano_35_);
lean_inc(v_second_34_);
lean_dec(v_x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_102_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___y_42_; lean_object* v___y_43_; lean_object* v___y_63_; lean_object* v___y_64_; lean_object* v___y_65_; lean_object* v___y_66_; lean_object* v_fst_70_; lean_object* v_fst_71_; lean_object* v_snd_72_; lean_object* v___x_90_; uint8_t v___x_91_; 
v___x_39_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__6));
v___x_40_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_90_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_91_ = lean_int_dec_lt(v___x_90_, v_second_34_);
if (v___x_91_ == 0)
{
uint8_t v___x_92_; 
v___x_92_ = lean_int_dec_lt(v_second_34_, v___x_90_);
if (v___x_92_ == 0)
{
uint8_t v___x_93_; 
v___x_93_ = lean_int_dec_lt(v_nano_35_, v___x_90_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
v___x_94_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__17));
lean_inc(v_nano_35_);
v_fst_70_ = v___x_94_;
v_fst_71_ = v_second_34_;
v_snd_72_ = v_nano_35_;
goto v___jp_69_;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__16));
v___x_96_ = lean_int_neg(v_second_34_);
lean_dec(v_second_34_);
v___x_97_ = lean_int_neg(v_nano_35_);
v_fst_70_ = v___x_95_;
v_fst_71_ = v___x_96_;
v_snd_72_ = v___x_97_;
goto v___jp_69_;
}
}
else
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__16));
v___x_99_ = lean_int_neg(v_second_34_);
lean_dec(v_second_34_);
v___x_100_ = lean_int_neg(v_nano_35_);
v_fst_70_ = v___x_98_;
v_fst_71_ = v___x_99_;
v_snd_72_ = v___x_100_;
goto v___jp_69_;
}
}
else
{
lean_object* v___x_101_; 
v___x_101_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__17));
lean_inc(v_nano_35_);
v_fst_70_ = v___x_101_;
v_fst_71_ = v_second_34_;
v_snd_72_ = v_nano_35_;
goto v___jp_69_;
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
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = l_Std_Time_instToStringDuration_leftPad(v___y_63_, v___y_66_);
lean_dec_ref(v___y_66_);
v___x_68_ = lean_string_append(v___y_65_, v___x_67_);
lean_dec_ref(v___x_67_);
v___y_42_ = v___y_64_;
v___y_43_ = v___x_68_;
goto v___jp_41_;
}
v___jp_69_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_73_ = l_Std_Time_Internal_UnitVal_instToString___lam__0(v_fst_71_);
lean_dec(v_fst_71_);
v___x_74_ = lean_string_append(v_fst_70_, v___x_73_);
lean_dec_ref(v___x_73_);
v___x_75_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_76_ = lean_int_dec_eq(v_nano_35_, v___x_75_);
lean_dec(v_nano_35_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; uint8_t v_isNeg_79_; 
v___x_77_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__15));
v___x_78_ = lean_unsigned_to_nat(9u);
v_isNeg_79_ = lean_int_dec_lt(v_snd_72_, v___x_75_);
if (v_isNeg_79_ == 0)
{
lean_object* v_a_80_; lean_object* v___x_81_; 
v_a_80_ = lean_nat_abs(v_snd_72_);
lean_dec(v_snd_72_);
v___x_81_ = l_Nat_reprFast(v_a_80_);
v___y_63_ = v___x_78_;
v___y_64_ = v___x_74_;
v___y_65_ = v___x_77_;
v___y_66_ = v___x_81_;
goto v___jp_62_;
}
else
{
lean_object* v_abs_82_; lean_object* v_one_83_; lean_object* v_a_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v_abs_82_ = lean_nat_abs(v_snd_72_);
lean_dec(v_snd_72_);
v_one_83_ = lean_unsigned_to_nat(1u);
v_a_84_ = lean_nat_sub(v_abs_82_, v_one_83_);
lean_dec(v_abs_82_);
v___x_85_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__16));
v___x_86_ = lean_nat_add(v_a_84_, v_one_83_);
lean_dec(v_a_84_);
v___x_87_ = l_Nat_reprFast(v___x_86_);
v___x_88_ = lean_string_append(v___x_85_, v___x_87_);
lean_dec_ref(v___x_87_);
v___y_63_ = v___x_78_;
v___y_64_ = v___x_74_;
v___y_65_ = v___x_77_;
v___y_66_ = v___x_88_;
goto v___jp_62_;
}
}
else
{
lean_object* v___x_89_; 
lean_dec(v_snd_72_);
v___x_89_ = ((lean_object*)(l_Std_Time_instReprTimestamp_repr___redArg___closed__17));
v___y_42_ = v___x_74_;
v___y_43_ = v___x_89_;
goto v___jp_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp_repr(lean_object* v_x_103_, lean_object* v_prec_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Std_Time_instReprTimestamp_repr___redArg(v_x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp_repr___boxed(lean_object* v_x_106_, lean_object* v_prec_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Std_Time_instReprTimestamp_repr(v_x_106_, v_prec_107_);
lean_dec(v_prec_107_);
return v_res_108_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimestamp_decEq(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_111_, v_x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimestamp_decEq___boxed(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Std_Time_instDecidableEqTimestamp_decEq(v_x_114_, v_x_115_);
lean_dec_ref(v_x_115_);
lean_dec_ref(v_x_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimestamp(lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
uint8_t v___x_120_; 
v___x_120_ = l_Std_Time_instDecidableEqDuration_decEq(v_x_118_, v_x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimestamp___boxed(lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Std_Time_instDecidableEqTimestamp(v_x_121_, v_x_122_);
lean_dec_ref(v_x_122_);
lean_dec_ref(v_x_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimestamp_default___closed__0(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
return v___x_126_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimestamp_default(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&l_Std_Time_instInhabitedTimestamp_default___closed__0, &l_Std_Time_instInhabitedTimestamp_default___closed__0_once, _init_l_Std_Time_instInhabitedTimestamp_default___closed__0);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_instInhabitedTimestamp_default_spec__0(lean_object* v_a_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_nat_to_int(v_a_128_);
v___x_130_ = l_Rat_ofInt(v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimestamp(void){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Std_Time_instInhabitedTimestamp_default;
return v___x_131_;
}
}
static lean_object* _init_l_Std_Time_instLETimestamp(void){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_box(0);
return v___x_132_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLeTimestamp(lean_object* v_x_133_, lean_object* v_y_134_){
_start:
{
uint8_t v___x_135_; 
v___x_135_ = l_Std_Time_Duration_instDecidableLe(v_x_133_, v_y_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLeTimestamp___boxed(lean_object* v_x_136_, lean_object* v_y_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Std_Time_instDecidableLeTimestamp(v_x_136_, v_y_137_);
lean_dec_ref(v_y_137_);
lean_dec_ref(v_x_136_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
static lean_object* _init_l_Std_Time_instLTTimestamp(void){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_box(0);
return v___x_140_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableLtTimestamp(lean_object* v_x_141_, lean_object* v_y_142_){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = l_Std_Time_Duration_instDecidableLt(v_x_141_, v_y_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableLtTimestamp___boxed(lean_object* v_x_144_, lean_object* v_y_145_){
_start:
{
uint8_t v_res_146_; lean_object* v_r_147_; 
v_res_146_ = l_Std_Time_instDecidableLtTimestamp(v_x_144_, v_y_145_);
lean_dec_ref(v_y_145_);
lean_dec_ref(v_x_144_);
v_r_147_ = lean_box(v_res_146_);
return v_r_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOfNatTimestamp(lean_object* v_n_148_){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_nat_to_int(v_n_148_);
v___x_150_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0(lean_object* v_s_152_){
_start:
{
lean_object* v_second_153_; lean_object* v___x_154_; 
v_second_153_ = lean_ctor_get(v_s_152_, 0);
v___x_154_ = l_Std_Time_Internal_UnitVal_instToString___lam__0(v_second_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instToStringTimestamp___lam__0___boxed(lean_object* v_s_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Std_Time_instToStringTimestamp___lam__0(v_s_155_);
lean_dec_ref(v_s_155_);
return v_res_156_;
}
}
static lean_object* _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_unsigned_to_nat(1000000000u);
v___x_163_ = lean_nat_to_int(v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp__1___lam__0(lean_object* v_s_164_, lean_object* v___y_165_){
_start:
{
lean_object* v_second_166_; lean_object* v_nano_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_181_; 
v_second_166_ = lean_ctor_get(v_s_164_, 0);
v_nano_167_ = lean_ctor_get(v_s_164_, 1);
v_isSharedCheck_181_ = !lean_is_exclusive(v_s_164_);
if (v_isSharedCheck_181_ == 0)
{
v___x_169_ = v_s_164_;
v_isShared_170_ = v_isSharedCheck_181_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_nano_167_);
lean_inc(v_second_166_);
lean_dec(v_s_164_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_181_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v_nanos_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_171_ = ((lean_object*)(l_Std_Time_instReprTimestamp__1___lam__0___closed__1));
v___x_172_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_173_ = lean_int_mul(v_second_166_, v___x_172_);
lean_dec(v_second_166_);
v_nanos_174_ = lean_int_add(v___x_173_, v_nano_167_);
lean_dec(v_nano_167_);
lean_dec(v___x_173_);
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = l_Std_Time_Internal_UnitVal_instRepr___lam__0(v_nanos_174_, v___x_175_);
lean_dec(v_nanos_174_);
if (v_isShared_170_ == 0)
{
lean_ctor_set_tag(v___x_169_, 5);
lean_ctor_set(v___x_169_, 1, v___x_176_);
lean_ctor_set(v___x_169_, 0, v___x_171_);
v___x_178_ = v___x_169_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_180_, 1, v___x_176_);
v___x_178_ = v_reuseFailAlloc_180_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_179_; 
v___x_179_ = l_Repr_addAppParen(v___x_178_, v___y_165_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimestamp__1___lam__0___boxed(lean_object* v_s_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_Time_instReprTimestamp__1___lam__0(v_s_182_, v___y_183_);
lean_dec(v___y_183_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp___lam__0(lean_object* v_x_187_){
_start:
{
lean_inc_ref(v_x_187_);
return v_x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdTimestamp___lam__0___boxed(lean_object* v_x_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Std_Time_instOrdTimestamp___lam__0(v_x_188_);
lean_dec_ref(v_x_188_);
return v_res_189_;
}
}
static lean_object* _init_l_Std_Time_instOrdTimestamp___closed__1(void){
_start:
{
lean_object* v___f_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___f_191_ = ((lean_object*)(l_Std_Time_instOrdTimestamp___closed__0));
v___x_192_ = l_Std_Time_instOrdDuration;
v___x_193_ = lean_alloc_closure((void*)(l_compareOn___boxed), 6, 4);
lean_closure_set(v___x_193_, 0, lean_box(0));
lean_closure_set(v___x_193_, 1, lean_box(0));
lean_closure_set(v___x_193_, 2, v___x_192_);
lean_closure_set(v___x_193_, 3, v___f_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Std_Time_instOrdTimestamp(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&l_Std_Time_instOrdTimestamp___closed__1, &l_Std_Time_instOrdTimestamp___closed__1_once, _init_l_Std_Time_instOrdTimestamp___closed__1);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_now___boxed(lean_object* v_a_00___x40___internal___hyg_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = lean_get_current_time();
return v_res_197_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toMinutes___closed__0(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_unsigned_to_nat(60u);
v___x_199_ = lean_nat_to_int(v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutes(lean_object* v_tm_200_){
_start:
{
lean_object* v_second_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_second_201_ = lean_ctor_get(v_tm_200_, 0);
v___x_202_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutes___closed__0, &l_Std_Time_Timestamp_toMinutes___closed__0_once, _init_l_Std_Time_Timestamp_toMinutes___closed__0);
v___x_203_ = lean_int_div(v_second_201_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMinutes___boxed(lean_object* v_tm_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Std_Time_Timestamp_toMinutes(v_tm_204_);
lean_dec_ref(v_tm_204_);
return v_res_205_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toDays___closed__0(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_unsigned_to_nat(86400u);
v___x_207_ = lean_nat_to_int(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDays(lean_object* v_tm_208_){
_start:
{
lean_object* v_second_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_second_209_ = lean_ctor_get(v_tm_208_, 0);
v___x_210_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_211_ = lean_int_div(v_second_209_, v___x_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDays___boxed(lean_object* v_tm_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Std_Time_Timestamp_toDays(v_tm_212_);
lean_dec_ref(v_tm_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofSecondsSinceUnixEpoch(lean_object* v_secs_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_216_, 0, v_secs_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(lean_object* v_nanos_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch___boxed(lean_object* v_nanos_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Std_Time_Timestamp_ofNanosecondsSinceUnixEpoch(v_nanos_219_);
lean_dec(v_nanos_219_);
return v_res_220_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(1000000u);
v___x_222_ = lean_nat_to_int(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(lean_object* v_milli_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_225_ = lean_int_mul(v_milli_223_, v___x_224_);
v___x_226_ = l_Std_Time_Duration_ofNanoseconds(v___x_225_);
lean_dec(v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___boxed(lean_object* v_milli_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch(v_milli_227_);
lean_dec(v_milli_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(lean_object* v_t_229_){
_start:
{
lean_object* v_second_230_; 
v_second_230_ = lean_ctor_get(v_t_229_, 0);
lean_inc(v_second_230_);
return v_second_230_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toSecondsSinceUnixEpoch___boxed(lean_object* v_t_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Std_Time_Timestamp_toSecondsSinceUnixEpoch(v_t_231_);
lean_dec_ref(v_t_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(lean_object* v_tm_233_){
_start:
{
lean_object* v_second_234_; lean_object* v_nano_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v_nanos_238_; 
v_second_234_ = lean_ctor_get(v_tm_233_, 0);
v_nano_235_ = lean_ctor_get(v_tm_233_, 1);
v___x_236_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_237_ = lean_int_mul(v_second_234_, v___x_236_);
v_nanos_238_ = lean_int_add(v___x_237_, v_nano_235_);
lean_dec(v___x_237_);
return v_nanos_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch___boxed(lean_object* v_tm_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Std_Time_Timestamp_toNanosecondsSinceUnixEpoch(v_tm_239_);
lean_dec_ref(v_tm_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(lean_object* v_tm_241_){
_start:
{
lean_object* v_second_242_; lean_object* v_nano_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_second_242_ = lean_ctor_get(v_tm_241_, 0);
v_nano_243_ = lean_ctor_get(v_tm_241_, 1);
v___x_244_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_245_ = lean_int_mul(v_second_242_, v___x_244_);
v___x_246_ = lean_int_add(v___x_245_, v_nano_243_);
lean_dec(v___x_245_);
v___x_247_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_248_ = lean_int_div(v___x_246_, v___x_247_);
lean_dec(v___x_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch___boxed(lean_object* v_tm_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_Time_Timestamp_toMillisecondsSinceUnixEpoch(v_tm_249_);
lean_dec_ref(v_tm_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since(lean_object* v_f_251_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_get_current_time();
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_274_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_274_ == 0)
{
v___x_256_ = v___x_253_;
v_isShared_257_ = v_isSharedCheck_274_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_253_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_274_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v_second_258_; lean_object* v_nano_259_; lean_object* v_second_260_; lean_object* v_nano_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
v_second_258_ = lean_ctor_get(v_f_251_, 0);
v_nano_259_ = lean_ctor_get(v_f_251_, 1);
v_second_260_ = lean_ctor_get(v_a_254_, 0);
lean_inc(v_second_260_);
v_nano_261_ = lean_ctor_get(v_a_254_, 1);
lean_inc(v_nano_261_);
lean_dec(v_a_254_);
v___x_262_ = lean_int_neg(v_second_258_);
v___x_263_ = lean_int_neg(v_nano_259_);
v___x_264_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_265_ = lean_int_mul(v_second_260_, v___x_264_);
lean_dec(v_second_260_);
v___x_266_ = lean_int_add(v___x_265_, v_nano_261_);
lean_dec(v_nano_261_);
lean_dec(v___x_265_);
v___x_267_ = lean_int_mul(v___x_262_, v___x_264_);
lean_dec(v___x_262_);
v___x_268_ = lean_int_add(v___x_267_, v___x_263_);
lean_dec(v___x_263_);
lean_dec(v___x_267_);
v___x_269_ = lean_int_add(v___x_266_, v___x_268_);
lean_dec(v___x_268_);
lean_dec(v___x_266_);
v___x_270_ = l_Std_Time_Duration_ofNanoseconds(v___x_269_);
lean_dec(v___x_269_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 0, v___x_270_);
v___x_272_ = v___x_256_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_a_275_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_253_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_253_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_since___boxed(lean_object* v_f_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_Time_Timestamp_since(v_f_283_);
lean_dec_ref(v_f_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch(lean_object* v_tm_286_){
_start:
{
lean_inc_ref(v_tm_286_);
return v_tm_286_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toDurationSinceUnixEpoch___boxed(lean_object* v_tm_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Std_Time_Timestamp_toDurationSinceUnixEpoch(v_tm_287_);
lean_dec_ref(v_tm_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds(lean_object* v_t_289_, lean_object* v_s_290_){
_start:
{
lean_object* v_second_291_; lean_object* v_nano_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_second_296_; lean_object* v_nano_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_second_291_ = lean_ctor_get(v_t_289_, 0);
v_nano_292_ = lean_ctor_get(v_t_289_, 1);
v___x_293_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_294_ = lean_int_mul(v_s_290_, v___x_293_);
v___x_295_ = l_Std_Time_Duration_ofNanoseconds(v___x_294_);
lean_dec(v___x_294_);
v_second_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_second_296_);
v_nano_297_ = lean_ctor_get(v___x_295_, 1);
lean_inc(v_nano_297_);
lean_dec_ref(v___x_295_);
v___x_298_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_299_ = lean_int_mul(v_second_291_, v___x_298_);
v___x_300_ = lean_int_add(v___x_299_, v_nano_292_);
lean_dec(v___x_299_);
v___x_301_ = lean_int_mul(v_second_296_, v___x_298_);
lean_dec(v_second_296_);
v___x_302_ = lean_int_add(v___x_301_, v_nano_297_);
lean_dec(v_nano_297_);
lean_dec(v___x_301_);
v___x_303_ = lean_int_add(v___x_300_, v___x_302_);
lean_dec(v___x_302_);
lean_dec(v___x_300_);
v___x_304_ = l_Std_Time_Duration_ofNanoseconds(v___x_303_);
lean_dec(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMilliseconds___boxed(lean_object* v_t_305_, lean_object* v_s_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Std_Time_Timestamp_addMilliseconds(v_t_305_, v_s_306_);
lean_dec(v_s_306_);
lean_dec_ref(v_t_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds(lean_object* v_t_308_, lean_object* v_s_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_second_313_; lean_object* v_nano_314_; lean_object* v_second_315_; lean_object* v_nano_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_310_ = lean_obj_once(&l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0, &l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0_once, _init_l_Std_Time_Timestamp_ofMillisecondsSinceUnixEpoch___closed__0);
v___x_311_ = lean_int_mul(v_s_309_, v___x_310_);
v___x_312_ = l_Std_Time_Duration_ofNanoseconds(v___x_311_);
lean_dec(v___x_311_);
v_second_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_second_313_);
v_nano_314_ = lean_ctor_get(v___x_312_, 1);
lean_inc(v_nano_314_);
lean_dec_ref(v___x_312_);
v_second_315_ = lean_ctor_get(v_t_308_, 0);
v_nano_316_ = lean_ctor_get(v_t_308_, 1);
v___x_317_ = lean_int_neg(v_second_313_);
lean_dec(v_second_313_);
v___x_318_ = lean_int_neg(v_nano_314_);
lean_dec(v_nano_314_);
v___x_319_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_320_ = lean_int_mul(v_second_315_, v___x_319_);
v___x_321_ = lean_int_add(v___x_320_, v_nano_316_);
lean_dec(v___x_320_);
v___x_322_ = lean_int_mul(v___x_317_, v___x_319_);
lean_dec(v___x_317_);
v___x_323_ = lean_int_add(v___x_322_, v___x_318_);
lean_dec(v___x_318_);
lean_dec(v___x_322_);
v___x_324_ = lean_int_add(v___x_321_, v___x_323_);
lean_dec(v___x_323_);
lean_dec(v___x_321_);
v___x_325_ = l_Std_Time_Duration_ofNanoseconds(v___x_324_);
lean_dec(v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMilliseconds___boxed(lean_object* v_t_326_, lean_object* v_s_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Std_Time_Timestamp_subMilliseconds(v_t_326_, v_s_327_);
lean_dec(v_s_327_);
lean_dec_ref(v_t_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds(lean_object* v_t_329_, lean_object* v_s_330_){
_start:
{
lean_object* v_second_331_; lean_object* v_nano_332_; lean_object* v___x_333_; lean_object* v_second_334_; lean_object* v_nano_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_second_331_ = lean_ctor_get(v_t_329_, 0);
v_nano_332_ = lean_ctor_get(v_t_329_, 1);
v___x_333_ = l_Std_Time_Duration_ofNanoseconds(v_s_330_);
v_second_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_second_334_);
v_nano_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc(v_nano_335_);
lean_dec_ref(v___x_333_);
v___x_336_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_337_ = lean_int_mul(v_second_331_, v___x_336_);
v___x_338_ = lean_int_add(v___x_337_, v_nano_332_);
lean_dec(v___x_337_);
v___x_339_ = lean_int_mul(v_second_334_, v___x_336_);
lean_dec(v_second_334_);
v___x_340_ = lean_int_add(v___x_339_, v_nano_335_);
lean_dec(v_nano_335_);
lean_dec(v___x_339_);
v___x_341_ = lean_int_add(v___x_338_, v___x_340_);
lean_dec(v___x_340_);
lean_dec(v___x_338_);
v___x_342_ = l_Std_Time_Duration_ofNanoseconds(v___x_341_);
lean_dec(v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addNanoseconds___boxed(lean_object* v_t_343_, lean_object* v_s_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Time_Timestamp_addNanoseconds(v_t_343_, v_s_344_);
lean_dec(v_s_344_);
lean_dec_ref(v_t_343_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds(lean_object* v_t_346_, lean_object* v_s_347_){
_start:
{
lean_object* v___x_348_; lean_object* v_second_349_; lean_object* v_nano_350_; lean_object* v_second_351_; lean_object* v_nano_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_348_ = l_Std_Time_Duration_ofNanoseconds(v_s_347_);
v_second_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_second_349_);
v_nano_350_ = lean_ctor_get(v___x_348_, 1);
lean_inc(v_nano_350_);
lean_dec_ref(v___x_348_);
v_second_351_ = lean_ctor_get(v_t_346_, 0);
v_nano_352_ = lean_ctor_get(v_t_346_, 1);
v___x_353_ = lean_int_neg(v_second_349_);
lean_dec(v_second_349_);
v___x_354_ = lean_int_neg(v_nano_350_);
lean_dec(v_nano_350_);
v___x_355_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_356_ = lean_int_mul(v_second_351_, v___x_355_);
v___x_357_ = lean_int_add(v___x_356_, v_nano_352_);
lean_dec(v___x_356_);
v___x_358_ = lean_int_mul(v___x_353_, v___x_355_);
lean_dec(v___x_353_);
v___x_359_ = lean_int_add(v___x_358_, v___x_354_);
lean_dec(v___x_354_);
lean_dec(v___x_358_);
v___x_360_ = lean_int_add(v___x_357_, v___x_359_);
lean_dec(v___x_359_);
lean_dec(v___x_357_);
v___x_361_ = l_Std_Time_Duration_ofNanoseconds(v___x_360_);
lean_dec(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subNanoseconds___boxed(lean_object* v_t_362_, lean_object* v_s_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_Time_Timestamp_subNanoseconds(v_t_362_, v_s_363_);
lean_dec(v_s_363_);
lean_dec_ref(v_t_362_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds(lean_object* v_t_365_, lean_object* v_s_366_){
_start:
{
lean_object* v_second_367_; lean_object* v_nano_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_second_367_ = lean_ctor_get(v_t_365_, 0);
v_nano_368_ = lean_ctor_get(v_t_365_, 1);
v___x_369_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_370_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_371_ = lean_int_mul(v_second_367_, v___x_370_);
v___x_372_ = lean_int_add(v___x_371_, v_nano_368_);
lean_dec(v___x_371_);
v___x_373_ = lean_int_mul(v_s_366_, v___x_370_);
v___x_374_ = lean_int_add(v___x_373_, v___x_369_);
lean_dec(v___x_373_);
v___x_375_ = lean_int_add(v___x_372_, v___x_374_);
lean_dec(v___x_374_);
lean_dec(v___x_372_);
v___x_376_ = l_Std_Time_Duration_ofNanoseconds(v___x_375_);
lean_dec(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addSeconds___boxed(lean_object* v_t_377_, lean_object* v_s_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_Time_Timestamp_addSeconds(v_t_377_, v_s_378_);
lean_dec(v_s_378_);
lean_dec_ref(v_t_377_);
return v_res_379_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_subSeconds___closed__0(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_381_ = lean_int_neg(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds(lean_object* v_t_382_, lean_object* v_s_383_){
_start:
{
lean_object* v_second_384_; lean_object* v_nano_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_second_384_ = lean_ctor_get(v_t_382_, 0);
v_nano_385_ = lean_ctor_get(v_t_382_, 1);
v___x_386_ = lean_int_neg(v_s_383_);
v___x_387_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_388_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_389_ = lean_int_mul(v_second_384_, v___x_388_);
v___x_390_ = lean_int_add(v___x_389_, v_nano_385_);
lean_dec(v___x_389_);
v___x_391_ = lean_int_mul(v___x_386_, v___x_388_);
lean_dec(v___x_386_);
v___x_392_ = lean_int_add(v___x_391_, v___x_387_);
lean_dec(v___x_391_);
v___x_393_ = lean_int_add(v___x_390_, v___x_392_);
lean_dec(v___x_392_);
lean_dec(v___x_390_);
v___x_394_ = l_Std_Time_Duration_ofNanoseconds(v___x_393_);
lean_dec(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subSeconds___boxed(lean_object* v_t_395_, lean_object* v_s_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_Time_Timestamp_subSeconds(v_t_395_, v_s_396_);
lean_dec(v_s_396_);
lean_dec_ref(v_t_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes(lean_object* v_t_398_, lean_object* v_m_399_){
_start:
{
lean_object* v_second_400_; lean_object* v_nano_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v_second_400_ = lean_ctor_get(v_t_398_, 0);
v_nano_401_ = lean_ctor_get(v_t_398_, 1);
v___x_402_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutes___closed__0, &l_Std_Time_Timestamp_toMinutes___closed__0_once, _init_l_Std_Time_Timestamp_toMinutes___closed__0);
v___x_403_ = lean_int_mul(v_m_399_, v___x_402_);
v___x_404_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_405_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_406_ = lean_int_mul(v_second_400_, v___x_405_);
v___x_407_ = lean_int_add(v___x_406_, v_nano_401_);
lean_dec(v___x_406_);
v___x_408_ = lean_int_mul(v___x_403_, v___x_405_);
lean_dec(v___x_403_);
v___x_409_ = lean_int_add(v___x_408_, v___x_404_);
lean_dec(v___x_408_);
v___x_410_ = lean_int_add(v___x_407_, v___x_409_);
lean_dec(v___x_409_);
lean_dec(v___x_407_);
v___x_411_ = l_Std_Time_Duration_ofNanoseconds(v___x_410_);
lean_dec(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addMinutes___boxed(lean_object* v_t_412_, lean_object* v_m_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_Time_Timestamp_addMinutes(v_t_412_, v_m_413_);
lean_dec(v_m_413_);
lean_dec_ref(v_t_412_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes(lean_object* v_t_415_, lean_object* v_m_416_){
_start:
{
lean_object* v_second_417_; lean_object* v_nano_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_second_417_ = lean_ctor_get(v_t_415_, 0);
v_nano_418_ = lean_ctor_get(v_t_415_, 1);
v___x_419_ = lean_obj_once(&l_Std_Time_Timestamp_toMinutes___closed__0, &l_Std_Time_Timestamp_toMinutes___closed__0_once, _init_l_Std_Time_Timestamp_toMinutes___closed__0);
v___x_420_ = lean_int_mul(v_m_416_, v___x_419_);
v___x_421_ = lean_int_neg(v___x_420_);
lean_dec(v___x_420_);
v___x_422_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_423_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_424_ = lean_int_mul(v_second_417_, v___x_423_);
v___x_425_ = lean_int_add(v___x_424_, v_nano_418_);
lean_dec(v___x_424_);
v___x_426_ = lean_int_mul(v___x_421_, v___x_423_);
lean_dec(v___x_421_);
v___x_427_ = lean_int_add(v___x_426_, v___x_422_);
lean_dec(v___x_426_);
v___x_428_ = lean_int_add(v___x_425_, v___x_427_);
lean_dec(v___x_427_);
lean_dec(v___x_425_);
v___x_429_ = l_Std_Time_Duration_ofNanoseconds(v___x_428_);
lean_dec(v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subMinutes___boxed(lean_object* v_t_430_, lean_object* v_m_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_Time_Timestamp_subMinutes(v_t_430_, v_m_431_);
lean_dec(v_m_431_);
lean_dec_ref(v_t_430_);
return v_res_432_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_addHours___closed__0(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(3600u);
v___x_434_ = lean_nat_to_int(v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours(lean_object* v_t_435_, lean_object* v_h_436_){
_start:
{
lean_object* v_second_437_; lean_object* v_nano_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v_second_437_ = lean_ctor_get(v_t_435_, 0);
v_nano_438_ = lean_ctor_get(v_t_435_, 1);
v___x_439_ = lean_obj_once(&l_Std_Time_Timestamp_addHours___closed__0, &l_Std_Time_Timestamp_addHours___closed__0_once, _init_l_Std_Time_Timestamp_addHours___closed__0);
v___x_440_ = lean_int_mul(v_h_436_, v___x_439_);
v___x_441_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_442_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_443_ = lean_int_mul(v_second_437_, v___x_442_);
v___x_444_ = lean_int_add(v___x_443_, v_nano_438_);
lean_dec(v___x_443_);
v___x_445_ = lean_int_mul(v___x_440_, v___x_442_);
lean_dec(v___x_440_);
v___x_446_ = lean_int_add(v___x_445_, v___x_441_);
lean_dec(v___x_445_);
v___x_447_ = lean_int_add(v___x_444_, v___x_446_);
lean_dec(v___x_446_);
lean_dec(v___x_444_);
v___x_448_ = l_Std_Time_Duration_ofNanoseconds(v___x_447_);
lean_dec(v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addHours___boxed(lean_object* v_t_449_, lean_object* v_h_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_Time_Timestamp_addHours(v_t_449_, v_h_450_);
lean_dec(v_h_450_);
lean_dec_ref(v_t_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours(lean_object* v_t_452_, lean_object* v_h_453_){
_start:
{
lean_object* v_second_454_; lean_object* v_nano_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_second_454_ = lean_ctor_get(v_t_452_, 0);
v_nano_455_ = lean_ctor_get(v_t_452_, 1);
v___x_456_ = lean_obj_once(&l_Std_Time_Timestamp_addHours___closed__0, &l_Std_Time_Timestamp_addHours___closed__0_once, _init_l_Std_Time_Timestamp_addHours___closed__0);
v___x_457_ = lean_int_mul(v_h_453_, v___x_456_);
v___x_458_ = lean_int_neg(v___x_457_);
lean_dec(v___x_457_);
v___x_459_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_460_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_461_ = lean_int_mul(v_second_454_, v___x_460_);
v___x_462_ = lean_int_add(v___x_461_, v_nano_455_);
lean_dec(v___x_461_);
v___x_463_ = lean_int_mul(v___x_458_, v___x_460_);
lean_dec(v___x_458_);
v___x_464_ = lean_int_add(v___x_463_, v___x_459_);
lean_dec(v___x_463_);
v___x_465_ = lean_int_add(v___x_462_, v___x_464_);
lean_dec(v___x_464_);
lean_dec(v___x_462_);
v___x_466_ = l_Std_Time_Duration_ofNanoseconds(v___x_465_);
lean_dec(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subHours___boxed(lean_object* v_t_467_, lean_object* v_h_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_Time_Timestamp_subHours(v_t_467_, v_h_468_);
lean_dec(v_h_468_);
lean_dec_ref(v_t_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays(lean_object* v_t_470_, lean_object* v_d_471_){
_start:
{
lean_object* v_second_472_; lean_object* v_nano_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v_second_472_ = lean_ctor_get(v_t_470_, 0);
v_nano_473_ = lean_ctor_get(v_t_470_, 1);
v___x_474_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_475_ = lean_int_mul(v_d_471_, v___x_474_);
v___x_476_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_477_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_478_ = lean_int_mul(v_second_472_, v___x_477_);
v___x_479_ = lean_int_add(v___x_478_, v_nano_473_);
lean_dec(v___x_478_);
v___x_480_ = lean_int_mul(v___x_475_, v___x_477_);
lean_dec(v___x_475_);
v___x_481_ = lean_int_add(v___x_480_, v___x_476_);
lean_dec(v___x_480_);
v___x_482_ = lean_int_add(v___x_479_, v___x_481_);
lean_dec(v___x_481_);
lean_dec(v___x_479_);
v___x_483_ = l_Std_Time_Duration_ofNanoseconds(v___x_482_);
lean_dec(v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDays___boxed(lean_object* v_t_484_, lean_object* v_d_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_Time_Timestamp_addDays(v_t_484_, v_d_485_);
lean_dec(v_d_485_);
lean_dec_ref(v_t_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays(lean_object* v_t_487_, lean_object* v_d_488_){
_start:
{
lean_object* v_second_489_; lean_object* v_nano_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v_second_489_ = lean_ctor_get(v_t_487_, 0);
v_nano_490_ = lean_ctor_get(v_t_487_, 1);
v___x_491_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_492_ = lean_int_mul(v_d_488_, v___x_491_);
v___x_493_ = lean_int_neg(v___x_492_);
lean_dec(v___x_492_);
v___x_494_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_495_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_496_ = lean_int_mul(v_second_489_, v___x_495_);
v___x_497_ = lean_int_add(v___x_496_, v_nano_490_);
lean_dec(v___x_496_);
v___x_498_ = lean_int_mul(v___x_493_, v___x_495_);
lean_dec(v___x_493_);
v___x_499_ = lean_int_add(v___x_498_, v___x_494_);
lean_dec(v___x_498_);
v___x_500_ = lean_int_add(v___x_497_, v___x_499_);
lean_dec(v___x_499_);
lean_dec(v___x_497_);
v___x_501_ = l_Std_Time_Duration_ofNanoseconds(v___x_500_);
lean_dec(v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDays___boxed(lean_object* v_t_502_, lean_object* v_d_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_Time_Timestamp_subDays(v_t_502_, v_d_503_);
lean_dec(v_d_503_);
lean_dec_ref(v_t_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks(lean_object* v_t_505_, lean_object* v_d_506_){
_start:
{
lean_object* v_second_507_; lean_object* v_nano_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_second_507_ = lean_ctor_get(v_t_505_, 0);
v_nano_508_ = lean_ctor_get(v_t_505_, 1);
v___x_509_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_510_ = lean_int_mul(v_d_506_, v___x_509_);
v___x_511_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_512_ = lean_int_mul(v___x_510_, v___x_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__14, &l_Std_Time_instReprTimestamp_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__14);
v___x_514_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_515_ = lean_int_mul(v_second_507_, v___x_514_);
v___x_516_ = lean_int_add(v___x_515_, v_nano_508_);
lean_dec(v___x_515_);
v___x_517_ = lean_int_mul(v___x_512_, v___x_514_);
lean_dec(v___x_512_);
v___x_518_ = lean_int_add(v___x_517_, v___x_513_);
lean_dec(v___x_517_);
v___x_519_ = lean_int_add(v___x_516_, v___x_518_);
lean_dec(v___x_518_);
lean_dec(v___x_516_);
v___x_520_ = l_Std_Time_Duration_ofNanoseconds(v___x_519_);
lean_dec(v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addWeeks___boxed(lean_object* v_t_521_, lean_object* v_d_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_Time_Timestamp_addWeeks(v_t_521_, v_d_522_);
lean_dec(v_d_522_);
lean_dec_ref(v_t_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks(lean_object* v_t_524_, lean_object* v_d_525_){
_start:
{
lean_object* v_second_526_; lean_object* v_nano_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v_second_526_ = lean_ctor_get(v_t_524_, 0);
v_nano_527_ = lean_ctor_get(v_t_524_, 1);
v___x_528_ = lean_obj_once(&l_Std_Time_instReprTimestamp_repr___redArg___closed__7, &l_Std_Time_instReprTimestamp_repr___redArg___closed__7_once, _init_l_Std_Time_instReprTimestamp_repr___redArg___closed__7);
v___x_529_ = lean_int_mul(v_d_525_, v___x_528_);
v___x_530_ = lean_obj_once(&l_Std_Time_Timestamp_toDays___closed__0, &l_Std_Time_Timestamp_toDays___closed__0_once, _init_l_Std_Time_Timestamp_toDays___closed__0);
v___x_531_ = lean_int_mul(v___x_529_, v___x_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_int_neg(v___x_531_);
lean_dec(v___x_531_);
v___x_533_ = lean_obj_once(&l_Std_Time_Timestamp_subSeconds___closed__0, &l_Std_Time_Timestamp_subSeconds___closed__0_once, _init_l_Std_Time_Timestamp_subSeconds___closed__0);
v___x_534_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_535_ = lean_int_mul(v_second_526_, v___x_534_);
v___x_536_ = lean_int_add(v___x_535_, v_nano_527_);
lean_dec(v___x_535_);
v___x_537_ = lean_int_mul(v___x_532_, v___x_534_);
lean_dec(v___x_532_);
v___x_538_ = lean_int_add(v___x_537_, v___x_533_);
lean_dec(v___x_537_);
v___x_539_ = lean_int_add(v___x_536_, v___x_538_);
lean_dec(v___x_538_);
lean_dec(v___x_536_);
v___x_540_ = l_Std_Time_Duration_ofNanoseconds(v___x_539_);
lean_dec(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subWeeks___boxed(lean_object* v_t_541_, lean_object* v_d_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_Time_Timestamp_subWeeks(v_t_541_, v_d_542_);
lean_dec(v_d_542_);
lean_dec_ref(v_t_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration(lean_object* v_t_544_, lean_object* v_d_545_){
_start:
{
lean_object* v_second_546_; lean_object* v_nano_547_; lean_object* v_second_548_; lean_object* v_nano_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_second_546_ = lean_ctor_get(v_t_544_, 0);
v_nano_547_ = lean_ctor_get(v_t_544_, 1);
v_second_548_ = lean_ctor_get(v_d_545_, 0);
v_nano_549_ = lean_ctor_get(v_d_545_, 1);
v___x_550_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_551_ = lean_int_mul(v_second_546_, v___x_550_);
v___x_552_ = lean_int_add(v___x_551_, v_nano_547_);
lean_dec(v___x_551_);
v___x_553_ = lean_int_mul(v_second_548_, v___x_550_);
v___x_554_ = lean_int_add(v___x_553_, v_nano_549_);
lean_dec(v___x_553_);
v___x_555_ = lean_int_add(v___x_552_, v___x_554_);
lean_dec(v___x_554_);
lean_dec(v___x_552_);
v___x_556_ = l_Std_Time_Duration_ofNanoseconds(v___x_555_);
lean_dec(v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_addDuration___boxed(lean_object* v_t_557_, lean_object* v_d_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_Time_Timestamp_addDuration(v_t_557_, v_d_558_);
lean_dec_ref(v_d_558_);
lean_dec_ref(v_t_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration(lean_object* v_t_560_, lean_object* v_d_561_){
_start:
{
lean_object* v_second_562_; lean_object* v_nano_563_; lean_object* v_second_564_; lean_object* v_nano_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_second_562_ = lean_ctor_get(v_d_561_, 0);
v_nano_563_ = lean_ctor_get(v_d_561_, 1);
v_second_564_ = lean_ctor_get(v_t_560_, 0);
v_nano_565_ = lean_ctor_get(v_t_560_, 1);
v___x_566_ = lean_int_neg(v_second_562_);
v___x_567_ = lean_int_neg(v_nano_563_);
v___x_568_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_569_ = lean_int_mul(v_second_564_, v___x_568_);
v___x_570_ = lean_int_add(v___x_569_, v_nano_565_);
lean_dec(v___x_569_);
v___x_571_ = lean_int_mul(v___x_566_, v___x_568_);
lean_dec(v___x_566_);
v___x_572_ = lean_int_add(v___x_571_, v___x_567_);
lean_dec(v___x_567_);
lean_dec(v___x_571_);
v___x_573_ = lean_int_add(v___x_570_, v___x_572_);
lean_dec(v___x_572_);
lean_dec(v___x_570_);
v___x_574_ = l_Std_Time_Duration_ofNanoseconds(v___x_573_);
lean_dec(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_subDuration___boxed(lean_object* v_t_575_, lean_object* v_d_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_Time_Timestamp_subDuration(v_t_575_, v_d_576_);
lean_dec_ref(v_d_576_);
lean_dec_ref(v_t_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0(lean_object* v_x_610_, lean_object* v_y_611_){
_start:
{
lean_object* v_second_612_; lean_object* v_nano_613_; lean_object* v_second_614_; lean_object* v_nano_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_second_612_ = lean_ctor_get(v_y_611_, 0);
v_nano_613_ = lean_ctor_get(v_y_611_, 1);
v_second_614_ = lean_ctor_get(v_x_610_, 0);
v_nano_615_ = lean_ctor_get(v_x_610_, 1);
v___x_616_ = lean_int_neg(v_second_612_);
v___x_617_ = lean_int_neg(v_nano_613_);
v___x_618_ = lean_obj_once(&l_Std_Time_instReprTimestamp__1___lam__0___closed__2, &l_Std_Time_instReprTimestamp__1___lam__0___closed__2_once, _init_l_Std_Time_instReprTimestamp__1___lam__0___closed__2);
v___x_619_ = lean_int_mul(v_second_614_, v___x_618_);
v___x_620_ = lean_int_add(v___x_619_, v_nano_615_);
lean_dec(v___x_619_);
v___x_621_ = lean_int_mul(v___x_616_, v___x_618_);
lean_dec(v___x_616_);
v___x_622_ = lean_int_add(v___x_621_, v___x_617_);
lean_dec(v___x_617_);
lean_dec(v___x_621_);
v___x_623_ = lean_int_add(v___x_620_, v___x_622_);
lean_dec(v___x_622_);
lean_dec(v___x_620_);
v___x_624_ = l_Std_Time_Duration_ofNanoseconds(v___x_623_);
lean_dec(v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_instHSubDuration__1___lam__0___boxed(lean_object* v_x_625_, lean_object* v_y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Std_Time_Timestamp_instHSubDuration__1___lam__0(v_x_625_, v_y_626_);
lean_dec_ref(v_y_626_);
lean_dec_ref(v_x_625_);
return v_res_627_;
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

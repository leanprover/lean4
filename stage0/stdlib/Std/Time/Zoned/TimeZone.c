// Lean compiler output
// Module: Std.Time.Zoned.TimeZone
// Imports: public import Std.Time.Time public import Std.Time.DateTime.Timestamp
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
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_Time_Second_instReprOffset___lam__0(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Std_Time_Duration_ofNanoseconds(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Std_Time_Second_instOrdOffset___aux__1___boxed(lean_object*, lean_object*);
lean_object* l_compareOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_instReprOffset_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "second"};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__3_value),((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7;
static const lean_string_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8_value;
static lean_once_cell_t l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9;
static lean_once_cell_t l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instReprOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instReprOffset_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instReprOffset___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instReprOffset = (const lean_object*)&l_Std_Time_TimeZone_instReprOffset___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instDecidableEqOffset_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instDecidableEqOffset(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_TimeZone_instInhabitedOffset___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_instInhabitedOffset___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instInhabitedOffset;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed(lean_object*);
static const lean_closure_object l_Std_Time_TimeZone_instOrdOffset___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instOrdOffset___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__0_value;
static const lean_closure_object l_Std_Time_TimeZone_instOrdOffset___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_Second_instOrdOffset___aux__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_TimeZone_instOrdOffset___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__1_value;
static const lean_closure_object l_Std_Time_TimeZone_instOrdOffset___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_compareOn___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__1_value),((lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__0_value)} };
static const lean_object* l_Std_Time_TimeZone_instOrdOffset___closed__2 = (const lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Time_TimeZone_instOrdOffset = (const lean_object*)&l_Std_Time_TimeZone_instOrdOffset___closed__2_value;
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__1(lean_object*);
static const lean_string_object l_Std_Time_TimeZone_Offset_toIsoString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_Offset_toIsoString___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_Offset_toIsoString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "0"};
static const lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_Offset_toIsoString___closed__1_value;
static lean_once_cell_t l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__2;
static lean_once_cell_t l_Std_Time_TimeZone_Offset_toIsoString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__3;
static lean_once_cell_t l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__4;
static const lean_string_object l_Std_Time_TimeZone_Offset_toIsoString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__5 = (const lean_object*)&l_Std_Time_TimeZone_Offset_toIsoString___closed__5_value;
static const lean_string_object l_Std_Time_TimeZone_Offset_toIsoString___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Std_Time_TimeZone_Offset_toIsoString___closed__6 = (const lean_object*)&l_Std_Time_TimeZone_Offset_toIsoString___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_zero;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_instInhabitedTimeZone_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Time_instInhabitedTimeZone_default___closed__0 = (const lean_object*)&l_Std_Time_instInhabitedTimeZone_default___closed__0_value;
static lean_once_cell_t l_Std_Time_instInhabitedTimeZone_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instInhabitedTimeZone_default___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedTimeZone_default;
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedTimeZone;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "offset"};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__0 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__1 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__2 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__2_value),((lean_object*)&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__3 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__4 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__5 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__5_value;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__6 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__6_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__6_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__7 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__7_value;
static lean_once_cell_t l_Std_Time_instReprTimeZone_repr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__8;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "abbreviation"};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__9 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__9_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__9_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__10 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__10_value;
static lean_once_cell_t l_Std_Time_instReprTimeZone_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__11;
static const lean_string_object l_Std_Time_instReprTimeZone_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "isDST"};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__12 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__12_value;
static const lean_ctor_object l_Std_Time_instReprTimeZone_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__13 = (const lean_object*)&l_Std_Time_instReprTimeZone_repr___redArg___closed__13_value;
static lean_once_cell_t l_Std_Time_instReprTimeZone_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_instReprTimeZone_repr___redArg___closed__14;
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Time_instReprTimeZone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Time_instReprTimeZone_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Time_instReprTimeZone___closed__0 = (const lean_object*)&l_Std_Time_instReprTimeZone___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Time_instReprTimeZone = (const lean_object*)&l_Std_Time_instReprTimeZone___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Time_TimeZone_UTC___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "UTC"};
static const lean_object* l_Std_Time_TimeZone_UTC___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_UTC___closed__0_value;
static lean_once_cell_t l_Std_Time_TimeZone_UTC___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_UTC___closed__1;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTC;
static const lean_string_object l_Std_Time_TimeZone_GMT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Greenwich Mean Time"};
static const lean_object* l_Std_Time_TimeZone_GMT___closed__0 = (const lean_object*)&l_Std_Time_TimeZone_GMT___closed__0_value;
static const lean_string_object l_Std_Time_TimeZone_GMT___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "GMT"};
static const lean_object* l_Std_Time_TimeZone_GMT___closed__1 = (const lean_object*)&l_Std_Time_TimeZone_GMT___closed__1_value;
static lean_once_cell_t l_Std_Time_TimeZone_GMT___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_TimeZone_GMT___closed__2;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_GMT;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds___boxed(lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_toWallTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_toWallTime___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Time_Timestamp_ofWallTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Time_Timestamp_ofWallTime___closed__0;
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_instReprOffset_repr_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(10u);
v___x_17_ = lean_nat_to_int(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__0));
v___x_20_ = lean_string_length(v___x_19_);
return v___x_20_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__9);
v___x_22_ = lean_nat_to_int(v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg(lean_object* v_x_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_28_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__6));
v___x_29_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = l_Std_Time_Second_instReprOffset___lam__0(v_x_27_, v___x_30_);
v___x_32_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_29_);
lean_ctor_set(v___x_32_, 1, v___x_31_);
v___x_33_ = 0;
v___x_34_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_34_, 0, v___x_32_);
lean_ctor_set_uint8(v___x_34_, sizeof(void*)*1, v___x_33_);
v___x_35_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_28_);
lean_ctor_set(v___x_35_, 1, v___x_34_);
v___x_36_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10);
v___x_37_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11));
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_35_);
v___x_39_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12));
v___x_40_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_38_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
v___x_41_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_36_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
v___x_42_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*1, v___x_33_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___redArg___boxed(lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_x_43_);
lean_dec(v_x_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr(lean_object* v_x_45_, lean_object* v_prec_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_x_45_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instReprOffset_repr___boxed(lean_object* v_x_48_, lean_object* v_prec_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_Time_TimeZone_instReprOffset_repr(v_x_48_, v_prec_49_);
lean_dec(v_prec_49_);
lean_dec(v_x_48_);
return v_res_50_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instDecidableEqOffset_decEq(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
uint8_t v___x_55_; 
v___x_55_ = lean_int_dec_eq(v_x_53_, v_x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset_decEq___boxed(lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Std_Time_TimeZone_instDecidableEqOffset_decEq(v_x_56_, v_x_57_);
lean_dec(v_x_57_);
lean_dec(v_x_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_TimeZone_instDecidableEqOffset(lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = lean_int_dec_eq(v_x_60_, v_x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset___boxed(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Std_Time_TimeZone_instDecidableEqOffset(v_x_63_, v_x_64_);
lean_dec(v_x_64_);
lean_dec(v_x_63_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_nat_to_int(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedOffset(void){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedOffset___closed__0, &l_Std_Time_TimeZone_instInhabitedOffset___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedOffset___closed__0);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0(lean_object* v_x_70_){
_start:
{
lean_inc(v_x_70_);
return v_x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed(lean_object* v_x_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Std_Time_TimeZone_instOrdOffset___lam__0(v_x_71_);
lean_dec(v_x_71_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__1(lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Rat_ofInt(v_a_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_unsigned_to_nat(3600u);
v___x_84_ = lean_nat_to_int(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__3(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(60u);
v___x_86_ = lean_nat_to_int(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_nat_to_int(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object* v_offset_91_, uint8_t v_colon_92_){
_start:
{
lean_object* v___y_94_; lean_object* v___y_95_; lean_object* v___y_96_; lean_object* v___y_104_; uint8_t v___y_105_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_128_ = lean_int_dec_le(v___x_127_, v_offset_91_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__5));
v___x_130_ = lean_int_neg(v_offset_91_);
lean_dec(v_offset_91_);
v_fst_113_ = v___x_129_;
v_snd_114_ = v___x_130_;
goto v___jp_112_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__6));
v_fst_113_ = v___x_131_;
v_snd_114_ = v_offset_91_;
goto v___jp_112_;
}
v___jp_93_:
{
if (v_colon_92_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; 
lean_inc_ref(v___y_95_);
v___x_97_ = lean_string_append(v___y_95_, v___y_94_);
lean_dec_ref(v___y_94_);
v___x_98_ = lean_string_append(v___x_97_, v___y_96_);
lean_dec_ref(v___y_96_);
return v___x_98_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_inc_ref(v___y_95_);
v___x_99_ = lean_string_append(v___y_95_, v___y_94_);
lean_dec_ref(v___y_94_);
v___x_100_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__0));
v___x_101_ = lean_string_append(v___x_99_, v___x_100_);
v___x_102_ = lean_string_append(v___x_101_, v___y_96_);
lean_dec_ref(v___y_96_);
return v___x_102_;
}
}
v___jp_103_:
{
if (v___y_105_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = l_Int_repr(v___y_104_);
lean_dec(v___y_104_);
v___y_94_ = v___y_107_;
v___y_95_ = v___y_106_;
v___y_96_ = v___x_108_;
goto v___jp_93_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__1));
v___x_110_ = l_Int_repr(v___y_104_);
lean_dec(v___y_104_);
v___x_111_ = lean_string_append(v___x_109_, v___x_110_);
lean_dec_ref(v___x_110_);
v___y_94_ = v___y_107_;
v___y_95_ = v___y_106_;
v___y_96_ = v___x_111_;
goto v___jp_93_;
}
}
v___jp_112_:
{
lean_object* v___x_115_; lean_object* v_hour_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_minute_119_; lean_object* v___x_120_; uint8_t v___x_121_; uint8_t v___x_122_; 
v___x_115_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__2, &l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2);
v_hour_116_ = lean_int_div(v_snd_114_, v___x_115_);
v___x_117_ = lean_int_mod(v_snd_114_, v___x_115_);
lean_dec(v_snd_114_);
v___x_118_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__3, &l_Std_Time_TimeZone_Offset_toIsoString___closed__3_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__3);
v_minute_119_ = lean_int_ediv(v___x_117_, v___x_118_);
lean_dec(v___x_117_);
v___x_120_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7);
v___x_121_ = lean_int_dec_lt(v_hour_116_, v___x_120_);
v___x_122_ = lean_int_dec_lt(v_minute_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = l_Int_repr(v_hour_116_);
lean_dec(v_hour_116_);
v___y_104_ = v_minute_119_;
v___y_105_ = v___x_122_;
v___y_106_ = v_fst_113_;
v___y_107_ = v___x_123_;
goto v___jp_103_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__1));
v___x_125_ = l_Int_repr(v_hour_116_);
lean_dec(v_hour_116_);
v___x_126_ = lean_string_append(v___x_124_, v___x_125_);
lean_dec_ref(v___x_125_);
v___y_104_ = v_minute_119_;
v___y_105_ = v___x_122_;
v___y_106_ = v_fst_113_;
v___y_107_ = v___x_126_;
goto v___jp_103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString___boxed(lean_object* v_offset_132_, lean_object* v_colon_133_){
_start:
{
uint8_t v_colon_boxed_134_; lean_object* v_res_135_; 
v_colon_boxed_134_ = lean_unbox(v_colon_133_);
v_res_135_ = l_Std_Time_TimeZone_Offset_toIsoString(v_offset_132_, v_colon_boxed_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__0(lean_object* v_a_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_nat_to_int(v_a_136_);
v___x_138_ = l_Rat_ofInt(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_zero(void){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours(lean_object* v_n_140_){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__2, &l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2);
v___x_142_ = lean_int_mul(v_n_140_, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours___boxed(lean_object* v_n_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Std_Time_TimeZone_Offset_ofHours(v_n_143_);
lean_dec(v_n_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(lean_object* v_n_145_, lean_object* v_m_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_147_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__2, &l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2);
v___x_148_ = lean_int_mul(v_n_145_, v___x_147_);
v___x_149_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__3, &l_Std_Time_TimeZone_Offset_toIsoString___closed__3_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__3);
v___x_150_ = lean_int_mul(v_m_146_, v___x_149_);
v___x_151_ = lean_int_add(v___x_148_, v___x_150_);
lean_dec(v___x_150_);
lean_dec(v___x_148_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes___boxed(lean_object* v_n_152_, lean_object* v_m_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(v_n_152_, v_m_153_);
lean_dec(v_m_153_);
lean_dec(v_n_152_);
return v_res_154_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimeZone_default___closed__1(void){
_start:
{
uint8_t v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = 0;
v___x_157_ = ((lean_object*)(l_Std_Time_instInhabitedTimeZone_default___closed__0));
v___x_158_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_159_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_157_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*3, v___x_156_);
return v___x_159_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimeZone_default(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Std_Time_instInhabitedTimeZone_default___closed__1, &l_Std_Time_instInhabitedTimeZone_default___closed__1_once, _init_l_Std_Time_instInhabitedTimeZone_default___closed__1);
return v___x_160_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimeZone(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Std_Time_instInhabitedTimeZone_default;
return v___x_161_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(8u);
v___x_178_ = lean_nat_to_int(v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_unsigned_to_nat(16u);
v___x_183_ = lean_nat_to_int(v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_unsigned_to_nat(9u);
v___x_188_ = lean_nat_to_int(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr___redArg(lean_object* v_x_189_){
_start:
{
lean_object* v_offset_190_; lean_object* v_name_191_; lean_object* v_abbreviation_192_; uint8_t v_isDST_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v_offset_190_ = lean_ctor_get(v_x_189_, 0);
lean_inc(v_offset_190_);
v_name_191_ = lean_ctor_get(v_x_189_, 1);
lean_inc_ref(v_name_191_);
v_abbreviation_192_ = lean_ctor_get(v_x_189_, 2);
lean_inc_ref(v_abbreviation_192_);
v_isDST_193_ = lean_ctor_get_uint8(v_x_189_, sizeof(void*)*3);
lean_dec_ref(v_x_189_);
v___x_194_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5));
v___x_195_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__3));
v___x_196_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7);
v___x_197_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_offset_190_);
lean_dec(v_offset_190_);
v___x_198_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_196_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v___x_199_ = 0;
v___x_200_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_200_, 0, v___x_198_);
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*1, v___x_199_);
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_195_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__5));
v___x_203_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_box(1);
v___x_205_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__7));
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v___x_194_);
v___x_209_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__8, &l_Std_Time_instReprTimeZone_repr___redArg___closed__8_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__8);
v___x_210_ = l_String_quote(v_name_191_);
v___x_211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___x_212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_209_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_213_, sizeof(void*)*1, v___x_199_);
v___x_214_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_208_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_202_);
v___x_216_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___x_204_);
v___x_217_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__10));
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_194_);
v___x_220_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__11, &l_Std_Time_instReprTimeZone_repr___redArg___closed__11_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__11);
v___x_221_ = l_String_quote(v_abbreviation_192_);
v___x_222_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
v___x_223_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_220_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_199_);
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_219_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___x_202_);
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set(v___x_227_, 1, v___x_204_);
v___x_228_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__13));
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_194_);
v___x_231_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__14, &l_Std_Time_instReprTimeZone_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__14);
v___x_232_ = l_Bool_repr___redArg(v_isDST_193_);
v___x_233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_199_);
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_230_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10);
v___x_237_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11));
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_235_);
v___x_239_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12));
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_236_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
v___x_242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_242_, 0, v___x_241_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*1, v___x_199_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr(lean_object* v_x_243_, lean_object* v_prec_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Std_Time_instReprTimeZone_repr___redArg(v_x_243_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr___boxed(lean_object* v_x_246_, lean_object* v_prec_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_Time_instReprTimeZone_repr(v_x_246_, v_prec_247_);
lean_dec(v_prec_247_);
return v_res_248_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone_decEq(lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_offset_253_; lean_object* v_name_254_; lean_object* v_abbreviation_255_; uint8_t v_isDST_256_; lean_object* v_offset_257_; lean_object* v_name_258_; lean_object* v_abbreviation_259_; uint8_t v_isDST_260_; uint8_t v___x_261_; 
v_offset_253_ = lean_ctor_get(v_x_251_, 0);
v_name_254_ = lean_ctor_get(v_x_251_, 1);
v_abbreviation_255_ = lean_ctor_get(v_x_251_, 2);
v_isDST_256_ = lean_ctor_get_uint8(v_x_251_, sizeof(void*)*3);
v_offset_257_ = lean_ctor_get(v_x_252_, 0);
v_name_258_ = lean_ctor_get(v_x_252_, 1);
v_abbreviation_259_ = lean_ctor_get(v_x_252_, 2);
v_isDST_260_ = lean_ctor_get_uint8(v_x_252_, sizeof(void*)*3);
v___x_261_ = lean_int_dec_eq(v_offset_253_, v_offset_257_);
if (v___x_261_ == 0)
{
return v___x_261_;
}
else
{
uint8_t v___x_262_; 
v___x_262_ = lean_string_dec_eq(v_name_254_, v_name_258_);
if (v___x_262_ == 0)
{
return v___x_262_;
}
else
{
uint8_t v___x_263_; 
v___x_263_ = lean_string_dec_eq(v_abbreviation_255_, v_abbreviation_259_);
if (v___x_263_ == 0)
{
return v___x_263_;
}
else
{
if (v_isDST_256_ == 0)
{
if (v_isDST_260_ == 0)
{
return v___x_263_;
}
else
{
return v_isDST_256_;
}
}
else
{
return v_isDST_260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone_decEq___boxed(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
uint8_t v_res_266_; lean_object* v_r_267_; 
v_res_266_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_264_, v_x_265_);
lean_dec_ref(v_x_265_);
lean_dec_ref(v_x_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone(lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
uint8_t v___x_270_; 
v___x_270_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_268_, v_x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone___boxed(lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
uint8_t v_res_273_; lean_object* v_r_274_; 
v_res_273_ = l_Std_Time_instDecidableEqTimeZone(v_x_271_, v_x_272_);
lean_dec_ref(v_x_272_);
lean_dec_ref(v_x_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_UTC___closed__1(void){
_start:
{
uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_276_ = 0;
v___x_277_ = ((lean_object*)(l_Std_Time_TimeZone_UTC___closed__0));
v___x_278_ = l_Std_Time_TimeZone_Offset_zero;
v___x_279_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_277_);
lean_ctor_set(v___x_279_, 2, v___x_277_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*3, v___x_276_);
return v___x_279_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_UTC(void){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_obj_once(&l_Std_Time_TimeZone_UTC___closed__1, &l_Std_Time_TimeZone_UTC___closed__1_once, _init_l_Std_Time_TimeZone_UTC___closed__1);
return v___x_280_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_GMT___closed__2(void){
_start:
{
uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_283_ = 0;
v___x_284_ = ((lean_object*)(l_Std_Time_TimeZone_GMT___closed__1));
v___x_285_ = ((lean_object*)(l_Std_Time_TimeZone_GMT___closed__0));
v___x_286_ = l_Std_Time_TimeZone_Offset_zero;
v___x_287_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_285_);
lean_ctor_set(v___x_287_, 2, v___x_284_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*3, v___x_283_);
return v___x_287_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_GMT(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_obj_once(&l_Std_Time_TimeZone_GMT___closed__2, &l_Std_Time_TimeZone_GMT___closed__2_once, _init_l_Std_Time_TimeZone_GMT___closed__2);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours(lean_object* v_name_289_, lean_object* v_abbreviation_290_, lean_object* v_n_291_, uint8_t v_isDST_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = l_Std_Time_TimeZone_Offset_ofHours(v_n_291_);
v___x_294_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_name_289_);
lean_ctor_set(v___x_294_, 2, v_abbreviation_290_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*3, v_isDST_292_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours___boxed(lean_object* v_name_295_, lean_object* v_abbreviation_296_, lean_object* v_n_297_, lean_object* v_isDST_298_){
_start:
{
uint8_t v_isDST_boxed_299_; lean_object* v_res_300_; 
v_isDST_boxed_299_ = lean_unbox(v_isDST_298_);
v_res_300_ = l_Std_Time_TimeZone_ofHours(v_name_295_, v_abbreviation_296_, v_n_297_, v_isDST_boxed_299_);
lean_dec(v_n_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds(lean_object* v_name_301_, lean_object* v_abbreviation_302_, lean_object* v_n_303_, uint8_t v_isDST_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_305_, 0, v_n_303_);
lean_ctor_set(v___x_305_, 1, v_name_301_);
lean_ctor_set(v___x_305_, 2, v_abbreviation_302_);
lean_ctor_set_uint8(v___x_305_, sizeof(void*)*3, v_isDST_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds___boxed(lean_object* v_name_306_, lean_object* v_abbreviation_307_, lean_object* v_n_308_, lean_object* v_isDST_309_){
_start:
{
uint8_t v_isDST_boxed_310_; lean_object* v_res_311_; 
v_isDST_boxed_310_ = lean_unbox(v_isDST_309_);
v_res_311_ = l_Std_Time_TimeZone_ofSeconds(v_name_306_, v_abbreviation_307_, v_n_308_, v_isDST_boxed_310_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds(lean_object* v_tz_312_){
_start:
{
lean_object* v_offset_313_; 
v_offset_313_ = lean_ctor_get(v_tz_312_, 0);
lean_inc(v_offset_313_);
return v_offset_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds___boxed(lean_object* v_tz_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Std_Time_TimeZone_toSeconds(v_tz_314_);
lean_dec_ref(v_tz_314_);
return v_res_315_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toWallTime___closed__0(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(1000000000u);
v___x_317_ = lean_nat_to_int(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime(lean_object* v_ts_318_, lean_object* v_offset_319_){
_start:
{
lean_object* v_second_320_; lean_object* v_nano_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_second_320_ = lean_ctor_get(v_ts_318_, 0);
v_nano_321_ = lean_ctor_get(v_ts_318_, 1);
v___x_322_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_323_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_324_ = lean_int_mul(v_second_320_, v___x_323_);
v___x_325_ = lean_int_add(v___x_324_, v_nano_321_);
lean_dec(v___x_324_);
v___x_326_ = lean_int_mul(v_offset_319_, v___x_323_);
v___x_327_ = lean_int_add(v___x_326_, v___x_322_);
lean_dec(v___x_326_);
v___x_328_ = lean_int_add(v___x_325_, v___x_327_);
lean_dec(v___x_327_);
lean_dec(v___x_325_);
v___x_329_ = l_Std_Time_Duration_ofNanoseconds(v___x_328_);
lean_dec(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime___boxed(lean_object* v_ts_330_, lean_object* v_offset_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Std_Time_Timestamp_toWallTime(v_ts_330_, v_offset_331_);
lean_dec(v_offset_331_);
lean_dec_ref(v_ts_330_);
return v_res_332_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofWallTime___closed__0(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_334_ = lean_int_neg(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime(lean_object* v_wt_335_, lean_object* v_offset_336_){
_start:
{
lean_object* v_second_337_; lean_object* v_nano_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_second_337_ = lean_ctor_get(v_wt_335_, 0);
v_nano_338_ = lean_ctor_get(v_wt_335_, 1);
v___x_339_ = lean_int_neg(v_offset_336_);
v___x_340_ = lean_obj_once(&l_Std_Time_Timestamp_ofWallTime___closed__0, &l_Std_Time_Timestamp_ofWallTime___closed__0_once, _init_l_Std_Time_Timestamp_ofWallTime___closed__0);
v___x_341_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_342_ = lean_int_mul(v_second_337_, v___x_341_);
v___x_343_ = lean_int_add(v___x_342_, v_nano_338_);
lean_dec(v___x_342_);
v___x_344_ = lean_int_mul(v___x_339_, v___x_341_);
lean_dec(v___x_339_);
v___x_345_ = lean_int_add(v___x_344_, v___x_340_);
lean_dec(v___x_344_);
v___x_346_ = lean_int_add(v___x_343_, v___x_345_);
lean_dec(v___x_345_);
lean_dec(v___x_343_);
v___x_347_ = l_Std_Time_Duration_ofNanoseconds(v___x_346_);
lean_dec(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime___boxed(lean_object* v_wt_348_, lean_object* v_offset_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Std_Time_Timestamp_ofWallTime(v_wt_348_, v_offset_349_);
lean_dec(v_offset_349_);
lean_dec_ref(v_wt_348_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp(lean_object* v_wt_351_, lean_object* v_offset_352_){
_start:
{
lean_object* v_second_353_; lean_object* v_nano_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v_second_353_ = lean_ctor_get(v_wt_351_, 0);
v_nano_354_ = lean_ctor_get(v_wt_351_, 1);
v___x_355_ = lean_int_neg(v_offset_352_);
v___x_356_ = lean_obj_once(&l_Std_Time_Timestamp_ofWallTime___closed__0, &l_Std_Time_Timestamp_ofWallTime___closed__0_once, _init_l_Std_Time_Timestamp_ofWallTime___closed__0);
v___x_357_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_358_ = lean_int_mul(v_second_353_, v___x_357_);
v___x_359_ = lean_int_add(v___x_358_, v_nano_354_);
lean_dec(v___x_358_);
v___x_360_ = lean_int_mul(v___x_355_, v___x_357_);
lean_dec(v___x_355_);
v___x_361_ = lean_int_add(v___x_360_, v___x_356_);
lean_dec(v___x_360_);
v___x_362_ = lean_int_add(v___x_359_, v___x_361_);
lean_dec(v___x_361_);
lean_dec(v___x_359_);
v___x_363_ = l_Std_Time_Duration_ofNanoseconds(v___x_362_);
lean_dec(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp___boxed(lean_object* v_wt_364_, lean_object* v_offset_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_Time_WallTime_toTimestamp(v_wt_364_, v_offset_365_);
lean_dec(v_offset_365_);
lean_dec_ref(v_wt_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp(lean_object* v_ts_367_, lean_object* v_offset_368_){
_start:
{
lean_object* v_second_369_; lean_object* v_nano_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_second_369_ = lean_ctor_get(v_ts_367_, 0);
v_nano_370_ = lean_ctor_get(v_ts_367_, 1);
v___x_371_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_372_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_373_ = lean_int_mul(v_second_369_, v___x_372_);
v___x_374_ = lean_int_add(v___x_373_, v_nano_370_);
lean_dec(v___x_373_);
v___x_375_ = lean_int_mul(v_offset_368_, v___x_372_);
v___x_376_ = lean_int_add(v___x_375_, v___x_371_);
lean_dec(v___x_375_);
v___x_377_ = lean_int_add(v___x_374_, v___x_376_);
lean_dec(v___x_376_);
lean_dec(v___x_374_);
v___x_378_ = l_Std_Time_Duration_ofNanoseconds(v___x_377_);
lean_dec(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp___boxed(lean_object* v_ts_379_, lean_object* v_offset_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_Time_WallTime_ofTimestamp(v_ts_379_, v_offset_380_);
lean_dec(v_offset_380_);
lean_dec_ref(v_ts_379_);
return v_res_381_;
}
}
lean_object* runtime_initialize_Std_Time_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_TimeZone(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Time_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_DateTime_Timestamp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_TimeZone_instInhabitedOffset = _init_l_Std_Time_TimeZone_instInhabitedOffset();
lean_mark_persistent(l_Std_Time_TimeZone_instInhabitedOffset);
l_Std_Time_TimeZone_Offset_zero = _init_l_Std_Time_TimeZone_Offset_zero();
lean_mark_persistent(l_Std_Time_TimeZone_Offset_zero);
l_Std_Time_instInhabitedTimeZone_default = _init_l_Std_Time_instInhabitedTimeZone_default();
lean_mark_persistent(l_Std_Time_instInhabitedTimeZone_default);
l_Std_Time_instInhabitedTimeZone = _init_l_Std_Time_instInhabitedTimeZone();
lean_mark_persistent(l_Std_Time_instInhabitedTimeZone);
l_Std_Time_TimeZone_UTC = _init_l_Std_Time_TimeZone_UTC();
lean_mark_persistent(l_Std_Time_TimeZone_UTC);
l_Std_Time_TimeZone_GMT = _init_l_Std_Time_TimeZone_GMT();
lean_mark_persistent(l_Std_Time_TimeZone_GMT);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Time_Zoned_TimeZone(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Time_Time(uint8_t builtin);
lean_object* initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Time(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_DateTime_Timestamp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Time_Zoned_TimeZone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Time_Zoned_TimeZone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Time_Zoned_TimeZone(builtin);
}
#ifdef __cplusplus
}
#endif

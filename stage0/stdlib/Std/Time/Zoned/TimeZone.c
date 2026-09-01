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
lean_inc_ref(v___y_94_);
v___x_97_ = lean_string_append(v___y_94_, v___y_95_);
lean_dec_ref(v___y_95_);
v___x_98_ = lean_string_append(v___x_97_, v___y_96_);
lean_dec_ref(v___y_96_);
return v___x_98_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_inc_ref(v___y_94_);
v___x_99_ = lean_string_append(v___y_94_, v___y_95_);
lean_dec_ref(v___y_95_);
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
v___x_108_ = l_Int_repr(v___y_106_);
lean_dec(v___y_106_);
v___y_94_ = v___y_104_;
v___y_95_ = v___y_107_;
v___y_96_ = v___x_108_;
goto v___jp_93_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__1));
v___x_110_ = l_Int_repr(v___y_106_);
lean_dec(v___y_106_);
v___x_111_ = lean_string_append(v___x_109_, v___x_110_);
lean_dec_ref(v___x_110_);
v___y_94_ = v___y_104_;
v___y_95_ = v___y_107_;
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
v___y_104_ = v_fst_113_;
v___y_105_ = v___x_122_;
v___y_106_ = v_minute_119_;
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
v___y_104_ = v_fst_113_;
v___y_105_ = v___x_122_;
v___y_106_ = v_minute_119_;
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
lean_object* v_offset_253_; lean_object* v_name_254_; lean_object* v_abbreviation_255_; uint8_t v_isDST_256_; lean_object* v_offset_257_; lean_object* v_name_258_; lean_object* v_abbreviation_259_; uint8_t v_isDST_260_; uint8_t v___x_261_; uint8_t v___x_262_; uint8_t v___x_263_; uint8_t v___y_265_; 
v_offset_253_ = lean_ctor_get(v_x_251_, 0);
v_name_254_ = lean_ctor_get(v_x_251_, 1);
v_abbreviation_255_ = lean_ctor_get(v_x_251_, 2);
v_isDST_256_ = lean_ctor_get_uint8(v_x_251_, sizeof(void*)*3);
v_offset_257_ = lean_ctor_get(v_x_252_, 0);
v_name_258_ = lean_ctor_get(v_x_252_, 1);
v_abbreviation_259_ = lean_ctor_get(v_x_252_, 2);
v_isDST_260_ = lean_ctor_get_uint8(v_x_252_, sizeof(void*)*3);
v___x_261_ = lean_int_dec_eq(v_offset_253_, v_offset_257_);
v___x_262_ = lean_string_dec_eq(v_name_254_, v_name_258_);
v___x_263_ = lean_string_dec_eq(v_abbreviation_255_, v_abbreviation_259_);
if (v_isDST_260_ == 0)
{
if (v_isDST_256_ == 0)
{
uint8_t v___x_266_; 
v___x_266_ = 1;
v___y_265_ = v___x_266_;
goto v___jp_264_;
}
else
{
v___y_265_ = v_isDST_260_;
goto v___jp_264_;
}
}
else
{
v___y_265_ = v_isDST_256_;
goto v___jp_264_;
}
v___jp_264_:
{
if (v___x_261_ == 0)
{
return v___x_261_;
}
else
{
if (v___x_262_ == 0)
{
return v___x_262_;
}
else
{
if (v___x_263_ == 0)
{
return v___x_263_;
}
else
{
return v___y_265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone_decEq___boxed(lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_267_, v_x_268_);
lean_dec_ref(v_x_268_);
lean_dec_ref(v_x_267_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone(lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_271_, v_x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone___boxed(lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = l_Std_Time_instDecidableEqTimeZone(v_x_274_, v_x_275_);
lean_dec_ref(v_x_275_);
lean_dec_ref(v_x_274_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_UTC___closed__1(void){
_start:
{
uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_279_ = 0;
v___x_280_ = ((lean_object*)(l_Std_Time_TimeZone_UTC___closed__0));
v___x_281_ = l_Std_Time_TimeZone_Offset_zero;
v___x_282_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
lean_ctor_set(v___x_282_, 2, v___x_280_);
lean_ctor_set_uint8(v___x_282_, sizeof(void*)*3, v___x_279_);
return v___x_282_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_UTC(void){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&l_Std_Time_TimeZone_UTC___closed__1, &l_Std_Time_TimeZone_UTC___closed__1_once, _init_l_Std_Time_TimeZone_UTC___closed__1);
return v___x_283_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_GMT___closed__2(void){
_start:
{
uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_286_ = 0;
v___x_287_ = ((lean_object*)(l_Std_Time_TimeZone_GMT___closed__1));
v___x_288_ = ((lean_object*)(l_Std_Time_TimeZone_GMT___closed__0));
v___x_289_ = l_Std_Time_TimeZone_Offset_zero;
v___x_290_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_288_);
lean_ctor_set(v___x_290_, 2, v___x_287_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*3, v___x_286_);
return v___x_290_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_GMT(void){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&l_Std_Time_TimeZone_GMT___closed__2, &l_Std_Time_TimeZone_GMT___closed__2_once, _init_l_Std_Time_TimeZone_GMT___closed__2);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours(lean_object* v_name_292_, lean_object* v_abbreviation_293_, lean_object* v_n_294_, uint8_t v_isDST_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = l_Std_Time_TimeZone_Offset_ofHours(v_n_294_);
v___x_297_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_name_292_);
lean_ctor_set(v___x_297_, 2, v_abbreviation_293_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*3, v_isDST_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours___boxed(lean_object* v_name_298_, lean_object* v_abbreviation_299_, lean_object* v_n_300_, lean_object* v_isDST_301_){
_start:
{
uint8_t v_isDST_boxed_302_; lean_object* v_res_303_; 
v_isDST_boxed_302_ = lean_unbox(v_isDST_301_);
v_res_303_ = l_Std_Time_TimeZone_ofHours(v_name_298_, v_abbreviation_299_, v_n_300_, v_isDST_boxed_302_);
lean_dec(v_n_300_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds(lean_object* v_name_304_, lean_object* v_abbreviation_305_, lean_object* v_n_306_, uint8_t v_isDST_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_308_, 0, v_n_306_);
lean_ctor_set(v___x_308_, 1, v_name_304_);
lean_ctor_set(v___x_308_, 2, v_abbreviation_305_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*3, v_isDST_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds___boxed(lean_object* v_name_309_, lean_object* v_abbreviation_310_, lean_object* v_n_311_, lean_object* v_isDST_312_){
_start:
{
uint8_t v_isDST_boxed_313_; lean_object* v_res_314_; 
v_isDST_boxed_313_ = lean_unbox(v_isDST_312_);
v_res_314_ = l_Std_Time_TimeZone_ofSeconds(v_name_309_, v_abbreviation_310_, v_n_311_, v_isDST_boxed_313_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds(lean_object* v_tz_315_){
_start:
{
lean_object* v_offset_316_; 
v_offset_316_ = lean_ctor_get(v_tz_315_, 0);
lean_inc(v_offset_316_);
return v_offset_316_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds___boxed(lean_object* v_tz_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Std_Time_TimeZone_toSeconds(v_tz_317_);
lean_dec_ref(v_tz_317_);
return v_res_318_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toWallTime___closed__0(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(1000000000u);
v___x_320_ = lean_nat_to_int(v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime(lean_object* v_ts_321_, lean_object* v_offset_322_){
_start:
{
lean_object* v_second_323_; lean_object* v_nano_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_second_323_ = lean_ctor_get(v_ts_321_, 0);
v_nano_324_ = lean_ctor_get(v_ts_321_, 1);
v___x_325_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_326_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_327_ = lean_int_mul(v_second_323_, v___x_326_);
v___x_328_ = lean_int_add(v___x_327_, v_nano_324_);
lean_dec(v___x_327_);
v___x_329_ = lean_int_mul(v_offset_322_, v___x_326_);
v___x_330_ = lean_int_add(v___x_329_, v___x_325_);
lean_dec(v___x_329_);
v___x_331_ = lean_int_add(v___x_328_, v___x_330_);
lean_dec(v___x_330_);
lean_dec(v___x_328_);
v___x_332_ = l_Std_Time_Duration_ofNanoseconds(v___x_331_);
lean_dec(v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime___boxed(lean_object* v_ts_333_, lean_object* v_offset_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_Time_Timestamp_toWallTime(v_ts_333_, v_offset_334_);
lean_dec(v_offset_334_);
lean_dec_ref(v_ts_333_);
return v_res_335_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofWallTime___closed__0(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_337_ = lean_int_neg(v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime(lean_object* v_wt_338_, lean_object* v_offset_339_){
_start:
{
lean_object* v_second_340_; lean_object* v_nano_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_second_340_ = lean_ctor_get(v_wt_338_, 0);
v_nano_341_ = lean_ctor_get(v_wt_338_, 1);
v___x_342_ = lean_int_neg(v_offset_339_);
v___x_343_ = lean_obj_once(&l_Std_Time_Timestamp_ofWallTime___closed__0, &l_Std_Time_Timestamp_ofWallTime___closed__0_once, _init_l_Std_Time_Timestamp_ofWallTime___closed__0);
v___x_344_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_345_ = lean_int_mul(v_second_340_, v___x_344_);
v___x_346_ = lean_int_add(v___x_345_, v_nano_341_);
lean_dec(v___x_345_);
v___x_347_ = lean_int_mul(v___x_342_, v___x_344_);
lean_dec(v___x_342_);
v___x_348_ = lean_int_add(v___x_347_, v___x_343_);
lean_dec(v___x_347_);
v___x_349_ = lean_int_add(v___x_346_, v___x_348_);
lean_dec(v___x_348_);
lean_dec(v___x_346_);
v___x_350_ = l_Std_Time_Duration_ofNanoseconds(v___x_349_);
lean_dec(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime___boxed(lean_object* v_wt_351_, lean_object* v_offset_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_Time_Timestamp_ofWallTime(v_wt_351_, v_offset_352_);
lean_dec(v_offset_352_);
lean_dec_ref(v_wt_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp(lean_object* v_wt_354_, lean_object* v_offset_355_){
_start:
{
lean_object* v_second_356_; lean_object* v_nano_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_second_356_ = lean_ctor_get(v_wt_354_, 0);
v_nano_357_ = lean_ctor_get(v_wt_354_, 1);
v___x_358_ = lean_int_neg(v_offset_355_);
v___x_359_ = lean_obj_once(&l_Std_Time_Timestamp_ofWallTime___closed__0, &l_Std_Time_Timestamp_ofWallTime___closed__0_once, _init_l_Std_Time_Timestamp_ofWallTime___closed__0);
v___x_360_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_361_ = lean_int_mul(v_second_356_, v___x_360_);
v___x_362_ = lean_int_add(v___x_361_, v_nano_357_);
lean_dec(v___x_361_);
v___x_363_ = lean_int_mul(v___x_358_, v___x_360_);
lean_dec(v___x_358_);
v___x_364_ = lean_int_add(v___x_363_, v___x_359_);
lean_dec(v___x_363_);
v___x_365_ = lean_int_add(v___x_362_, v___x_364_);
lean_dec(v___x_364_);
lean_dec(v___x_362_);
v___x_366_ = l_Std_Time_Duration_ofNanoseconds(v___x_365_);
lean_dec(v___x_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp___boxed(lean_object* v_wt_367_, lean_object* v_offset_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Time_WallTime_toTimestamp(v_wt_367_, v_offset_368_);
lean_dec(v_offset_368_);
lean_dec_ref(v_wt_367_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp(lean_object* v_ts_370_, lean_object* v_offset_371_){
_start:
{
lean_object* v_second_372_; lean_object* v_nano_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_second_372_ = lean_ctor_get(v_ts_370_, 0);
v_nano_373_ = lean_ctor_get(v_ts_370_, 1);
v___x_374_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_375_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_376_ = lean_int_mul(v_second_372_, v___x_375_);
v___x_377_ = lean_int_add(v___x_376_, v_nano_373_);
lean_dec(v___x_376_);
v___x_378_ = lean_int_mul(v_offset_371_, v___x_375_);
v___x_379_ = lean_int_add(v___x_378_, v___x_374_);
lean_dec(v___x_378_);
v___x_380_ = lean_int_add(v___x_377_, v___x_379_);
lean_dec(v___x_379_);
lean_dec(v___x_377_);
v___x_381_ = l_Std_Time_Duration_ofNanoseconds(v___x_380_);
lean_dec(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp___boxed(lean_object* v_ts_382_, lean_object* v_offset_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_Time_WallTime_ofTimestamp(v_ts_382_, v_offset_383_);
lean_dec(v_offset_383_);
lean_dec_ref(v_ts_382_);
return v_res_384_;
}
}
lean_object* runtime_initialize_Std_Time_Time(uint8_t builtin);
lean_object* runtime_initialize_Std_Time_DateTime_Timestamp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Time_Zoned_TimeZone(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

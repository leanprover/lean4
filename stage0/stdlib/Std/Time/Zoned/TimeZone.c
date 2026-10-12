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
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_int_div(lean_object*, lean_object*);
lean_object* lean_int_mod(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
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
uint8_t l_Std_Time_TimeZone_instDecidableEqOffset_decEq(lean_object* v_x_53_, lean_object* v_x_54_){
_start:
{
uint8_t v___x_55_; 
v___x_55_ = lean_int_dec_eq(v_x_53_, v_x_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_instDecidableEqOffset_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_53_ = stack[0].m_obj;
lean_object* v_x_54_ = stack[1].m_obj;
uint8_t v_res_56_;
v_res_56_ = l_Std_Time_TimeZone_instDecidableEqOffset_decEq(v_x_53_, v_x_54_);
stack->m_num = v_res_56_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset_decEq___boxed(lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Std_Time_TimeZone_instDecidableEqOffset_decEq(v_x_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec(v_x_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
uint8_t l_Std_Time_TimeZone_instDecidableEqOffset(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = lean_int_dec_eq(v_x_61_, v_x_62_);
return v___x_63_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_instDecidableEqOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_61_ = stack[0].m_obj;
lean_object* v_x_62_ = stack[1].m_obj;
uint8_t v_res_64_;
v_res_64_ = l_Std_Time_TimeZone_instDecidableEqOffset(v_x_61_, v_x_62_);
stack->m_num = v_res_64_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instDecidableEqOffset___boxed(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
uint8_t v_res_67_; lean_object* v_r_68_; 
v_res_67_ = l_Std_Time_TimeZone_instDecidableEqOffset(v_x_65_, v_x_66_);
lean_dec(v_x_66_);
lean_dec(v_x_65_);
v_r_68_ = lean_box(v_res_67_);
return v_r_68_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedOffset___closed__0(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(0u);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_instInhabitedOffset(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_obj_once(&l_Std_Time_TimeZone_instInhabitedOffset___closed__0, &l_Std_Time_TimeZone_instInhabitedOffset___closed__0_once, _init_l_Std_Time_TimeZone_instInhabitedOffset___closed__0);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0(lean_object* v_x_72_){
_start:
{
lean_inc(v_x_72_);
return v_x_72_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_instOrdOffset___lam__0___boxed(lean_object* v_x_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Std_Time_TimeZone_instOrdOffset___lam__0(v_x_73_);
lean_dec(v_x_73_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__1(lean_object* v_a_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Rat_ofInt(v_a_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(3600u);
v___x_86_ = lean_nat_to_int(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__3(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(60u);
v___x_88_ = lean_nat_to_int(v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_nat_to_int(v___x_89_);
return v___x_90_;
}
}
lean_object* l_Std_Time_TimeZone_Offset_toIsoString(lean_object* v_offset_93_, uint8_t v_colon_94_){
_start:
{
lean_object* v___y_96_; lean_object* v___y_97_; lean_object* v___y_98_; lean_object* v___y_106_; lean_object* v___y_107_; lean_object* v___y_108_; lean_object* v___y_109_; lean_object* v_fst_116_; lean_object* v_snd_117_; lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_130_ = lean_int_dec_le(v___x_129_, v_offset_93_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__5));
v___x_132_ = lean_int_neg(v_offset_93_);
lean_dec(v_offset_93_);
v_fst_116_ = v___x_131_;
v_snd_117_ = v___x_132_;
goto v___jp_115_;
}
else
{
lean_object* v___x_133_; 
v___x_133_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__6));
v_fst_116_ = v___x_133_;
v_snd_117_ = v_offset_93_;
goto v___jp_115_;
}
v___jp_95_:
{
if (v_colon_94_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_inc_ref(v___y_97_);
v___x_99_ = lean_string_append(v___y_97_, v___y_96_);
lean_dec_ref(v___y_96_);
v___x_100_ = lean_string_append(v___x_99_, v___y_98_);
lean_dec_ref(v___y_98_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
lean_inc_ref(v___y_97_);
v___x_101_ = lean_string_append(v___y_97_, v___y_96_);
lean_dec_ref(v___y_96_);
v___x_102_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__0));
v___x_103_ = lean_string_append(v___x_101_, v___x_102_);
v___x_104_ = lean_string_append(v___x_103_, v___y_98_);
lean_dec_ref(v___y_98_);
return v___x_104_;
}
}
v___jp_105_:
{
uint8_t v___x_110_; 
v___x_110_ = lean_int_dec_lt(v___y_107_, v___y_106_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; 
v___x_111_ = l_Int_repr(v___y_107_);
lean_dec(v___y_107_);
v___y_96_ = v___y_109_;
v___y_97_ = v___y_108_;
v___y_98_ = v___x_111_;
goto v___jp_95_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__1));
v___x_113_ = l_Int_repr(v___y_107_);
lean_dec(v___y_107_);
v___x_114_ = lean_string_append(v___x_112_, v___x_113_);
lean_dec_ref(v___x_113_);
v___y_96_ = v___y_109_;
v___y_97_ = v___y_108_;
v___y_98_ = v___x_114_;
goto v___jp_95_;
}
}
v___jp_115_:
{
lean_object* v___x_118_; lean_object* v_hour_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_minute_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_118_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__2, &l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2);
v_hour_119_ = lean_int_div(v_snd_117_, v___x_118_);
v___x_120_ = lean_int_mod(v_snd_117_, v___x_118_);
lean_dec(v_snd_117_);
v___x_121_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__3, &l_Std_Time_TimeZone_Offset_toIsoString___closed__3_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__3);
v_minute_122_ = lean_int_ediv(v___x_120_, v___x_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7);
v___x_124_ = lean_int_dec_lt(v_hour_119_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
v___x_125_ = l_Int_repr(v_hour_119_);
lean_dec(v_hour_119_);
v___y_106_ = v___x_123_;
v___y_107_ = v_minute_122_;
v___y_108_ = v_fst_116_;
v___y_109_ = v___x_125_;
goto v___jp_105_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = ((lean_object*)(l_Std_Time_TimeZone_Offset_toIsoString___closed__1));
v___x_127_ = l_Int_repr(v_hour_119_);
lean_dec(v_hour_119_);
v___x_128_ = lean_string_append(v___x_126_, v___x_127_);
lean_dec_ref(v___x_127_);
v___y_106_ = v___x_123_;
v___y_107_ = v_minute_122_;
v___y_108_ = v_fst_116_;
v___y_109_ = v___x_128_;
goto v___jp_105_;
}
}
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_Offset_toIsoString_0interp(lean_interpreter_value* stack)
{
lean_object* v_offset_93_ = stack[0].m_obj;
uint8_t v_colon_94_ = stack[1].m_num;
lean_object* v_res_134_;
v_res_134_ = l_Std_Time_TimeZone_Offset_toIsoString(v_offset_93_, v_colon_94_);
stack->m_obj
 = v_res_134_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_toIsoString___boxed(lean_object* v_offset_135_, lean_object* v_colon_136_){
_start:
{
uint8_t v_colon_boxed_137_; lean_object* v_res_138_; 
v_colon_boxed_137_ = lean_unbox(v_colon_136_);
v_res_138_ = l_Std_Time_TimeZone_Offset_toIsoString(v_offset_135_, v_colon_boxed_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Time_TimeZone_Offset_toIsoString_spec__0(lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_nat_to_int(v_a_139_);
v___x_141_ = l_Rat_ofInt(v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_Offset_zero(void){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours(lean_object* v_n_143_){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__2, &l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2);
v___x_145_ = lean_int_mul(v_n_143_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHours___boxed(lean_object* v_n_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Std_Time_TimeZone_Offset_ofHours(v_n_146_);
lean_dec(v_n_146_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(lean_object* v_n_148_, lean_object* v_m_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_150_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__2, &l_Std_Time_TimeZone_Offset_toIsoString___closed__2_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__2);
v___x_151_ = lean_int_mul(v_n_148_, v___x_150_);
v___x_152_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__3, &l_Std_Time_TimeZone_Offset_toIsoString___closed__3_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__3);
v___x_153_ = lean_int_mul(v_m_149_, v___x_152_);
v___x_154_ = lean_int_add(v___x_151_, v___x_153_);
lean_dec(v___x_153_);
lean_dec(v___x_151_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_Offset_ofHoursAndMinutes___boxed(lean_object* v_n_155_, lean_object* v_m_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_Time_TimeZone_Offset_ofHoursAndMinutes(v_n_155_, v_m_156_);
lean_dec(v_m_156_);
lean_dec(v_n_155_);
return v_res_157_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimeZone_default___closed__1(void){
_start:
{
uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_159_ = 0;
v___x_160_ = ((lean_object*)(l_Std_Time_instInhabitedTimeZone_default___closed__0));
v___x_161_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_162_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
lean_ctor_set(v___x_162_, 2, v___x_160_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*3, v___x_159_);
return v___x_162_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimeZone_default(void){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&l_Std_Time_instInhabitedTimeZone_default___closed__1, &l_Std_Time_instInhabitedTimeZone_default___closed__1_once, _init_l_Std_Time_instInhabitedTimeZone_default___closed__1);
return v___x_163_;
}
}
static lean_object* _init_l_Std_Time_instInhabitedTimeZone(void){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l_Std_Time_instInhabitedTimeZone_default;
return v___x_164_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__8(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(8u);
v___x_181_ = lean_nat_to_int(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(16u);
v___x_186_ = lean_nat_to_int(v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_unsigned_to_nat(9u);
v___x_191_ = lean_nat_to_int(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr___redArg(lean_object* v_x_192_){
_start:
{
lean_object* v_offset_193_; lean_object* v_name_194_; lean_object* v_abbreviation_195_; uint8_t v_isDST_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v_offset_193_ = lean_ctor_get(v_x_192_, 0);
lean_inc(v_offset_193_);
v_name_194_ = lean_ctor_get(v_x_192_, 1);
lean_inc_ref(v_name_194_);
v_abbreviation_195_ = lean_ctor_get(v_x_192_, 2);
lean_inc_ref(v_abbreviation_195_);
v_isDST_196_ = lean_ctor_get_uint8(v_x_192_, sizeof(void*)*3);
lean_dec_ref(v_x_192_);
v___x_197_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__5));
v___x_198_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__3));
v___x_199_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__7);
v___x_200_ = l_Std_Time_TimeZone_instReprOffset_repr___redArg(v_offset_193_);
lean_dec(v_offset_193_);
v___x_201_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = 0;
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_202_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_198_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__5));
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
v___x_207_ = lean_box(1);
v___x_208_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__7));
v___x_210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_197_);
v___x_212_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__8, &l_Std_Time_instReprTimeZone_repr___redArg___closed__8_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__8);
v___x_213_ = l_String_quote(v_name_194_);
v___x_214_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
v___x_215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_212_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*1, v___x_202_);
v___x_217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_211_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set(v___x_218_, 1, v___x_205_);
v___x_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
lean_ctor_set(v___x_219_, 1, v___x_207_);
v___x_220_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__10));
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_197_);
v___x_223_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__11, &l_Std_Time_instReprTimeZone_repr___redArg___closed__11_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__11);
v___x_224_ = l_String_quote(v_abbreviation_195_);
v___x_225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
v___x_226_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_223_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*1, v___x_202_);
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_222_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_205_);
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_207_);
v___x_231_ = ((lean_object*)(l_Std_Time_instReprTimeZone_repr___redArg___closed__13));
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v___x_197_);
v___x_234_ = lean_obj_once(&l_Std_Time_instReprTimeZone_repr___redArg___closed__14, &l_Std_Time_instReprTimeZone_repr___redArg___closed__14_once, _init_l_Std_Time_instReprTimeZone_repr___redArg___closed__14);
v___x_235_ = l_Bool_repr___redArg(v_isDST_196_);
v___x_236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set_uint8(v___x_237_, sizeof(void*)*1, v___x_202_);
v___x_238_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_233_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_obj_once(&l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10, &l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10_once, _init_l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__10);
v___x_240_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__11));
v___x_241_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___x_238_);
v___x_242_ = ((lean_object*)(l_Std_Time_TimeZone_instReprOffset_repr___redArg___closed__12));
v___x_243_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_239_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_202_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr(lean_object* v_x_246_, lean_object* v_prec_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l_Std_Time_instReprTimeZone_repr___redArg(v_x_246_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone_repr___boxed(lean_object* v_x_249_, lean_object* v_prec_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_Time_instReprTimeZone_repr(v_x_249_, v_prec_250_);
lean_dec(v_prec_250_);
return v_res_251_;
}
}
uint8_t l_Std_Time_instDecidableEqTimeZone_decEq(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
lean_object* v_offset_256_; lean_object* v_name_257_; lean_object* v_abbreviation_258_; uint8_t v_isDST_259_; lean_object* v_offset_260_; lean_object* v_name_261_; lean_object* v_abbreviation_262_; uint8_t v_isDST_263_; uint8_t v___x_264_; 
v_offset_256_ = lean_ctor_get(v_x_254_, 0);
v_name_257_ = lean_ctor_get(v_x_254_, 1);
v_abbreviation_258_ = lean_ctor_get(v_x_254_, 2);
v_isDST_259_ = lean_ctor_get_uint8(v_x_254_, sizeof(void*)*3);
v_offset_260_ = lean_ctor_get(v_x_255_, 0);
v_name_261_ = lean_ctor_get(v_x_255_, 1);
v_abbreviation_262_ = lean_ctor_get(v_x_255_, 2);
v_isDST_263_ = lean_ctor_get_uint8(v_x_255_, sizeof(void*)*3);
v___x_264_ = lean_int_dec_eq(v_offset_256_, v_offset_260_);
if (v___x_264_ == 0)
{
return v___x_264_;
}
else
{
uint8_t v___x_265_; 
v___x_265_ = lean_string_dec_eq(v_name_257_, v_name_261_);
if (v___x_265_ == 0)
{
return v___x_265_;
}
else
{
uint8_t v___x_266_; 
v___x_266_ = lean_string_dec_eq(v_abbreviation_258_, v_abbreviation_262_);
if (v___x_266_ == 0)
{
return v___x_266_;
}
else
{
if (v_isDST_263_ == 0)
{
if (v_isDST_259_ == 0)
{
return v___x_266_;
}
else
{
return v_isDST_263_;
}
}
else
{
return v_isDST_259_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqTimeZone_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_254_ = stack[0].m_obj;
lean_object* v_x_255_ = stack[1].m_obj;
uint8_t v_res_267_;
v_res_267_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_254_, v_x_255_);
stack->m_num = v_res_267_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone_decEq___boxed(lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
uint8_t v_res_270_; lean_object* v_r_271_; 
v_res_270_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_268_, v_x_269_);
lean_dec_ref(v_x_269_);
lean_dec_ref(v_x_268_);
v_r_271_ = lean_box(v_res_270_);
return v_r_271_;
}
}
uint8_t l_Std_Time_instDecidableEqTimeZone(lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = l_Std_Time_instDecidableEqTimeZone_decEq(v_x_272_, v_x_273_);
return v___x_274_;
}
}
LEAN_EXPORT void l_Std_Time_instDecidableEqTimeZone_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_272_ = stack[0].m_obj;
lean_object* v_x_273_ = stack[1].m_obj;
uint8_t v_res_275_;
v_res_275_ = l_Std_Time_instDecidableEqTimeZone(v_x_272_, v_x_273_);
stack->m_num = v_res_275_;
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone___boxed(lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_res_278_; lean_object* v_r_279_; 
v_res_278_ = l_Std_Time_instDecidableEqTimeZone(v_x_276_, v_x_277_);
lean_dec_ref(v_x_277_);
lean_dec_ref(v_x_276_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_UTC___closed__1(void){
_start:
{
uint8_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_281_ = 0;
v___x_282_ = ((lean_object*)(l_Std_Time_TimeZone_UTC___closed__0));
v___x_283_ = l_Std_Time_TimeZone_Offset_zero;
v___x_284_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_282_);
lean_ctor_set(v___x_284_, 2, v___x_282_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*3, v___x_281_);
return v___x_284_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_UTC(void){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = lean_obj_once(&l_Std_Time_TimeZone_UTC___closed__1, &l_Std_Time_TimeZone_UTC___closed__1_once, _init_l_Std_Time_TimeZone_UTC___closed__1);
return v___x_285_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_GMT___closed__2(void){
_start:
{
uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_288_ = 0;
v___x_289_ = ((lean_object*)(l_Std_Time_TimeZone_GMT___closed__1));
v___x_290_ = ((lean_object*)(l_Std_Time_TimeZone_GMT___closed__0));
v___x_291_ = l_Std_Time_TimeZone_Offset_zero;
v___x_292_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_290_);
lean_ctor_set(v___x_292_, 2, v___x_289_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*3, v___x_288_);
return v___x_292_;
}
}
static lean_object* _init_l_Std_Time_TimeZone_GMT(void){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = lean_obj_once(&l_Std_Time_TimeZone_GMT___closed__2, &l_Std_Time_TimeZone_GMT___closed__2_once, _init_l_Std_Time_TimeZone_GMT___closed__2);
return v___x_293_;
}
}
lean_object* l_Std_Time_TimeZone_ofHours(lean_object* v_name_294_, lean_object* v_abbreviation_295_, lean_object* v_n_296_, uint8_t v_isDST_297_){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = l_Std_Time_TimeZone_Offset_ofHours(v_n_296_);
v___x_299_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v_name_294_);
lean_ctor_set(v___x_299_, 2, v_abbreviation_295_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*3, v_isDST_297_);
return v___x_299_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_ofHours_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_294_ = stack[0].m_obj;
lean_object* v_abbreviation_295_ = stack[1].m_obj;
lean_object* v_n_296_ = stack[2].m_obj;
uint8_t v_isDST_297_ = stack[3].m_num;
lean_object* v_res_300_;
v_res_300_ = l_Std_Time_TimeZone_ofHours(v_name_294_, v_abbreviation_295_, v_n_296_, v_isDST_297_);
stack->m_obj
 = v_res_300_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours___boxed(lean_object* v_name_301_, lean_object* v_abbreviation_302_, lean_object* v_n_303_, lean_object* v_isDST_304_){
_start:
{
uint8_t v_isDST_boxed_305_; lean_object* v_res_306_; 
v_isDST_boxed_305_ = lean_unbox(v_isDST_304_);
v_res_306_ = l_Std_Time_TimeZone_ofHours(v_name_301_, v_abbreviation_302_, v_n_303_, v_isDST_boxed_305_);
lean_dec(v_n_303_);
return v_res_306_;
}
}
lean_object* l_Std_Time_TimeZone_ofSeconds(lean_object* v_name_307_, lean_object* v_abbreviation_308_, lean_object* v_n_309_, uint8_t v_isDST_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_311_, 0, v_n_309_);
lean_ctor_set(v___x_311_, 1, v_name_307_);
lean_ctor_set(v___x_311_, 2, v_abbreviation_308_);
lean_ctor_set_uint8(v___x_311_, sizeof(void*)*3, v_isDST_310_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Std_Time_TimeZone_ofSeconds_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_307_ = stack[0].m_obj;
lean_object* v_abbreviation_308_ = stack[1].m_obj;
lean_object* v_n_309_ = stack[2].m_obj;
uint8_t v_isDST_310_ = stack[3].m_num;
lean_object* v_res_312_;
v_res_312_ = l_Std_Time_TimeZone_ofSeconds(v_name_307_, v_abbreviation_308_, v_n_309_, v_isDST_310_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds___boxed(lean_object* v_name_313_, lean_object* v_abbreviation_314_, lean_object* v_n_315_, lean_object* v_isDST_316_){
_start:
{
uint8_t v_isDST_boxed_317_; lean_object* v_res_318_; 
v_isDST_boxed_317_ = lean_unbox(v_isDST_316_);
v_res_318_ = l_Std_Time_TimeZone_ofSeconds(v_name_313_, v_abbreviation_314_, v_n_315_, v_isDST_boxed_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds(lean_object* v_tz_319_){
_start:
{
lean_object* v_offset_320_; 
v_offset_320_ = lean_ctor_get(v_tz_319_, 0);
lean_inc(v_offset_320_);
return v_offset_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds___boxed(lean_object* v_tz_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_Time_TimeZone_toSeconds(v_tz_321_);
lean_dec_ref(v_tz_321_);
return v_res_322_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_toWallTime___closed__0(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(1000000000u);
v___x_324_ = lean_nat_to_int(v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime(lean_object* v_ts_325_, lean_object* v_offset_326_){
_start:
{
lean_object* v_second_327_; lean_object* v_nano_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_nanos_332_; lean_object* v___x_333_; lean_object* v_nanos_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v_second_327_ = lean_ctor_get(v_ts_325_, 0);
v_nano_328_ = lean_ctor_get(v_ts_325_, 1);
v___x_329_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_330_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_331_ = lean_int_mul(v_second_327_, v___x_330_);
v_nanos_332_ = lean_int_add(v___x_331_, v_nano_328_);
lean_dec(v___x_331_);
v___x_333_ = lean_int_mul(v_offset_326_, v___x_330_);
v_nanos_334_ = lean_int_add(v___x_333_, v___x_329_);
lean_dec(v___x_333_);
v___x_335_ = lean_int_add(v_nanos_332_, v_nanos_334_);
lean_dec(v_nanos_334_);
lean_dec(v_nanos_332_);
v___x_336_ = l_Std_Time_Duration_ofNanoseconds(v___x_335_);
lean_dec(v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_toWallTime___boxed(lean_object* v_ts_337_, lean_object* v_offset_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Std_Time_Timestamp_toWallTime(v_ts_337_, v_offset_338_);
lean_dec(v_offset_338_);
lean_dec_ref(v_ts_337_);
return v_res_339_;
}
}
static lean_object* _init_l_Std_Time_Timestamp_ofWallTime___closed__0(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_341_ = lean_int_neg(v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime(lean_object* v_wt_342_, lean_object* v_offset_343_){
_start:
{
lean_object* v_second_344_; lean_object* v_nano_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v_nanos_350_; lean_object* v___x_351_; lean_object* v_nanos_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_second_344_ = lean_ctor_get(v_wt_342_, 0);
v_nano_345_ = lean_ctor_get(v_wt_342_, 1);
v___x_346_ = lean_int_neg(v_offset_343_);
v___x_347_ = lean_obj_once(&l_Std_Time_Timestamp_ofWallTime___closed__0, &l_Std_Time_Timestamp_ofWallTime___closed__0_once, _init_l_Std_Time_Timestamp_ofWallTime___closed__0);
v___x_348_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_349_ = lean_int_mul(v_second_344_, v___x_348_);
v_nanos_350_ = lean_int_add(v___x_349_, v_nano_345_);
lean_dec(v___x_349_);
v___x_351_ = lean_int_mul(v___x_346_, v___x_348_);
lean_dec(v___x_346_);
v_nanos_352_ = lean_int_add(v___x_351_, v___x_347_);
lean_dec(v___x_351_);
v___x_353_ = lean_int_add(v_nanos_350_, v_nanos_352_);
lean_dec(v_nanos_352_);
lean_dec(v_nanos_350_);
v___x_354_ = l_Std_Time_Duration_ofNanoseconds(v___x_353_);
lean_dec(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_Timestamp_ofWallTime___boxed(lean_object* v_wt_355_, lean_object* v_offset_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_Time_Timestamp_ofWallTime(v_wt_355_, v_offset_356_);
lean_dec(v_offset_356_);
lean_dec_ref(v_wt_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp(lean_object* v_wt_358_, lean_object* v_offset_359_){
_start:
{
lean_object* v_second_360_; lean_object* v_nano_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_nanos_366_; lean_object* v___x_367_; lean_object* v_nanos_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_second_360_ = lean_ctor_get(v_wt_358_, 0);
v_nano_361_ = lean_ctor_get(v_wt_358_, 1);
v___x_362_ = lean_int_neg(v_offset_359_);
v___x_363_ = lean_obj_once(&l_Std_Time_Timestamp_ofWallTime___closed__0, &l_Std_Time_Timestamp_ofWallTime___closed__0_once, _init_l_Std_Time_Timestamp_ofWallTime___closed__0);
v___x_364_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_365_ = lean_int_mul(v_second_360_, v___x_364_);
v_nanos_366_ = lean_int_add(v___x_365_, v_nano_361_);
lean_dec(v___x_365_);
v___x_367_ = lean_int_mul(v___x_362_, v___x_364_);
lean_dec(v___x_362_);
v_nanos_368_ = lean_int_add(v___x_367_, v___x_363_);
lean_dec(v___x_367_);
v___x_369_ = lean_int_add(v_nanos_366_, v_nanos_368_);
lean_dec(v_nanos_368_);
lean_dec(v_nanos_366_);
v___x_370_ = l_Std_Time_Duration_ofNanoseconds(v___x_369_);
lean_dec(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_toTimestamp___boxed(lean_object* v_wt_371_, lean_object* v_offset_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_Time_WallTime_toTimestamp(v_wt_371_, v_offset_372_);
lean_dec(v_offset_372_);
lean_dec_ref(v_wt_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp(lean_object* v_ts_374_, lean_object* v_offset_375_){
_start:
{
lean_object* v_second_376_; lean_object* v_nano_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_nanos_381_; lean_object* v___x_382_; lean_object* v_nanos_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_second_376_ = lean_ctor_get(v_ts_374_, 0);
v_nano_377_ = lean_ctor_get(v_ts_374_, 1);
v___x_378_ = lean_obj_once(&l_Std_Time_TimeZone_Offset_toIsoString___closed__4, &l_Std_Time_TimeZone_Offset_toIsoString___closed__4_once, _init_l_Std_Time_TimeZone_Offset_toIsoString___closed__4);
v___x_379_ = lean_obj_once(&l_Std_Time_Timestamp_toWallTime___closed__0, &l_Std_Time_Timestamp_toWallTime___closed__0_once, _init_l_Std_Time_Timestamp_toWallTime___closed__0);
v___x_380_ = lean_int_mul(v_second_376_, v___x_379_);
v_nanos_381_ = lean_int_add(v___x_380_, v_nano_377_);
lean_dec(v___x_380_);
v___x_382_ = lean_int_mul(v_offset_375_, v___x_379_);
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
LEAN_EXPORT lean_object* l_Std_Time_WallTime_ofTimestamp___boxed(lean_object* v_ts_386_, lean_object* v_offset_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_Time_WallTime_ofTimestamp(v_ts_386_, v_offset_387_);
lean_dec(v_offset_387_);
lean_dec_ref(v_ts_386_);
return v_res_388_;
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

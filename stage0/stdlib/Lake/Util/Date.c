// Lean compiler output
// Module: Lake.Util.Date
// Imports: public import Init.Data.Ord.Basic public import Lean.Data.Json import Lake.Util.String import Init.Data.String.Search import Init.Data.Iterators.Consumers.Collect import Init.Data.ToString.Macro
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
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lake_zpad(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static const lean_ctor_object l_Lake_instInhabitedDate_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedDate_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedDate_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedDate_default = (const lean_object*)&l_Lake_instInhabitedDate_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedDate = (const lean_object*)&l_Lake_instInhabitedDate_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqDate_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instOrdDate_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdDate_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instOrdDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instOrdDate_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instOrdDate___closed__0 = (const lean_object*)&l_Lake_instOrdDate___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instOrdDate = (const lean_object*)&l_Lake_instOrdDate___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprDate_repr_spec__0(lean_object*);
static const lean_string_object l_Lake_instReprDate_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprDate_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "year"};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprDate_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDate_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprDate_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprDate_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprDate_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprDate_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDate_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprDate_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprDate_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprDate_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprDate_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprDate_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprDate_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDate_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__9_value;
static const lean_string_object l_Lake_instReprDate_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "month"};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__10 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lake_instReprDate_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDate_repr___redArg___closed__10_value)}};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lake_instReprDate_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__12;
static const lean_string_object l_Lake_instReprDate_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "day"};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__13 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lake_instReprDate_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDate_repr___redArg___closed__13_value)}};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lake_instReprDate_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__15;
static const lean_string_object l_Lake_instReprDate_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__16 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__16_value;
static lean_once_cell_t l_Lake_instReprDate_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__17;
static lean_once_cell_t l_Lake_instReprDate_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprDate_repr___redArg___closed__18;
static const lean_ctor_object l_Lake_instReprDate_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDate_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__19 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lake_instReprDate_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDate_repr___redArg___closed__16_value)}};
static const lean_object* l_Lake_instReprDate_repr___redArg___closed__20 = (const lean_object*)&l_Lake_instReprDate_repr___redArg___closed__20_value;
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprDate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprDate_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprDate___closed__0 = (const lean_object*)&l_Lake_instReprDate___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprDate = (const lean_object*)&l_Lake_instReprDate___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Date_instLT;
LEAN_EXPORT lean_object* l_Lake_Date_instLE;
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Date_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Date_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Date_instMin___closed__0 = (const lean_object*)&l_Lake_Date_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Date_instMin = (const lean_object*)&l_Lake_Date_instMin___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Date_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Date_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Date_instMax___closed__0 = (const lean_object*)&l_Lake_Date_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Date_instMax = (const lean_object*)&l_Lake_Date_instMax___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Date_maxDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_maxDay___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_ofValid_x3f(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Date_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Date_ofString_x3f___closed__0 = (const lean_object*)&l_Lake_Date_ofString_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Date_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Date_fromJson_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "expected date"};
static const lean_object* l_Lake_Date_fromJson_x3f___closed__0 = (const lean_object*)&l_Lake_Date_fromJson_x3f___closed__0_value;
static const lean_ctor_object l_Lake_Date_fromJson_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_Date_fromJson_x3f___closed__0_value)}};
static const lean_object* l_Lake_Date_fromJson_x3f___closed__1 = (const lean_object*)&l_Lake_Date_fromJson_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Date_fromJson_x3f(lean_object*);
static const lean_closure_object l_Lake_Date_instFromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Date_fromJson_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Date_instFromJson___closed__0 = (const lean_object*)&l_Lake_Date_instFromJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Date_instFromJson = (const lean_object*)&l_Lake_Date_instFromJson___closed__0_value;
static const lean_string_object l_Lake_Date_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_Date_toString___closed__0 = (const lean_object*)&l_Lake_Date_toString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Date_toString(lean_object*);
static const lean_closure_object l_Lake_Date_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Date_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Date_instToString___closed__0 = (const lean_object*)&l_Lake_Date_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Date_instToString = (const lean_object*)&l_Lake_Date_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Date_toJson(lean_object*);
static const lean_closure_object l_Lake_Date_instToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Date_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Date_instToJson___closed__0 = (const lean_object*)&l_Lake_Date_instToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Date_instToJson = (const lean_object*)&l_Lake_Date_instToJson___closed__0_value;
uint8_t l_Lake_instDecidableEqDate_decEq(lean_object* v_x_5_, lean_object* v_x_6_){
_start:
{
lean_object* v_year_7_; lean_object* v_month_8_; lean_object* v_day_9_; lean_object* v_year_10_; lean_object* v_month_11_; lean_object* v_day_12_; uint8_t v___x_13_; 
v_year_7_ = lean_ctor_get(v_x_5_, 0);
v_month_8_ = lean_ctor_get(v_x_5_, 1);
v_day_9_ = lean_ctor_get(v_x_5_, 2);
v_year_10_ = lean_ctor_get(v_x_6_, 0);
v_month_11_ = lean_ctor_get(v_x_6_, 1);
v_day_12_ = lean_ctor_get(v_x_6_, 2);
v___x_13_ = lean_nat_dec_eq(v_year_7_, v_year_10_);
if (v___x_13_ == 0)
{
return v___x_13_;
}
else
{
uint8_t v___x_14_; 
v___x_14_ = lean_nat_dec_eq(v_month_8_, v_month_11_);
if (v___x_14_ == 0)
{
return v___x_14_;
}
else
{
uint8_t v___x_15_; 
v___x_15_ = lean_nat_dec_eq(v_day_9_, v_day_12_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT void l_Lake_instDecidableEqDate_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5_ = stack[0].m_obj;
lean_object* v_x_6_ = stack[1].m_obj;
uint8_t v_res_16_;
v_res_16_ = l_Lake_instDecidableEqDate_decEq(v_x_5_, v_x_6_);
stack->m_num = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate_decEq___boxed(lean_object* v_x_17_, lean_object* v_x_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Lake_instDecidableEqDate_decEq(v_x_17_, v_x_18_);
lean_dec_ref(v_x_18_);
lean_dec_ref(v_x_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
uint8_t l_Lake_instDecidableEqDate(lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
uint8_t v___x_23_; 
v___x_23_ = l_Lake_instDecidableEqDate_decEq(v_x_21_, v_x_22_);
return v___x_23_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqDate_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_21_ = stack[0].m_obj;
lean_object* v_x_22_ = stack[1].m_obj;
uint8_t v_res_24_;
v_res_24_ = l_Lake_instDecidableEqDate(v_x_21_, v_x_22_);
stack->m_num = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate___boxed(lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lake_instDecidableEqDate(v_x_25_, v_x_26_);
lean_dec_ref(v_x_26_);
lean_dec_ref(v_x_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
uint8_t l_Lake_instOrdDate_ord(lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
lean_object* v_year_31_; lean_object* v_month_32_; lean_object* v_day_33_; lean_object* v_year_34_; lean_object* v_month_35_; lean_object* v_day_36_; uint8_t v___x_37_; 
v_year_31_ = lean_ctor_get(v_x_29_, 0);
v_month_32_ = lean_ctor_get(v_x_29_, 1);
v_day_33_ = lean_ctor_get(v_x_29_, 2);
v_year_34_ = lean_ctor_get(v_x_30_, 0);
v_month_35_ = lean_ctor_get(v_x_30_, 1);
v_day_36_ = lean_ctor_get(v_x_30_, 2);
v___x_37_ = lean_nat_dec_lt(v_year_31_, v_year_34_);
if (v___x_37_ == 0)
{
uint8_t v___x_38_; 
v___x_38_ = lean_nat_dec_eq(v_year_31_, v_year_34_);
if (v___x_38_ == 0)
{
uint8_t v___x_39_; 
v___x_39_ = 2;
return v___x_39_;
}
else
{
uint8_t v___x_40_; 
v___x_40_ = lean_nat_dec_lt(v_month_32_, v_month_35_);
if (v___x_40_ == 0)
{
uint8_t v___x_41_; 
v___x_41_ = lean_nat_dec_eq(v_month_32_, v_month_35_);
if (v___x_41_ == 0)
{
uint8_t v___x_42_; 
v___x_42_ = 2;
return v___x_42_;
}
else
{
uint8_t v___x_43_; 
v___x_43_ = lean_nat_dec_lt(v_day_33_, v_day_36_);
if (v___x_43_ == 0)
{
uint8_t v___x_44_; 
v___x_44_ = lean_nat_dec_eq(v_day_33_, v_day_36_);
if (v___x_44_ == 0)
{
uint8_t v___x_45_; 
v___x_45_ = 2;
return v___x_45_;
}
else
{
uint8_t v___x_46_; 
v___x_46_ = 1;
return v___x_46_;
}
}
else
{
uint8_t v___x_47_; 
v___x_47_ = 0;
return v___x_47_;
}
}
}
else
{
uint8_t v___x_48_; 
v___x_48_ = 0;
return v___x_48_;
}
}
}
else
{
uint8_t v___x_49_; 
v___x_49_ = 0;
return v___x_49_;
}
}
}
LEAN_EXPORT void l_Lake_instOrdDate_ord_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_29_ = stack[0].m_obj;
lean_object* v_x_30_ = stack[1].m_obj;
uint8_t v_res_50_;
v_res_50_ = l_Lake_instOrdDate_ord(v_x_29_, v_x_30_);
stack->m_num = v_res_50_;
}
LEAN_EXPORT lean_object* l_Lake_instOrdDate_ord___boxed(lean_object* v_x_51_, lean_object* v_x_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Lake_instOrdDate_ord(v_x_51_, v_x_52_);
lean_dec_ref(v_x_52_);
lean_dec_ref(v_x_51_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprDate_repr_spec__0(lean_object* v_a_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_nat_to_int(v_a_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(8u);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(9u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(7u);
v___x_86_ = lean_nat_to_int(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__0));
v___x_89_ = lean_string_length(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_obj_once(&l_Lake_instReprDate_repr___redArg___closed__17, &l_Lake_instReprDate_repr___redArg___closed__17_once, _init_l_Lake_instReprDate_repr___redArg___closed__17);
v___x_91_ = lean_nat_to_int(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr___redArg(lean_object* v_x_96_){
_start:
{
lean_object* v_year_97_; lean_object* v_month_98_; lean_object* v_day_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; uint8_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_year_97_ = lean_ctor_get(v_x_96_, 0);
lean_inc(v_year_97_);
v_month_98_ = lean_ctor_get(v_x_96_, 1);
lean_inc(v_month_98_);
v_day_99_ = lean_ctor_get(v_x_96_, 2);
lean_inc(v_day_99_);
lean_dec_ref(v_x_96_);
v___x_100_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__5));
v___x_101_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__6));
v___x_102_ = lean_obj_once(&l_Lake_instReprDate_repr___redArg___closed__7, &l_Lake_instReprDate_repr___redArg___closed__7_once, _init_l_Lake_instReprDate_repr___redArg___closed__7);
v___x_103_ = l_Nat_reprFast(v_year_97_);
v___x_104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
v___x_105_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_102_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = 0;
v___x_107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*1, v___x_106_);
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_101_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__9));
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = lean_box(1);
v___x_112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_110_);
lean_ctor_set(v___x_112_, 1, v___x_111_);
v___x_113_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__11));
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
v___x_115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_100_);
v___x_116_ = lean_obj_once(&l_Lake_instReprDate_repr___redArg___closed__12, &l_Lake_instReprDate_repr___redArg___closed__12_once, _init_l_Lake_instReprDate_repr___redArg___closed__12);
v___x_117_ = l_Nat_reprFast(v_month_98_);
v___x_118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
v___x_119_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_116_);
lean_ctor_set(v___x_119_, 1, v___x_118_);
v___x_120_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_106_);
v___x_121_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_115_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_109_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_111_);
v___x_124_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__14));
v___x_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___x_100_);
v___x_127_ = lean_obj_once(&l_Lake_instReprDate_repr___redArg___closed__15, &l_Lake_instReprDate_repr___redArg___closed__15_once, _init_l_Lake_instReprDate_repr___redArg___closed__15);
v___x_128_ = l_Nat_reprFast(v_day_99_);
v___x_129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
v___x_130_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_127_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*1, v___x_106_);
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_126_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_obj_once(&l_Lake_instReprDate_repr___redArg___closed__18, &l_Lake_instReprDate_repr___redArg___closed__18_once, _init_l_Lake_instReprDate_repr___redArg___closed__18);
v___x_134_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__19));
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_132_);
v___x_136_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__20));
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_133_);
lean_ctor_set(v___x_138_, 1, v___x_137_);
v___x_139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set_uint8(v___x_139_, sizeof(void*)*1, v___x_106_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr(lean_object* v_x_140_, lean_object* v_prec_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lake_instReprDate_repr___redArg(v_x_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr___boxed(lean_object* v_x_143_, lean_object* v_prec_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lake_instReprDate_repr(v_x_143_, v_prec_144_);
lean_dec(v_prec_144_);
return v_res_145_;
}
}
static lean_object* _init_l_Lake_Date_instLT(void){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
return v___x_148_;
}
}
static lean_object* _init_l_Lake_Date_instLE(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_box(0);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0(lean_object* v_x_150_, lean_object* v_y_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = l_Lake_instOrdDate_ord(v_x_150_, v_y_151_);
if (v___x_152_ == 2)
{
lean_inc_ref(v_y_151_);
return v_y_151_;
}
else
{
lean_inc_ref(v_x_150_);
return v_x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0___boxed(lean_object* v_x_153_, lean_object* v_y_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l_Lake_Date_instMin___lam__0(v_x_153_, v_y_154_);
lean_dec_ref(v_y_154_);
lean_dec_ref(v_x_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0(lean_object* v_x_158_, lean_object* v_y_159_){
_start:
{
uint8_t v___x_160_; 
v___x_160_ = l_Lake_instOrdDate_ord(v_x_158_, v_y_159_);
if (v___x_160_ == 2)
{
lean_inc_ref(v_x_158_);
return v_x_158_;
}
else
{
lean_inc_ref(v_y_159_);
return v_y_159_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0___boxed(lean_object* v_x_161_, lean_object* v_y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lake_Date_instMax___lam__0(v_x_161_, v_y_162_);
lean_dec_ref(v_y_162_);
lean_dec_ref(v_x_161_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_maxDay(lean_object* v_y_166_, lean_object* v_m_167_){
_start:
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(2u);
v___x_169_ = lean_nat_dec_eq(v_m_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = lean_unsigned_to_nat(7u);
v___x_171_ = lean_nat_dec_le(v_m_167_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_unsigned_to_nat(31u);
v___x_173_ = lean_nat_mod(v_m_167_, v___x_168_);
v___x_174_ = lean_nat_sub(v___x_172_, v___x_173_);
lean_dec(v___x_173_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(30u);
v___x_176_ = lean_nat_mod(v_m_167_, v___x_168_);
v___x_177_ = lean_nat_add(v___x_175_, v___x_176_);
lean_dec(v___x_176_);
return v___x_177_;
}
}
else
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_187_; 
v___x_178_ = lean_unsigned_to_nat(4u);
v___x_179_ = lean_nat_mod(v_y_166_, v___x_178_);
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_nat_dec_eq(v___x_179_, v___x_180_);
lean_dec(v___x_179_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
v___x_188_ = lean_unsigned_to_nat(28u);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_189_ = lean_unsigned_to_nat(100u);
v___x_190_ = lean_nat_mod(v_y_166_, v___x_189_);
v___x_191_ = lean_nat_dec_eq(v___x_190_, v___x_180_);
lean_dec(v___x_190_);
if (v___x_191_ == 0)
{
if (v___x_187_ == 0)
{
goto v___jp_181_;
}
else
{
lean_object* v___x_192_; 
v___x_192_ = lean_unsigned_to_nat(29u);
return v___x_192_;
}
}
else
{
goto v___jp_181_;
}
}
v___jp_181_:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = lean_unsigned_to_nat(400u);
v___x_183_ = lean_nat_mod(v_y_166_, v___x_182_);
v___x_184_ = lean_nat_dec_eq(v___x_183_, v___x_180_);
lean_dec(v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_unsigned_to_nat(28u);
return v___x_185_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = lean_unsigned_to_nat(29u);
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_maxDay___boxed(lean_object* v_y_193_, lean_object* v_m_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lake_Date_maxDay(v_y_193_, v_m_194_);
lean_dec(v_m_194_);
lean_dec(v_y_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_ofValid_x3f(lean_object* v_year_196_, lean_object* v_month_197_, lean_object* v_day_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_nat_dec_le(v___x_199_, v_month_197_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec(v_day_198_);
lean_dec(v_month_197_);
lean_dec(v_year_196_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_202_ = lean_unsigned_to_nat(12u);
v___x_203_ = lean_nat_dec_le(v_month_197_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; 
lean_dec(v_day_198_);
lean_dec(v_month_197_);
lean_dec(v_year_196_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
uint8_t v___x_205_; 
v___x_205_ = lean_nat_dec_le(v___x_199_, v_day_198_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec(v_day_198_);
lean_dec(v_month_197_);
lean_dec(v_year_196_);
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = l_Lake_Date_maxDay(v_year_196_, v_month_197_);
v___x_208_ = lean_nat_dec_le(v_day_198_, v___x_207_);
lean_dec(v___x_207_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
lean_dec(v_day_198_);
lean_dec(v_month_197_);
lean_dec(v_year_196_);
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_210_, 0, v_year_196_);
lean_ctor_set(v___x_210_, 1, v_month_197_);
lean_ctor_set(v___x_210_, 2, v_day_198_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
}
}
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg___closed__0));
return v___x_215_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_216_;
v_res_216_ = l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg();
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg();
return v_res_218_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___redArg();
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0(lean_object* v_s_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___boxed(lean_object* v_s_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0(v_s_222_);
lean_dec_ref(v_s_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(lean_object* v_t_224_, lean_object* v___x_225_, lean_object* v___x_226_, lean_object* v_a_227_, lean_object* v_b_228_){
_start:
{
lean_object* v_it_230_; lean_object* v_startInclusive_231_; lean_object* v_endExclusive_232_; 
if (lean_obj_tag(v_a_227_) == 0)
{
lean_object* v_currPos_236_; lean_object* v_searcher_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_260_; 
v_currPos_236_ = lean_ctor_get(v_a_227_, 0);
v_searcher_237_ = lean_ctor_get(v_a_227_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_a_227_);
if (v_isSharedCheck_260_ == 0)
{
v___x_239_ = v_a_227_;
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_searcher_237_);
lean_inc(v_currPos_236_);
lean_dec(v_a_227_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
uint8_t v_decide_241_; 
v_decide_241_ = lean_nat_dec_eq(v_searcher_237_, v___x_226_);
if (v_decide_241_ == 0)
{
uint32_t v___x_242_; uint32_t v___x_243_; uint8_t v___x_244_; 
v___x_242_ = 45;
v___x_243_ = lean_string_utf8_get_fast(v_t_224_, v_searcher_237_);
v___x_244_ = lean_uint32_dec_eq(v___x_243_, v___x_242_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_string_utf8_next_fast(v_t_224_, v_searcher_237_);
lean_dec(v_searcher_237_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_245_);
v___x_247_ = v___x_239_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_currPos_236_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_249_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
v_a_227_ = v___x_247_;
goto _start;
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v_slice_253_; lean_object* v_nextIt_255_; 
v___x_250_ = lean_string_utf8_next_fast(v_t_224_, v_searcher_237_);
v___x_251_ = lean_nat_sub(v___x_250_, v_searcher_237_);
v___x_252_ = lean_nat_add(v_searcher_237_, v___x_251_);
lean_dec(v___x_251_);
v_slice_253_ = l_String_Slice_subslice_x21(v___x_225_, v_currPos_236_, v_searcher_237_);
lean_inc(v___x_252_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_252_);
lean_ctor_set(v___x_239_, 0, v___x_252_);
v_nextIt_255_ = v___x_239_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v___x_252_);
v_nextIt_255_ = v_reuseFailAlloc_258_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v_startInclusive_256_; lean_object* v_endExclusive_257_; 
v_startInclusive_256_ = lean_ctor_get(v_slice_253_, 0);
lean_inc(v_startInclusive_256_);
v_endExclusive_257_ = lean_ctor_get(v_slice_253_, 1);
lean_inc(v_endExclusive_257_);
lean_dec_ref(v_slice_253_);
v_it_230_ = v_nextIt_255_;
v_startInclusive_231_ = v_startInclusive_256_;
v_endExclusive_232_ = v_endExclusive_257_;
goto v___jp_229_;
}
}
}
else
{
lean_object* v___x_259_; 
lean_del_object(v___x_239_);
lean_dec(v_searcher_237_);
v___x_259_ = lean_box(1);
lean_inc(v___x_226_);
v_it_230_ = v___x_259_;
v_startInclusive_231_ = v_currPos_236_;
v_endExclusive_232_ = v___x_226_;
goto v___jp_229_;
}
}
}
else
{
lean_dec(v___x_226_);
lean_dec_ref(v_t_224_);
return v_b_228_;
}
v___jp_229_:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_inc_ref(v_t_224_);
v___x_233_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_233_, 0, v_t_224_);
lean_ctor_set(v___x_233_, 1, v_startInclusive_231_);
lean_ctor_set(v___x_233_, 2, v_endExclusive_232_);
v___x_234_ = lean_array_push(v_b_228_, v___x_233_);
v_a_227_ = v_it_230_;
v_b_228_ = v___x_234_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg___boxed(lean_object* v_t_261_, lean_object* v___x_262_, lean_object* v___x_263_, lean_object* v_a_264_, lean_object* v_b_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(v_t_261_, v___x_262_, v___x_263_, v_a_264_, v_b_265_);
lean_dec_ref(v___x_262_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_ofString_x3f(lean_object* v_t_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_270_ = lean_unsigned_to_nat(0u);
v___x_271_ = lean_string_utf8_byte_size(v_t_269_);
lean_inc_ref(v_t_269_);
v___x_272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_272_, 0, v_t_269_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
lean_ctor_set(v___x_272_, 2, v___x_271_);
v___x_273_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0);
v___x_274_ = ((lean_object*)(l_Lake_Date_ofString_x3f___closed__0));
v___x_275_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(v_t_269_, v___x_272_, v___x_271_, v___x_273_, v___x_274_);
lean_dec_ref_known(v___x_272_, 3);
v___x_276_ = lean_array_to_list(v___x_275_);
if (lean_obj_tag(v___x_276_) == 1)
{
lean_object* v_tail_277_; 
v_tail_277_ = lean_ctor_get(v___x_276_, 1);
lean_inc(v_tail_277_);
if (lean_obj_tag(v_tail_277_) == 1)
{
lean_object* v_tail_278_; 
v_tail_278_ = lean_ctor_get(v_tail_277_, 1);
lean_inc(v_tail_278_);
if (lean_obj_tag(v_tail_278_) == 1)
{
lean_object* v_tail_279_; 
v_tail_279_ = lean_ctor_get(v_tail_278_, 1);
if (lean_obj_tag(v_tail_279_) == 0)
{
lean_object* v_head_280_; lean_object* v_head_281_; lean_object* v_head_282_; lean_object* v___x_283_; 
v_head_280_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_head_280_);
lean_dec_ref_known(v___x_276_, 2);
v_head_281_ = lean_ctor_get(v_tail_277_, 0);
lean_inc(v_head_281_);
lean_dec_ref_known(v_tail_277_, 2);
v_head_282_ = lean_ctor_get(v_tail_278_, 0);
lean_inc(v_head_282_);
lean_dec_ref_known(v_tail_278_, 2);
v___x_283_ = l_String_Slice_toNat_x3f(v_head_280_);
lean_dec(v_head_280_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_284_; 
lean_dec(v_head_282_);
lean_dec(v_head_281_);
v___x_284_ = lean_box(0);
return v___x_284_;
}
else
{
lean_object* v_val_285_; lean_object* v___x_286_; 
v_val_285_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v___x_283_, 1);
v___x_286_ = l_String_Slice_toNat_x3f(v_head_281_);
lean_dec(v_head_281_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_287_; 
lean_dec(v_val_285_);
lean_dec(v_head_282_);
v___x_287_ = lean_box(0);
return v___x_287_;
}
else
{
lean_object* v_val_288_; lean_object* v___x_289_; 
v_val_288_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_val_288_);
lean_dec_ref_known(v___x_286_, 1);
v___x_289_ = l_String_Slice_toNat_x3f(v_head_282_);
lean_dec(v_head_282_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_290_; 
lean_dec(v_val_288_);
lean_dec(v_val_285_);
v___x_290_ = lean_box(0);
return v___x_290_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_292_; 
v_val_291_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_291_);
lean_dec_ref_known(v___x_289_, 1);
v___x_292_ = l_Lake_Date_ofValid_x3f(v_val_285_, v_val_288_, v_val_291_);
return v___x_292_;
}
}
}
}
else
{
lean_object* v___x_293_; 
lean_dec_ref_known(v_tail_278_, 2);
lean_dec_ref_known(v_tail_277_, 2);
lean_dec_ref_known(v___x_276_, 2);
v___x_293_ = lean_box(0);
return v___x_293_;
}
}
else
{
lean_object* v___x_294_; 
lean_dec(v_tail_278_);
lean_dec_ref_known(v_tail_277_, 2);
lean_dec_ref_known(v___x_276_, 2);
v___x_294_ = lean_box(0);
return v___x_294_;
}
}
else
{
lean_object* v___x_295_; 
lean_dec_ref_known(v___x_276_, 2);
lean_dec(v_tail_277_);
v___x_295_ = lean_box(0);
return v___x_295_;
}
}
else
{
lean_object* v___x_296_; 
lean_dec(v___x_276_);
v___x_296_ = lean_box(0);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1(lean_object* v_t_297_, lean_object* v___x_298_, lean_object* v___x_299_, lean_object* v_inst_300_, lean_object* v_R_301_, lean_object* v_a_302_, lean_object* v_b_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(v_t_297_, v___x_298_, v___x_299_, v_a_302_, v_b_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___boxed(lean_object* v_t_305_, lean_object* v___x_306_, lean_object* v___x_307_, lean_object* v_inst_308_, lean_object* v_R_309_, lean_object* v_a_310_, lean_object* v_b_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1(v_t_305_, v___x_306_, v___x_307_, v_inst_308_, v_R_309_, v_a_310_, v_b_311_);
lean_dec_ref(v___x_306_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_fromJson_x3f(lean_object* v_j_316_){
_start:
{
if (lean_obj_tag(v_j_316_) == 3)
{
lean_object* v_s_317_; lean_object* v___x_318_; 
v_s_317_ = lean_ctor_get(v_j_316_, 0);
lean_inc_ref(v_s_317_);
lean_dec_ref_known(v_j_316_, 1);
v___x_318_ = l_Lake_Date_ofString_x3f(v_s_317_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v_val_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_val_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_val_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_val_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
else
{
lean_object* v___x_327_; 
lean_dec(v___x_318_);
v___x_327_ = ((lean_object*)(l_Lake_Date_fromJson_x3f___closed__1));
return v___x_327_;
}
}
else
{
lean_object* v___x_328_; 
lean_dec(v_j_316_);
v___x_328_ = ((lean_object*)(l_Lake_Date_fromJson_x3f___closed__1));
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_toString(lean_object* v_d_332_){
_start:
{
lean_object* v_year_333_; lean_object* v_month_334_; lean_object* v_day_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_year_333_ = lean_ctor_get(v_d_332_, 0);
lean_inc(v_year_333_);
v_month_334_ = lean_ctor_get(v_d_332_, 1);
lean_inc(v_month_334_);
v_day_335_ = lean_ctor_get(v_d_332_, 2);
lean_inc(v_day_335_);
lean_dec_ref(v_d_332_);
v___x_336_ = lean_unsigned_to_nat(4u);
v___x_337_ = l_Lake_zpad(v_year_333_, v___x_336_);
v___x_338_ = ((lean_object*)(l_Lake_Date_toString___closed__0));
v___x_339_ = lean_string_append(v___x_337_, v___x_338_);
v___x_340_ = lean_unsigned_to_nat(2u);
v___x_341_ = l_Lake_zpad(v_month_334_, v___x_340_);
v___x_342_ = lean_string_append(v___x_339_, v___x_341_);
lean_dec_ref(v___x_341_);
v___x_343_ = lean_string_append(v___x_342_, v___x_338_);
v___x_344_ = l_Lake_zpad(v_day_335_, v___x_340_);
v___x_345_ = lean_string_append(v___x_343_, v___x_344_);
lean_dec_ref(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_toJson(lean_object* v_d_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = l_Lake_Date_toString(v_d_348_);
v___x_350_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
return v___x_350_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Date(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Date_instLT = _init_l_Lake_Date_instLT();
lean_mark_persistent(l_Lake_Date_instLT);
l_Lake_Date_instLE = _init_l_Lake_Date_instLE();
lean_mark_persistent(l_Lake_Date_instLE);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Date(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Json(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Date(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Date(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Date(builtin);
}
#ifdef __cplusplus
}
#endif

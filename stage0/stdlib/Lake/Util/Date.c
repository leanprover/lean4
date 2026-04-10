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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0_value;
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
LEAN_EXPORT uint8_t l_Lake_instDecidableEqDate_decEq(lean_object* v_x_5_, lean_object* v_x_6_){
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
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate_decEq___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_Lake_instDecidableEqDate_decEq(v_x_16_, v_x_17_);
lean_dec_ref(v_x_17_);
lean_dec_ref(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqDate(lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
uint8_t v___x_22_; 
v___x_22_ = l_Lake_instDecidableEqDate_decEq(v_x_20_, v_x_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate___boxed(lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Lake_instDecidableEqDate(v_x_23_, v_x_24_);
lean_dec_ref(v_x_24_);
lean_dec_ref(v_x_23_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdDate_ord(lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
lean_object* v_year_29_; lean_object* v_month_30_; lean_object* v_day_31_; lean_object* v_year_32_; lean_object* v_month_33_; lean_object* v_day_34_; uint8_t v___x_35_; 
v_year_29_ = lean_ctor_get(v_x_27_, 0);
v_month_30_ = lean_ctor_get(v_x_27_, 1);
v_day_31_ = lean_ctor_get(v_x_27_, 2);
v_year_32_ = lean_ctor_get(v_x_28_, 0);
v_month_33_ = lean_ctor_get(v_x_28_, 1);
v_day_34_ = lean_ctor_get(v_x_28_, 2);
v___x_35_ = lean_nat_dec_lt(v_year_29_, v_year_32_);
if (v___x_35_ == 0)
{
uint8_t v___x_36_; 
v___x_36_ = lean_nat_dec_eq(v_year_29_, v_year_32_);
if (v___x_36_ == 0)
{
uint8_t v___x_37_; 
v___x_37_ = 2;
return v___x_37_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = lean_nat_dec_lt(v_month_30_, v_month_33_);
if (v___x_38_ == 0)
{
uint8_t v___x_39_; 
v___x_39_ = lean_nat_dec_eq(v_month_30_, v_month_33_);
if (v___x_39_ == 0)
{
uint8_t v___x_40_; 
v___x_40_ = 2;
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = lean_nat_dec_lt(v_day_31_, v_day_34_);
if (v___x_41_ == 0)
{
uint8_t v___x_42_; 
v___x_42_ = lean_nat_dec_eq(v_day_31_, v_day_34_);
if (v___x_42_ == 0)
{
uint8_t v___x_43_; 
v___x_43_ = 2;
return v___x_43_;
}
else
{
uint8_t v___x_44_; 
v___x_44_ = 1;
return v___x_44_;
}
}
else
{
uint8_t v___x_45_; 
v___x_45_ = 0;
return v___x_45_;
}
}
}
else
{
uint8_t v___x_46_; 
v___x_46_ = 0;
return v___x_46_;
}
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
LEAN_EXPORT lean_object* l_Lake_instOrdDate_ord___boxed(lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Lake_instOrdDate_ord(v_x_48_, v_x_49_);
lean_dec_ref(v_x_49_);
lean_dec_ref(v_x_48_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprDate_repr_spec__0(lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_nat_to_int(v_a_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(8u);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(9u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(7u);
v___x_83_ = lean_nat_to_int(v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__0));
v___x_86_ = lean_string_length(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Lake_instReprDate_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&l_Lake_instReprDate_repr___redArg___closed__17, &l_Lake_instReprDate_repr___redArg___closed__17_once, _init_l_Lake_instReprDate_repr___redArg___closed__17);
v___x_88_ = lean_nat_to_int(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr___redArg(lean_object* v_x_93_){
_start:
{
lean_object* v_year_94_; lean_object* v_month_95_; lean_object* v_day_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_year_94_ = lean_ctor_get(v_x_93_, 0);
lean_inc(v_year_94_);
v_month_95_ = lean_ctor_get(v_x_93_, 1);
lean_inc(v_month_95_);
v_day_96_ = lean_ctor_get(v_x_93_, 2);
lean_inc(v_day_96_);
lean_dec_ref(v_x_93_);
v___x_97_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__5));
v___x_98_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__6));
v___x_99_ = lean_obj_once(&l_Lake_instReprDate_repr___redArg___closed__7, &l_Lake_instReprDate_repr___redArg___closed__7_once, _init_l_Lake_instReprDate_repr___redArg___closed__7);
v___x_100_ = l_Nat_reprFast(v_year_94_);
v___x_101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_99_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = 0;
v___x_104_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_104_, 0, v___x_102_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*1, v___x_103_);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_98_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__9));
v___x_107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = lean_box(1);
v___x_109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__11));
v___x_111_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_97_);
v___x_113_ = lean_obj_once(&l_Lake_instReprDate_repr___redArg___closed__12, &l_Lake_instReprDate_repr___redArg___closed__12_once, _init_l_Lake_instReprDate_repr___redArg___closed__12);
v___x_114_ = l_Nat_reprFast(v_month_95_);
v___x_115_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_113_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_103_);
v___x_118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_112_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
v___x_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v___x_106_);
v___x_120_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_108_);
v___x_121_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__14));
v___x_122_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_97_);
v___x_124_ = lean_obj_once(&l_Lake_instReprDate_repr___redArg___closed__15, &l_Lake_instReprDate_repr___redArg___closed__15_once, _init_l_Lake_instReprDate_repr___redArg___closed__15);
v___x_125_ = l_Nat_reprFast(v_day_96_);
v___x_126_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
v___x_127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_124_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*1, v___x_103_);
v___x_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_123_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_obj_once(&l_Lake_instReprDate_repr___redArg___closed__18, &l_Lake_instReprDate_repr___redArg___closed__18_once, _init_l_Lake_instReprDate_repr___redArg___closed__18);
v___x_131_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__19));
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_129_);
v___x_133_ = ((lean_object*)(l_Lake_instReprDate_repr___redArg___closed__20));
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_130_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set_uint8(v___x_136_, sizeof(void*)*1, v___x_103_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr(lean_object* v_x_137_, lean_object* v_prec_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lake_instReprDate_repr___redArg(v_x_137_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDate_repr___boxed(lean_object* v_x_140_, lean_object* v_prec_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lake_instReprDate_repr(v_x_140_, v_prec_141_);
lean_dec(v_prec_141_);
return v_res_142_;
}
}
static lean_object* _init_l_Lake_Date_instLT(void){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_box(0);
return v___x_145_;
}
}
static lean_object* _init_l_Lake_Date_instLE(void){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = lean_box(0);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0(lean_object* v_x_147_, lean_object* v_y_148_){
_start:
{
uint8_t v___x_149_; 
v___x_149_ = l_Lake_instOrdDate_ord(v_x_147_, v_y_148_);
if (v___x_149_ == 2)
{
lean_inc_ref(v_y_148_);
return v_y_148_;
}
else
{
lean_inc_ref(v_x_147_);
return v_x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0___boxed(lean_object* v_x_150_, lean_object* v_y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lake_Date_instMin___lam__0(v_x_150_, v_y_151_);
lean_dec_ref(v_y_151_);
lean_dec_ref(v_x_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0(lean_object* v_x_155_, lean_object* v_y_156_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = l_Lake_instOrdDate_ord(v_x_155_, v_y_156_);
if (v___x_157_ == 2)
{
lean_inc_ref(v_x_155_);
return v_x_155_;
}
else
{
lean_inc_ref(v_y_156_);
return v_y_156_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0___boxed(lean_object* v_x_158_, lean_object* v_y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lake_Date_instMax___lam__0(v_x_158_, v_y_159_);
lean_dec_ref(v_y_159_);
lean_dec_ref(v_x_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_maxDay(lean_object* v_y_163_, lean_object* v_m_164_){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(2u);
v___x_166_ = lean_nat_dec_eq(v_m_164_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_unsigned_to_nat(7u);
v___x_168_ = lean_nat_dec_le(v_m_164_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_unsigned_to_nat(31u);
v___x_170_ = lean_nat_mod(v_m_164_, v___x_165_);
v___x_171_ = lean_nat_sub(v___x_169_, v___x_170_);
lean_dec(v___x_170_);
return v___x_171_;
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_unsigned_to_nat(30u);
v___x_173_ = lean_nat_mod(v_m_164_, v___x_165_);
v___x_174_ = lean_nat_add(v___x_172_, v___x_173_);
lean_dec(v___x_173_);
return v___x_174_;
}
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_184_; 
v___x_175_ = lean_unsigned_to_nat(4u);
v___x_176_ = lean_nat_mod(v_y_163_, v___x_175_);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_nat_dec_eq(v___x_176_, v___x_177_);
lean_dec(v___x_176_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_unsigned_to_nat(28u);
return v___x_185_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_186_ = lean_unsigned_to_nat(100u);
v___x_187_ = lean_nat_mod(v_y_163_, v___x_186_);
v___x_188_ = lean_nat_dec_eq(v___x_187_, v___x_177_);
lean_dec(v___x_187_);
if (v___x_188_ == 0)
{
if (v___x_184_ == 0)
{
goto v___jp_178_;
}
else
{
lean_object* v___x_189_; 
v___x_189_ = lean_unsigned_to_nat(29u);
return v___x_189_;
}
}
else
{
goto v___jp_178_;
}
}
v___jp_178_:
{
lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(400u);
v___x_180_ = lean_nat_mod(v_y_163_, v___x_179_);
v___x_181_ = lean_nat_dec_eq(v___x_180_, v___x_177_);
lean_dec(v___x_180_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_unsigned_to_nat(28u);
return v___x_182_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_unsigned_to_nat(29u);
return v___x_183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_maxDay___boxed(lean_object* v_y_190_, lean_object* v_m_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lake_Date_maxDay(v_y_190_, v_m_191_);
lean_dec(v_m_191_);
lean_dec(v_y_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_ofValid_x3f(lean_object* v_year_193_, lean_object* v_month_194_, lean_object* v_day_195_){
_start:
{
lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_dec_le(v___x_196_, v_month_194_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; 
lean_dec(v_day_195_);
lean_dec(v_month_194_);
lean_dec(v_year_193_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(12u);
v___x_200_ = lean_nat_dec_le(v_month_194_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_dec(v_day_195_);
lean_dec(v_month_194_);
lean_dec(v_year_193_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
uint8_t v___x_202_; 
v___x_202_ = lean_nat_dec_le(v___x_196_, v_day_195_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; 
lean_dec(v_day_195_);
lean_dec(v_month_194_);
lean_dec(v_year_193_);
v___x_203_ = lean_box(0);
return v___x_203_;
}
else
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = l_Lake_Date_maxDay(v_year_193_, v_month_194_);
v___x_205_ = lean_nat_dec_le(v_day_195_, v___x_204_);
lean_dec(v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_dec(v_day_195_);
lean_dec(v_month_194_);
lean_dec(v_year_193_);
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_207_, 0, v_year_193_);
lean_ctor_set(v___x_207_, 1, v_month_194_);
lean_ctor_set(v___x_207_, 2, v_day_195_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0(lean_object* v_s_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___closed__0));
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0___boxed(lean_object* v_s_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0(v_s_213_);
lean_dec_ref(v_s_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(lean_object* v_t_215_, lean_object* v___x_216_, lean_object* v___x_217_, lean_object* v_a_218_, lean_object* v_b_219_){
_start:
{
lean_object* v_it_221_; lean_object* v_startInclusive_222_; lean_object* v_endExclusive_223_; 
if (lean_obj_tag(v_a_218_) == 0)
{
lean_object* v_currPos_227_; lean_object* v_searcher_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_254_; 
v_currPos_227_ = lean_ctor_get(v_a_218_, 0);
v_searcher_228_ = lean_ctor_get(v_a_218_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v_a_218_);
if (v_isSharedCheck_254_ == 0)
{
v___x_230_ = v_a_218_;
v_isShared_231_ = v_isSharedCheck_254_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_searcher_228_);
lean_inc(v_currPos_227_);
lean_dec(v_a_218_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_254_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v_startInclusive_232_; lean_object* v_endExclusive_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_startInclusive_232_ = lean_ctor_get(v___x_216_, 1);
v_endExclusive_233_ = lean_ctor_get(v___x_216_, 2);
v___x_234_ = lean_nat_sub(v_endExclusive_233_, v_startInclusive_232_);
v___x_235_ = lean_nat_dec_eq(v_searcher_228_, v___x_234_);
lean_dec(v___x_234_);
if (v___x_235_ == 0)
{
uint32_t v___x_236_; uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_236_ = 45;
v___x_237_ = lean_string_utf8_get_fast(v_t_215_, v_searcher_228_);
v___x_238_ = lean_uint32_dec_eq(v___x_237_, v___x_236_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_string_utf8_next_fast(v_t_215_, v_searcher_228_);
lean_dec(v_searcher_228_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_239_);
v___x_241_ = v___x_230_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_currPos_227_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
v_a_218_ = v___x_241_;
goto _start;
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_slice_247_; lean_object* v_nextIt_249_; 
v___x_244_ = lean_string_utf8_next_fast(v_t_215_, v_searcher_228_);
v___x_245_ = lean_nat_sub(v___x_244_, v_searcher_228_);
v___x_246_ = lean_nat_add(v_searcher_228_, v___x_245_);
lean_dec(v___x_245_);
v_slice_247_ = l_String_Slice_subslice_x21(v___x_216_, v_currPos_227_, v_searcher_228_);
lean_inc(v___x_246_);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 1, v___x_246_);
lean_ctor_set(v___x_230_, 0, v___x_246_);
v_nextIt_249_ = v___x_230_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_246_);
v_nextIt_249_ = v_reuseFailAlloc_252_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v_startInclusive_250_; lean_object* v_endExclusive_251_; 
v_startInclusive_250_ = lean_ctor_get(v_slice_247_, 0);
lean_inc(v_startInclusive_250_);
v_endExclusive_251_ = lean_ctor_get(v_slice_247_, 1);
lean_inc(v_endExclusive_251_);
lean_dec_ref(v_slice_247_);
v_it_221_ = v_nextIt_249_;
v_startInclusive_222_ = v_startInclusive_250_;
v_endExclusive_223_ = v_endExclusive_251_;
goto v___jp_220_;
}
}
}
else
{
lean_object* v___x_253_; 
lean_del_object(v___x_230_);
lean_dec(v_searcher_228_);
v___x_253_ = lean_box(1);
lean_inc(v___x_217_);
v_it_221_ = v___x_253_;
v_startInclusive_222_ = v_currPos_227_;
v_endExclusive_223_ = v___x_217_;
goto v___jp_220_;
}
}
}
else
{
lean_dec(v___x_217_);
lean_dec_ref(v_t_215_);
return v_b_219_;
}
v___jp_220_:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_inc_ref(v_t_215_);
v___x_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_224_, 0, v_t_215_);
lean_ctor_set(v___x_224_, 1, v_startInclusive_222_);
lean_ctor_set(v___x_224_, 2, v_endExclusive_223_);
v___x_225_ = lean_array_push(v_b_219_, v___x_224_);
v_a_218_ = v_it_221_;
v_b_219_ = v___x_225_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg___boxed(lean_object* v_t_255_, lean_object* v___x_256_, lean_object* v___x_257_, lean_object* v_a_258_, lean_object* v_b_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(v_t_255_, v___x_256_, v___x_257_, v_a_258_, v_b_259_);
lean_dec_ref(v___x_256_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_ofString_x3f(lean_object* v_t_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___x_265_ = lean_string_utf8_byte_size(v_t_263_);
lean_inc_ref(v_t_263_);
v___x_266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_266_, 0, v_t_263_);
lean_ctor_set(v___x_266_, 1, v___x_264_);
lean_ctor_set(v___x_266_, 2, v___x_265_);
v___x_267_ = l_String_Slice_splitToSubslice___at___00Lake_Date_ofString_x3f_spec__0(v___x_266_);
v___x_268_ = ((lean_object*)(l_Lake_Date_ofString_x3f___closed__0));
v___x_269_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(v_t_263_, v___x_266_, v___x_265_, v___x_267_, v___x_268_);
lean_dec_ref(v___x_266_);
v___x_270_ = lean_array_to_list(v___x_269_);
if (lean_obj_tag(v___x_270_) == 1)
{
lean_object* v_tail_271_; 
v_tail_271_ = lean_ctor_get(v___x_270_, 1);
lean_inc(v_tail_271_);
if (lean_obj_tag(v_tail_271_) == 1)
{
lean_object* v_tail_272_; 
v_tail_272_ = lean_ctor_get(v_tail_271_, 1);
lean_inc(v_tail_272_);
if (lean_obj_tag(v_tail_272_) == 1)
{
lean_object* v_tail_273_; 
v_tail_273_ = lean_ctor_get(v_tail_272_, 1);
if (lean_obj_tag(v_tail_273_) == 0)
{
lean_object* v_head_274_; lean_object* v_head_275_; lean_object* v_head_276_; lean_object* v___x_277_; 
v_head_274_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_head_274_);
lean_dec_ref(v___x_270_);
v_head_275_ = lean_ctor_get(v_tail_271_, 0);
lean_inc(v_head_275_);
lean_dec_ref(v_tail_271_);
v_head_276_ = lean_ctor_get(v_tail_272_, 0);
lean_inc(v_head_276_);
lean_dec_ref(v_tail_272_);
v___x_277_ = l_String_Slice_toNat_x3f(v_head_274_);
lean_dec(v_head_274_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v___x_278_; 
lean_dec(v_head_276_);
lean_dec(v_head_275_);
v___x_278_ = lean_box(0);
return v___x_278_;
}
else
{
lean_object* v_val_279_; lean_object* v___x_280_; 
v_val_279_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_val_279_);
lean_dec_ref(v___x_277_);
v___x_280_ = l_String_Slice_toNat_x3f(v_head_275_);
lean_dec(v_head_275_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; 
lean_dec(v_val_279_);
lean_dec(v_head_276_);
v___x_281_ = lean_box(0);
return v___x_281_;
}
else
{
lean_object* v_val_282_; lean_object* v___x_283_; 
v_val_282_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_282_);
lean_dec_ref(v___x_280_);
v___x_283_ = l_String_Slice_toNat_x3f(v_head_276_);
lean_dec(v_head_276_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_284_; 
lean_dec(v_val_282_);
lean_dec(v_val_279_);
v___x_284_ = lean_box(0);
return v___x_284_;
}
else
{
lean_object* v_val_285_; lean_object* v___x_286_; 
v_val_285_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_val_285_);
lean_dec_ref(v___x_283_);
v___x_286_ = l_Lake_Date_ofValid_x3f(v_val_279_, v_val_282_, v_val_285_);
return v___x_286_;
}
}
}
}
else
{
lean_object* v___x_287_; 
lean_dec_ref(v_tail_272_);
lean_dec_ref(v_tail_271_);
lean_dec_ref(v___x_270_);
v___x_287_ = lean_box(0);
return v___x_287_;
}
}
else
{
lean_object* v___x_288_; 
lean_dec(v_tail_272_);
lean_dec_ref(v_tail_271_);
lean_dec_ref(v___x_270_);
v___x_288_ = lean_box(0);
return v___x_288_;
}
}
else
{
lean_object* v___x_289_; 
lean_dec(v_tail_271_);
lean_dec_ref(v___x_270_);
v___x_289_ = lean_box(0);
return v___x_289_;
}
}
else
{
lean_object* v___x_290_; 
lean_dec(v___x_270_);
v___x_290_ = lean_box(0);
return v___x_290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1(lean_object* v_t_291_, lean_object* v___x_292_, lean_object* v___x_293_, lean_object* v_inst_294_, lean_object* v_R_295_, lean_object* v_a_296_, lean_object* v_b_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___redArg(v_t_291_, v___x_292_, v___x_293_, v_a_296_, v_b_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1___boxed(lean_object* v_t_299_, lean_object* v___x_300_, lean_object* v___x_301_, lean_object* v_inst_302_, lean_object* v_R_303_, lean_object* v_a_304_, lean_object* v_b_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Date_ofString_x3f_spec__1(v_t_299_, v___x_300_, v___x_301_, v_inst_302_, v_R_303_, v_a_304_, v_b_305_);
lean_dec_ref(v___x_300_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_fromJson_x3f(lean_object* v_j_310_){
_start:
{
if (lean_obj_tag(v_j_310_) == 3)
{
lean_object* v_s_311_; lean_object* v___x_312_; 
v_s_311_ = lean_ctor_get(v_j_310_, 0);
lean_inc_ref(v_s_311_);
lean_dec_ref(v_j_310_);
v___x_312_ = l_Lake_Date_ofString_x3f(v_s_311_);
if (lean_obj_tag(v___x_312_) == 1)
{
lean_object* v_val_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
v_val_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_val_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_val_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
else
{
lean_object* v___x_321_; 
lean_dec(v___x_312_);
v___x_321_ = ((lean_object*)(l_Lake_Date_fromJson_x3f___closed__1));
return v___x_321_;
}
}
else
{
lean_object* v___x_322_; 
lean_dec(v_j_310_);
v___x_322_ = ((lean_object*)(l_Lake_Date_fromJson_x3f___closed__1));
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_toString(lean_object* v_d_326_){
_start:
{
lean_object* v_year_327_; lean_object* v_month_328_; lean_object* v_day_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_year_327_ = lean_ctor_get(v_d_326_, 0);
lean_inc(v_year_327_);
v_month_328_ = lean_ctor_get(v_d_326_, 1);
lean_inc(v_month_328_);
v_day_329_ = lean_ctor_get(v_d_326_, 2);
lean_inc(v_day_329_);
lean_dec_ref(v_d_326_);
v___x_330_ = lean_unsigned_to_nat(4u);
v___x_331_ = l_Lake_zpad(v_year_327_, v___x_330_);
v___x_332_ = ((lean_object*)(l_Lake_Date_toString___closed__0));
v___x_333_ = lean_string_append(v___x_331_, v___x_332_);
v___x_334_ = lean_unsigned_to_nat(2u);
v___x_335_ = l_Lake_zpad(v_month_328_, v___x_334_);
v___x_336_ = lean_string_append(v___x_333_, v___x_335_);
lean_dec_ref(v___x_335_);
v___x_337_ = lean_string_append(v___x_336_, v___x_332_);
v___x_338_ = l_Lake_zpad(v_day_329_, v___x_334_);
v___x_339_ = lean_string_append(v___x_337_, v___x_338_);
lean_dec_ref(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_toJson(lean_object* v_d_342_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = l_Lake_Date_toString(v_d_342_);
v___x_344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Json(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Date(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

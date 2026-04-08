// Lean compiler output
// Module: Lake.Toml.Data.DateTime
// Imports: public import Lake.Util.Date import Lake.Util.String import Init.Data.String.Search import Init.Data.Iterators.Consumers.Collect import Init.Data.Iterators.Consumers.Loop import Init.Data.ToString.Macro
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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t l_Lake_instDecidableEqDate_decEq(lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedDate_default;
lean_object* l_Lake_zpad(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_rpad(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* l_Lake_Date_toString(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Date_ofString_x3f(lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_Toml_instInhabitedTime_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_instInhabitedTime_default___closed__0 = (const lean_object*)&l_Lake_Toml_instInhabitedTime_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instInhabitedTime_default = (const lean_object*)&l_Lake_Toml_instInhabitedTime_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instInhabitedTime = (const lean_object*)&l_Lake_Toml_instInhabitedTime_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqTime_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqTime_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT const lean_object* l_Lake_Toml_Time_zero = (const lean_object*)&l_Lake_Toml_instInhabitedTime_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_Time_instOfNat = (const lean_object*)&l_Lake_Toml_instInhabitedTime_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Time_ofValid_x3f(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lake_Toml_Time_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Toml_Time_ofString_x3f___closed__0 = (const lean_object*)&l_Lake_Toml_Time_ofString_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Time_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_Time_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lake_Toml_Time_toString___closed__0 = (const lean_object*)&l_Lake_Toml_Time_toString___closed__0_value;
static const lean_string_object l_Lake_Toml_Time_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_Toml_Time_toString___closed__1 = (const lean_object*)&l_Lake_Toml_Time_toString___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_Time_toString(lean_object*);
static const lean_closure_object l_Lake_Toml_Time_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_Time_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_Time_instToString___closed__0 = (const lean_object*)&l_Lake_Toml_Time_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_Time_instToString = (const lean_object*)&l_Lake_Toml_Time_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_instInhabitedDateTime_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_instInhabitedDateTime_default___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedDateTime_default;
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedDateTime;
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeDateDateTime___lam__0(lean_object*);
static const lean_closure_object l_Lake_Toml_instCoeDateDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_instCoeDateDateTime___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instCoeDateDateTime___closed__0 = (const lean_object*)&l_Lake_Toml_instCoeDateDateTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instCoeDateDateTime = (const lean_object*)&l_Lake_Toml_instCoeDateDateTime___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeTimeDateTime___lam__0(lean_object*);
static const lean_closure_object l_Lake_Toml_instCoeTimeDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_instCoeTimeDateTime___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_instCoeTimeDateTime___closed__0 = (const lean_object*)&l_Lake_Toml_instCoeTimeDateTime___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_instCoeTimeDateTime = (const lean_object*)&l_Lake_Toml_instCoeTimeDateTime___closed__0_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_DateTime_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "T"};
static const lean_object* l_Lake_Toml_DateTime_toString___closed__0 = (const lean_object*)&l_Lake_Toml_DateTime_toString___closed__0_value;
static const lean_string_object l_Lake_Toml_DateTime_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lake_Toml_DateTime_toString___closed__1 = (const lean_object*)&l_Lake_Toml_DateTime_toString___closed__1_value;
static const lean_string_object l_Lake_Toml_DateTime_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_Toml_DateTime_toString___closed__2 = (const lean_object*)&l_Lake_Toml_DateTime_toString___closed__2_value;
static const lean_string_object l_Lake_Toml_DateTime_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "Z"};
static const lean_object* l_Lake_Toml_DateTime_toString___closed__3 = (const lean_object*)&l_Lake_Toml_DateTime_toString___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_toString(lean_object*);
static const lean_closure_object l_Lake_Toml_DateTime_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_DateTime_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_DateTime_instToString___closed__0 = (const lean_object*)&l_Lake_Toml_DateTime_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Toml_DateTime_instToString = (const lean_object*)&l_Lake_Toml_DateTime_instToString___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqTime_decEq(lean_object* v_x_5_, lean_object* v_x_6_){
_start:
{
lean_object* v_hour_7_; lean_object* v_minute_8_; lean_object* v_second_9_; lean_object* v_fracExponent_10_; lean_object* v_fracMantissa_11_; lean_object* v_hour_12_; lean_object* v_minute_13_; lean_object* v_second_14_; lean_object* v_fracExponent_15_; lean_object* v_fracMantissa_16_; uint8_t v___x_17_; 
v_hour_7_ = lean_ctor_get(v_x_5_, 0);
v_minute_8_ = lean_ctor_get(v_x_5_, 1);
v_second_9_ = lean_ctor_get(v_x_5_, 2);
v_fracExponent_10_ = lean_ctor_get(v_x_5_, 3);
v_fracMantissa_11_ = lean_ctor_get(v_x_5_, 4);
v_hour_12_ = lean_ctor_get(v_x_6_, 0);
v_minute_13_ = lean_ctor_get(v_x_6_, 1);
v_second_14_ = lean_ctor_get(v_x_6_, 2);
v_fracExponent_15_ = lean_ctor_get(v_x_6_, 3);
v_fracMantissa_16_ = lean_ctor_get(v_x_6_, 4);
v___x_17_ = lean_nat_dec_eq(v_hour_7_, v_hour_12_);
if (v___x_17_ == 0)
{
return v___x_17_;
}
else
{
uint8_t v___x_18_; 
v___x_18_ = lean_nat_dec_eq(v_minute_8_, v_minute_13_);
if (v___x_18_ == 0)
{
return v___x_18_;
}
else
{
uint8_t v___x_19_; 
v___x_19_ = lean_nat_dec_eq(v_second_9_, v_second_14_);
if (v___x_19_ == 0)
{
return v___x_19_;
}
else
{
uint8_t v___x_20_; 
v___x_20_ = lean_nat_dec_eq(v_fracExponent_10_, v_fracExponent_15_);
if (v___x_20_ == 0)
{
return v___x_20_;
}
else
{
uint8_t v___x_21_; 
v___x_21_ = lean_nat_dec_eq(v_fracMantissa_11_, v_fracMantissa_16_);
return v___x_21_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqTime_decEq___boxed(lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lake_Toml_instDecidableEqTime_decEq(v_x_22_, v_x_23_);
lean_dec_ref(v_x_23_);
lean_dec_ref(v_x_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqTime(lean_object* v_x_26_, lean_object* v_x_27_){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = l_Lake_Toml_instDecidableEqTime_decEq(v_x_26_, v_x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqTime___boxed(lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Lake_Toml_instDecidableEqTime(v_x_29_, v_x_30_);
lean_dec_ref(v_x_30_);
lean_dec_ref(v_x_29_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_ofValid_x3f(lean_object* v_hour_35_, lean_object* v_minute_36_, lean_object* v_second_37_){
_start:
{
lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_38_ = lean_unsigned_to_nat(23u);
v___x_39_ = lean_nat_dec_le(v_hour_35_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; 
lean_dec(v_second_37_);
lean_dec(v_minute_36_);
lean_dec(v_hour_35_);
v___x_40_ = lean_box(0);
return v___x_40_;
}
else
{
lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(59u);
v___x_42_ = lean_nat_dec_le(v_minute_36_, v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; 
lean_dec(v_second_37_);
lean_dec(v_minute_36_);
lean_dec(v_hour_35_);
v___x_43_ = lean_box(0);
return v___x_43_;
}
else
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(60u);
v___x_45_ = lean_nat_dec_le(v_second_37_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
lean_dec(v_second_37_);
lean_dec(v_minute_36_);
lean_dec(v_hour_35_);
v___x_46_ = lean_box(0);
return v___x_46_;
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_unsigned_to_nat(0u);
v___x_48_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_48_, 0, v_hour_35_);
lean_ctor_set(v___x_48_, 1, v_minute_36_);
lean_ctor_set(v___x_48_, 2, v_second_37_);
lean_ctor_set(v___x_48_, 3, v___x_47_);
lean_ctor_set(v___x_48_, 4, v___x_47_);
v___x_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(lean_object* v_s_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___boxed(lean_object* v_s_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(v_s_54_);
lean_dec_ref(v_s_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(lean_object* v_s_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0));
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___boxed(lean_object* v_s_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(v_s_58_);
lean_dec_ref(v_s_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(lean_object* v_head_60_, lean_object* v_a_61_, lean_object* v_b_62_){
_start:
{
if (lean_obj_tag(v_a_61_) == 0)
{
lean_object* v_currPos_63_; lean_object* v_searcher_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_102_; 
v_currPos_63_ = lean_ctor_get(v_a_61_, 0);
v_searcher_64_ = lean_ctor_get(v_a_61_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_a_61_);
if (v_isSharedCheck_102_ == 0)
{
v___x_66_ = v_a_61_;
v_isShared_67_ = v_isSharedCheck_102_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_searcher_64_);
lean_inc(v_currPos_63_);
lean_dec(v_a_61_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_102_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v_str_68_; lean_object* v_startInclusive_69_; lean_object* v_endExclusive_70_; lean_object* v_it_72_; lean_object* v_startInclusive_73_; lean_object* v_endExclusive_74_; lean_object* v___x_80_; uint8_t v___x_81_; 
v_str_68_ = lean_ctor_get(v_head_60_, 0);
v_startInclusive_69_ = lean_ctor_get(v_head_60_, 1);
v_endExclusive_70_ = lean_ctor_get(v_head_60_, 2);
v___x_80_ = lean_nat_sub(v_endExclusive_70_, v_startInclusive_69_);
v___x_81_ = lean_nat_dec_eq(v_searcher_64_, v___x_80_);
if (v___x_81_ == 0)
{
uint32_t v___x_82_; lean_object* v___x_83_; uint32_t v___x_84_; uint8_t v___x_85_; 
lean_dec(v___x_80_);
v___x_82_ = 46;
v___x_83_ = lean_nat_add(v_startInclusive_69_, v_searcher_64_);
v___x_84_ = lean_string_utf8_get_fast(v_str_68_, v___x_83_);
v___x_85_ = lean_uint32_dec_eq(v___x_84_, v___x_82_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
lean_dec(v_searcher_64_);
v___x_86_ = lean_string_utf8_next_fast(v_str_68_, v___x_83_);
lean_dec(v___x_83_);
v___x_87_ = lean_nat_sub(v___x_86_, v_startInclusive_69_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_87_);
v___x_89_ = v___x_66_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_currPos_63_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_87_);
v___x_89_ = v_reuseFailAlloc_91_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
v_a_61_ = v___x_89_;
goto _start;
}
}
else
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v_slice_95_; lean_object* v_nextIt_97_; 
v___x_92_ = lean_string_utf8_next_fast(v_str_68_, v___x_83_);
v___x_93_ = lean_nat_sub(v___x_92_, v___x_83_);
lean_dec(v___x_83_);
v___x_94_ = lean_nat_add(v_searcher_64_, v___x_93_);
lean_dec(v___x_93_);
v_slice_95_ = l_String_Slice_subslice_x21(v_head_60_, v_currPos_63_, v_searcher_64_);
lean_inc(v___x_94_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 1, v___x_94_);
lean_ctor_set(v___x_66_, 0, v___x_94_);
v_nextIt_97_ = v___x_66_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_94_);
v_nextIt_97_ = v_reuseFailAlloc_100_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v_startInclusive_98_; lean_object* v_endExclusive_99_; 
v_startInclusive_98_ = lean_ctor_get(v_slice_95_, 0);
lean_inc(v_startInclusive_98_);
v_endExclusive_99_ = lean_ctor_get(v_slice_95_, 1);
lean_inc(v_endExclusive_99_);
lean_dec_ref(v_slice_95_);
v_it_72_ = v_nextIt_97_;
v_startInclusive_73_ = v_startInclusive_98_;
v_endExclusive_74_ = v_endExclusive_99_;
goto v___jp_71_;
}
}
}
else
{
lean_object* v___x_101_; 
lean_del_object(v___x_66_);
lean_dec(v_searcher_64_);
v___x_101_ = lean_box(1);
v_it_72_ = v___x_101_;
v_startInclusive_73_ = v_currPos_63_;
v_endExclusive_74_ = v___x_80_;
goto v___jp_71_;
}
v___jp_71_:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_nat_add(v_startInclusive_69_, v_startInclusive_73_);
lean_dec(v_startInclusive_73_);
v___x_76_ = lean_nat_add(v_startInclusive_69_, v_endExclusive_74_);
lean_dec(v_endExclusive_74_);
lean_inc_ref(v_str_68_);
v___x_77_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_77_, 0, v_str_68_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
lean_ctor_set(v___x_77_, 2, v___x_76_);
v___x_78_ = lean_array_push(v_b_62_, v___x_77_);
v_a_61_ = v_it_72_;
v_b_62_ = v___x_78_;
goto _start;
}
}
}
else
{
return v_b_62_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg___boxed(lean_object* v_head_103_, lean_object* v_a_104_, lean_object* v_b_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_103_, v_a_104_, v_b_105_);
lean_dec_ref(v_head_103_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(lean_object* v_t_107_, lean_object* v___x_108_, lean_object* v___x_109_, lean_object* v_a_110_, lean_object* v_b_111_){
_start:
{
lean_object* v_it_113_; lean_object* v_startInclusive_114_; lean_object* v_endExclusive_115_; 
if (lean_obj_tag(v_a_110_) == 0)
{
lean_object* v_currPos_119_; lean_object* v_searcher_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_146_; 
v_currPos_119_ = lean_ctor_get(v_a_110_, 0);
v_searcher_120_ = lean_ctor_get(v_a_110_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_a_110_);
if (v_isSharedCheck_146_ == 0)
{
v___x_122_ = v_a_110_;
v_isShared_123_ = v_isSharedCheck_146_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_searcher_120_);
lean_inc(v_currPos_119_);
lean_dec(v_a_110_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_146_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_startInclusive_124_; lean_object* v_endExclusive_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_startInclusive_124_ = lean_ctor_get(v___x_108_, 1);
v_endExclusive_125_ = lean_ctor_get(v___x_108_, 2);
v___x_126_ = lean_nat_sub(v_endExclusive_125_, v_startInclusive_124_);
v___x_127_ = lean_nat_dec_eq(v_searcher_120_, v___x_126_);
lean_dec(v___x_126_);
if (v___x_127_ == 0)
{
uint32_t v___x_128_; uint32_t v___x_129_; uint8_t v___x_130_; 
v___x_128_ = 58;
v___x_129_ = lean_string_utf8_get_fast(v_t_107_, v_searcher_120_);
v___x_130_ = lean_uint32_dec_eq(v___x_129_, v___x_128_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_string_utf8_next_fast(v_t_107_, v_searcher_120_);
lean_dec(v_searcher_120_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_131_);
v___x_133_ = v___x_122_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_currPos_119_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_135_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
v_a_110_ = v___x_133_;
goto _start;
}
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v_slice_139_; lean_object* v_nextIt_141_; 
v___x_136_ = lean_string_utf8_next_fast(v_t_107_, v_searcher_120_);
v___x_137_ = lean_nat_sub(v___x_136_, v_searcher_120_);
v___x_138_ = lean_nat_add(v_searcher_120_, v___x_137_);
lean_dec(v___x_137_);
v_slice_139_ = l_String_Slice_subslice_x21(v___x_108_, v_currPos_119_, v_searcher_120_);
lean_inc(v___x_138_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_138_);
lean_ctor_set(v___x_122_, 0, v___x_138_);
v_nextIt_141_ = v___x_122_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_138_);
v_nextIt_141_ = v_reuseFailAlloc_144_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v_startInclusive_142_; lean_object* v_endExclusive_143_; 
v_startInclusive_142_ = lean_ctor_get(v_slice_139_, 0);
lean_inc(v_startInclusive_142_);
v_endExclusive_143_ = lean_ctor_get(v_slice_139_, 1);
lean_inc(v_endExclusive_143_);
lean_dec_ref(v_slice_139_);
v_it_113_ = v_nextIt_141_;
v_startInclusive_114_ = v_startInclusive_142_;
v_endExclusive_115_ = v_endExclusive_143_;
goto v___jp_112_;
}
}
}
else
{
lean_object* v___x_145_; 
lean_del_object(v___x_122_);
lean_dec(v_searcher_120_);
v___x_145_ = lean_box(1);
lean_inc(v___x_109_);
v_it_113_ = v___x_145_;
v_startInclusive_114_ = v_currPos_119_;
v_endExclusive_115_ = v___x_109_;
goto v___jp_112_;
}
}
}
else
{
lean_dec(v___x_109_);
lean_dec_ref(v_t_107_);
return v_b_111_;
}
v___jp_112_:
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_inc_ref(v_t_107_);
v___x_116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_116_, 0, v_t_107_);
lean_ctor_set(v___x_116_, 1, v_startInclusive_114_);
lean_ctor_set(v___x_116_, 2, v_endExclusive_115_);
v___x_117_ = lean_array_push(v_b_111_, v___x_116_);
v_a_110_ = v_it_113_;
v_b_111_ = v___x_117_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg___boxed(lean_object* v_t_147_, lean_object* v___x_148_, lean_object* v___x_149_, lean_object* v_a_150_, lean_object* v_b_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_147_, v___x_148_, v___x_149_, v_a_150_, v_b_151_);
lean_dec_ref(v___x_148_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(lean_object* v_head_153_, lean_object* v_a_154_, lean_object* v_b_155_){
_start:
{
lean_object* v_str_156_; lean_object* v_startInclusive_157_; lean_object* v_endExclusive_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v_str_156_ = lean_ctor_get(v_head_153_, 0);
v_startInclusive_157_ = lean_ctor_get(v_head_153_, 1);
v_endExclusive_158_ = lean_ctor_get(v_head_153_, 2);
v___x_159_ = lean_nat_sub(v_endExclusive_158_, v_startInclusive_157_);
v___x_160_ = lean_nat_dec_eq(v_a_154_, v___x_159_);
lean_dec(v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_161_ = lean_nat_add(v_startInclusive_157_, v_a_154_);
lean_dec(v_a_154_);
v___x_162_ = lean_string_utf8_next_fast(v_str_156_, v___x_161_);
lean_dec(v___x_161_);
v___x_163_ = lean_nat_sub(v___x_162_, v_startInclusive_157_);
v___x_164_ = lean_unsigned_to_nat(1u);
v___x_165_ = lean_nat_add(v_b_155_, v___x_164_);
lean_dec(v_b_155_);
v_a_154_ = v___x_163_;
v_b_155_ = v___x_165_;
goto _start;
}
else
{
lean_dec(v_a_154_);
return v_b_155_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg___boxed(lean_object* v_head_167_, lean_object* v_a_168_, lean_object* v_b_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_167_, v_a_168_, v_b_169_);
lean_dec_ref(v_head_167_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_ofString_x3f(lean_object* v_t_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_string_utf8_byte_size(v_t_173_);
lean_inc_ref(v_t_173_);
v___x_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_176_, 0, v_t_173_);
lean_ctor_set(v___x_176_, 1, v___x_174_);
lean_ctor_set(v___x_176_, 2, v___x_175_);
v___x_177_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(v___x_176_);
v___x_178_ = ((lean_object*)(l_Lake_Toml_Time_ofString_x3f___closed__0));
v___x_179_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_173_, v___x_176_, v___x_175_, v___x_177_, v___x_178_);
lean_dec_ref(v___x_176_);
v___x_180_ = lean_array_to_list(v___x_179_);
if (lean_obj_tag(v___x_180_) == 1)
{
lean_object* v_tail_181_; 
v_tail_181_ = lean_ctor_get(v___x_180_, 1);
lean_inc(v_tail_181_);
if (lean_obj_tag(v_tail_181_) == 1)
{
lean_object* v_tail_182_; 
v_tail_182_ = lean_ctor_get(v_tail_181_, 1);
if (lean_obj_tag(v_tail_182_) == 0)
{
lean_object* v_head_183_; lean_object* v_head_184_; lean_object* v___x_185_; 
v_head_183_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_head_183_);
lean_dec_ref(v___x_180_);
v_head_184_ = lean_ctor_get(v_tail_181_, 0);
lean_inc(v_head_184_);
lean_dec_ref(v_tail_181_);
v___x_185_ = l_String_Slice_toNat_x3f(v_head_183_);
lean_dec(v_head_183_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v___x_186_; 
lean_dec(v_head_184_);
v___x_186_ = lean_box(0);
return v___x_186_;
}
else
{
lean_object* v_val_187_; lean_object* v___x_188_; 
v_val_187_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_val_187_);
lean_dec_ref(v___x_185_);
v___x_188_ = l_String_Slice_toNat_x3f(v_head_184_);
lean_dec(v_head_184_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v___x_189_; 
lean_dec(v_val_187_);
v___x_189_ = lean_box(0);
return v___x_189_;
}
else
{
lean_object* v_val_190_; lean_object* v___x_191_; 
v_val_190_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_val_190_);
lean_dec_ref(v___x_188_);
v___x_191_ = l_Lake_Toml_Time_ofValid_x3f(v_val_187_, v_val_190_, v___x_174_);
return v___x_191_;
}
}
}
else
{
lean_object* v_tail_192_; 
lean_inc_ref(v_tail_182_);
v_tail_192_ = lean_ctor_get(v_tail_182_, 1);
if (lean_obj_tag(v_tail_192_) == 0)
{
lean_object* v_head_193_; lean_object* v_head_194_; lean_object* v_head_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v_head_193_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_head_193_);
lean_dec_ref(v___x_180_);
v_head_194_ = lean_ctor_get(v_tail_181_, 0);
lean_inc(v_head_194_);
lean_dec_ref(v_tail_181_);
v_head_195_ = lean_ctor_get(v_tail_182_, 0);
lean_inc(v_head_195_);
lean_dec_ref(v_tail_182_);
v___x_196_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(v_head_195_);
v___x_197_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_195_, v___x_196_, v___x_178_);
lean_dec(v_head_195_);
v___x_198_ = lean_array_to_list(v___x_197_);
if (lean_obj_tag(v___x_198_) == 1)
{
lean_object* v_tail_199_; 
v_tail_199_ = lean_ctor_get(v___x_198_, 1);
lean_inc(v_tail_199_);
if (lean_obj_tag(v_tail_199_) == 0)
{
lean_object* v_head_200_; lean_object* v___x_201_; 
v_head_200_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_head_200_);
lean_dec_ref(v___x_198_);
v___x_201_ = l_String_Slice_toNat_x3f(v_head_193_);
lean_dec(v_head_193_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v___x_202_; 
lean_dec(v_head_200_);
lean_dec(v_head_194_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
lean_object* v_val_203_; lean_object* v___x_204_; 
v_val_203_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_val_203_);
lean_dec_ref(v___x_201_);
v___x_204_ = l_String_Slice_toNat_x3f(v_head_194_);
lean_dec(v_head_194_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v___x_205_; 
lean_dec(v_val_203_);
lean_dec(v_head_200_);
v___x_205_ = lean_box(0);
return v___x_205_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_207_; 
v_val_206_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_val_206_);
lean_dec_ref(v___x_204_);
v___x_207_ = l_String_Slice_toNat_x3f(v_head_200_);
lean_dec(v_head_200_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v___x_208_; 
lean_dec(v_val_206_);
lean_dec(v_val_203_);
v___x_208_ = lean_box(0);
return v___x_208_;
}
else
{
lean_object* v_val_209_; lean_object* v___x_210_; 
v_val_209_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_val_209_);
lean_dec_ref(v___x_207_);
v___x_210_ = l_Lake_Toml_Time_ofValid_x3f(v_val_203_, v_val_206_, v_val_209_);
return v___x_210_;
}
}
}
}
else
{
lean_object* v_tail_211_; 
v_tail_211_ = lean_ctor_get(v_tail_199_, 1);
if (lean_obj_tag(v_tail_211_) == 0)
{
lean_object* v_head_212_; lean_object* v_head_213_; lean_object* v___x_214_; 
v_head_212_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_head_212_);
lean_dec_ref(v___x_198_);
v_head_213_ = lean_ctor_get(v_tail_199_, 0);
lean_inc(v_head_213_);
lean_dec_ref(v_tail_199_);
v___x_214_ = l_String_Slice_toNat_x3f(v_head_193_);
lean_dec(v_head_193_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v___x_215_; 
lean_dec(v_head_213_);
lean_dec(v_head_212_);
lean_dec(v_head_194_);
v___x_215_ = lean_box(0);
return v___x_215_;
}
else
{
lean_object* v_val_216_; lean_object* v___x_217_; 
v_val_216_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_val_216_);
lean_dec_ref(v___x_214_);
v___x_217_ = l_String_Slice_toNat_x3f(v_head_194_);
lean_dec(v_head_194_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v___x_218_; 
lean_dec(v_val_216_);
lean_dec(v_head_213_);
lean_dec(v_head_212_);
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v_val_219_; lean_object* v___x_220_; 
v_val_219_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_val_219_);
lean_dec_ref(v___x_217_);
v___x_220_ = l_String_Slice_toNat_x3f(v_head_212_);
lean_dec(v_head_212_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v___x_221_; 
lean_dec(v_val_219_);
lean_dec(v_val_216_);
lean_dec(v_head_213_);
v___x_221_ = lean_box(0);
return v___x_221_;
}
else
{
lean_object* v_val_222_; lean_object* v___x_223_; 
v_val_222_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_val_222_);
lean_dec_ref(v___x_220_);
v___x_223_ = l_Lake_Toml_Time_ofValid_x3f(v_val_216_, v_val_219_, v_val_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_dec(v_head_213_);
return v___x_223_;
}
else
{
lean_object* v_val_224_; lean_object* v___x_225_; 
v_val_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_224_);
lean_dec_ref(v___x_223_);
v___x_225_ = l_String_Slice_toNat_x3f(v_head_213_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v___x_226_; 
lean_dec(v_val_224_);
lean_dec(v_head_213_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
lean_object* v_val_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_250_; 
v_val_227_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_250_ == 0)
{
v___x_229_ = v___x_225_;
v_isShared_230_ = v_isSharedCheck_250_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_val_227_);
lean_dec(v___x_225_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_250_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v_hour_231_; lean_object* v_minute_232_; lean_object* v_second_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_247_; 
v_hour_231_ = lean_ctor_get(v_val_224_, 0);
v_minute_232_ = lean_ctor_get(v_val_224_, 1);
v_second_233_ = lean_ctor_get(v_val_224_, 2);
v_isSharedCheck_247_ = !lean_is_exclusive(v_val_224_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; lean_object* v_unused_249_; 
v_unused_248_ = lean_ctor_get(v_val_224_, 4);
lean_dec(v_unused_248_);
v_unused_249_ = lean_ctor_get(v_val_224_, 3);
lean_dec(v_unused_249_);
v___x_235_ = v_val_224_;
v_isShared_236_ = v_isSharedCheck_247_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_second_233_);
lean_inc(v_minute_232_);
lean_inc(v_hour_231_);
lean_dec(v_val_224_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_247_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_237_ = l_String_Slice_positions(v_head_213_);
v___x_238_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_213_, v___x_237_, v___x_174_);
lean_dec(v_head_213_);
v___x_239_ = lean_unsigned_to_nat(1u);
v___x_240_ = lean_nat_sub(v___x_238_, v___x_239_);
lean_dec(v___x_238_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 4, v_val_227_);
lean_ctor_set(v___x_235_, 3, v___x_240_);
v___x_242_ = v___x_235_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_hour_231_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_minute_232_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_second_233_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v_val_227_);
v___x_242_ = v_reuseFailAlloc_246_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_244_; 
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 0, v___x_242_);
v___x_244_ = v___x_229_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_251_; 
lean_dec_ref(v_tail_199_);
lean_dec_ref(v___x_198_);
lean_dec(v_head_194_);
lean_dec(v_head_193_);
v___x_251_ = lean_box(0);
return v___x_251_;
}
}
}
else
{
lean_object* v___x_252_; 
lean_dec(v___x_198_);
lean_dec(v_head_194_);
lean_dec(v_head_193_);
v___x_252_ = lean_box(0);
return v___x_252_;
}
}
else
{
lean_object* v___x_253_; 
lean_dec_ref(v_tail_182_);
lean_dec_ref(v_tail_181_);
lean_dec_ref(v___x_180_);
v___x_253_ = lean_box(0);
return v___x_253_;
}
}
}
else
{
lean_object* v___x_254_; 
lean_dec_ref(v___x_180_);
lean_dec(v_tail_181_);
v___x_254_ = lean_box(0);
return v___x_254_;
}
}
else
{
lean_object* v___x_255_; 
lean_dec(v___x_180_);
v___x_255_ = lean_box(0);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(lean_object* v_t_256_, lean_object* v___x_257_, lean_object* v___x_258_, lean_object* v_inst_259_, lean_object* v_R_260_, lean_object* v_a_261_, lean_object* v_b_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_256_, v___x_257_, v___x_258_, v_a_261_, v_b_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___boxed(lean_object* v_t_264_, lean_object* v___x_265_, lean_object* v___x_266_, lean_object* v_inst_267_, lean_object* v_R_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(v_t_264_, v___x_265_, v___x_266_, v_inst_267_, v_R_268_, v_a_269_, v_b_270_);
lean_dec_ref(v___x_265_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(lean_object* v_head_272_, lean_object* v_inst_273_, lean_object* v_R_274_, lean_object* v_a_275_, lean_object* v_b_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_272_, v_a_275_, v_b_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___boxed(lean_object* v_head_278_, lean_object* v_inst_279_, lean_object* v_R_280_, lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(v_head_278_, v_inst_279_, v_R_280_, v_a_281_, v_b_282_);
lean_dec_ref(v_head_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(lean_object* v_head_284_, lean_object* v_inst_285_, lean_object* v_R_286_, lean_object* v_a_287_, lean_object* v_b_288_, lean_object* v_c_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_284_, v_a_287_, v_b_288_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___boxed(lean_object* v_head_291_, lean_object* v_inst_292_, lean_object* v_R_293_, lean_object* v_a_294_, lean_object* v_b_295_, lean_object* v_c_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(v_head_291_, v_inst_292_, v_R_293_, v_a_294_, v_b_295_, v_c_296_);
lean_dec_ref(v_head_291_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_toString(lean_object* v_t_300_){
_start:
{
lean_object* v_hour_301_; lean_object* v_minute_302_; lean_object* v_second_303_; lean_object* v_fracExponent_304_; lean_object* v_fracMantissa_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v_s_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_hour_301_ = lean_ctor_get(v_t_300_, 0);
lean_inc(v_hour_301_);
v_minute_302_ = lean_ctor_get(v_t_300_, 1);
lean_inc(v_minute_302_);
v_second_303_ = lean_ctor_get(v_t_300_, 2);
lean_inc(v_second_303_);
v_fracExponent_304_ = lean_ctor_get(v_t_300_, 3);
lean_inc(v_fracExponent_304_);
v_fracMantissa_305_ = lean_ctor_get(v_t_300_, 4);
lean_inc(v_fracMantissa_305_);
lean_dec_ref(v_t_300_);
v___x_306_ = lean_unsigned_to_nat(2u);
v___x_307_ = l_Lake_zpad(v_hour_301_, v___x_306_);
v___x_308_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_309_ = lean_string_append(v___x_307_, v___x_308_);
v___x_310_ = l_Lake_zpad(v_minute_302_, v___x_306_);
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
lean_dec_ref(v___x_310_);
v___x_312_ = lean_string_append(v___x_311_, v___x_308_);
v___x_313_ = l_Lake_zpad(v_second_303_, v___x_306_);
v_s_314_ = lean_string_append(v___x_312_, v___x_313_);
lean_dec_ref(v___x_313_);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_nat_dec_eq(v_fracMantissa_305_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint32_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_317_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__1));
v___x_318_ = lean_string_append(v_s_314_, v___x_317_);
v___x_319_ = l_Lake_zpad(v_fracMantissa_305_, v_fracExponent_304_);
lean_dec(v_fracExponent_304_);
v___x_320_ = 48;
v___x_321_ = lean_unsigned_to_nat(3u);
v___x_322_ = l_Lake_rpad(v___x_319_, v___x_320_, v___x_321_);
v___x_323_ = lean_string_append(v___x_318_, v___x_322_);
lean_dec_ref(v___x_322_);
return v___x_323_;
}
else
{
lean_dec(v_fracMantissa_305_);
lean_dec(v_fracExponent_304_);
return v_s_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx(lean_object* v_x_326_){
_start:
{
switch(lean_obj_tag(v_x_326_))
{
case 0:
{
lean_object* v___x_327_; 
v___x_327_ = lean_unsigned_to_nat(0u);
return v___x_327_;
}
case 1:
{
lean_object* v___x_328_; 
v___x_328_ = lean_unsigned_to_nat(1u);
return v___x_328_;
}
case 2:
{
lean_object* v___x_329_; 
v___x_329_ = lean_unsigned_to_nat(2u);
return v___x_329_;
}
default: 
{
lean_object* v___x_330_; 
v___x_330_ = lean_unsigned_to_nat(3u);
return v___x_330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx___boxed(lean_object* v_x_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lake_Toml_DateTime_ctorIdx(v_x_331_);
lean_dec_ref(v_x_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___redArg(lean_object* v_t_333_, lean_object* v_k_334_){
_start:
{
switch(lean_obj_tag(v_t_333_))
{
case 0:
{
lean_object* v_date_335_; lean_object* v_time_336_; lean_object* v_offset_x3f_337_; lean_object* v___x_338_; 
v_date_335_ = lean_ctor_get(v_t_333_, 0);
lean_inc_ref(v_date_335_);
v_time_336_ = lean_ctor_get(v_t_333_, 1);
lean_inc_ref(v_time_336_);
v_offset_x3f_337_ = lean_ctor_get(v_t_333_, 2);
lean_inc(v_offset_x3f_337_);
lean_dec_ref(v_t_333_);
v___x_338_ = lean_apply_3(v_k_334_, v_date_335_, v_time_336_, v_offset_x3f_337_);
return v___x_338_;
}
case 1:
{
lean_object* v_date_339_; lean_object* v_time_340_; lean_object* v___x_341_; 
v_date_339_ = lean_ctor_get(v_t_333_, 0);
lean_inc_ref(v_date_339_);
v_time_340_ = lean_ctor_get(v_t_333_, 1);
lean_inc_ref(v_time_340_);
lean_dec_ref(v_t_333_);
v___x_341_ = lean_apply_2(v_k_334_, v_date_339_, v_time_340_);
return v___x_341_;
}
default: 
{
lean_object* v_date_342_; lean_object* v___x_343_; 
v_date_342_ = lean_ctor_get(v_t_333_, 0);
lean_inc_ref(v_date_342_);
lean_dec_ref(v_t_333_);
v___x_343_ = lean_apply_1(v_k_334_, v_date_342_);
return v___x_343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim(lean_object* v_motive_344_, lean_object* v_ctorIdx_345_, lean_object* v_t_346_, lean_object* v_h_347_, lean_object* v_k_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_346_, v_k_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___boxed(lean_object* v_motive_350_, lean_object* v_ctorIdx_351_, lean_object* v_t_352_, lean_object* v_h_353_, lean_object* v_k_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lake_Toml_DateTime_ctorElim(v_motive_350_, v_ctorIdx_351_, v_t_352_, v_h_353_, v_k_354_);
lean_dec(v_ctorIdx_351_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim___redArg(lean_object* v_t_356_, lean_object* v_offsetDateTime_357_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_356_, v_offsetDateTime_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim(lean_object* v_motive_359_, lean_object* v_t_360_, lean_object* v_h_361_, lean_object* v_offsetDateTime_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_360_, v_offsetDateTime_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim___redArg(lean_object* v_t_364_, lean_object* v_localDateTime_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_364_, v_localDateTime_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim(lean_object* v_motive_367_, lean_object* v_t_368_, lean_object* v_h_369_, lean_object* v_localDateTime_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_368_, v_localDateTime_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim___redArg(lean_object* v_t_372_, lean_object* v_localDate_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_372_, v_localDate_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim(lean_object* v_motive_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_localDate_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_376_, v_localDate_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim___redArg(lean_object* v_t_380_, lean_object* v_localTime_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_380_, v_localTime_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim(lean_object* v_motive_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_localTime_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_384_, v_localTime_386_);
return v___x_387_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_388_ = lean_box(0);
v___x_389_ = ((lean_object*)(l_Lake_Toml_instInhabitedTime_default));
v___x_390_ = l_Lake_instInhabitedDate_default;
v___x_391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
lean_ctor_set(v___x_391_, 2, v___x_388_);
return v___x_391_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime_default(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_once(&l_Lake_Toml_instInhabitedDateTime_default___closed__0, &l_Lake_Toml_instInhabitedDateTime_default___closed__0_once, _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0);
return v___x_392_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime(void){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lake_Toml_instInhabitedDateTime_default;
return v___x_393_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(uint8_t v___x_394_, uint8_t v___y_395_, uint8_t v___y_396_){
_start:
{
if (v___y_395_ == 0)
{
if (v___y_396_ == 0)
{
return v___x_394_;
}
else
{
return v___y_395_;
}
}
else
{
return v___y_396_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed(lean_object* v___x_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
uint8_t v___x_270__boxed_400_; uint8_t v___y_271__boxed_401_; uint8_t v___y_272__boxed_402_; uint8_t v_res_403_; lean_object* v_r_404_; 
v___x_270__boxed_400_ = lean_unbox(v___x_397_);
v___y_271__boxed_401_ = lean_unbox(v___y_398_);
v___y_272__boxed_402_ = lean_unbox(v___y_399_);
v_res_403_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(v___x_270__boxed_400_, v___y_271__boxed_401_, v___y_272__boxed_402_);
v_r_404_ = lean_box(v_res_403_);
return v_r_404_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(lean_object* v___f_405_, lean_object* v_a_406_, lean_object* v_b_407_){
_start:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqTime___boxed), 2, 0);
v___x_409_ = l_instDecidableEqProd___redArg(v___f_405_, v___x_408_, v_a_406_, v_b_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed(lean_object* v___f_410_, lean_object* v_a_411_, lean_object* v_b_412_){
_start:
{
uint8_t v_res_413_; lean_object* v_r_414_; 
v_res_413_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(v___f_410_, v_a_411_, v_b_412_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq(lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
switch(lean_obj_tag(v_x_415_))
{
case 0:
{
if (lean_obj_tag(v_x_416_) == 0)
{
lean_object* v_date_417_; lean_object* v_time_418_; lean_object* v_offset_x3f_419_; lean_object* v_date_420_; lean_object* v_time_421_; lean_object* v_offset_x3f_422_; uint8_t v___x_423_; 
v_date_417_ = lean_ctor_get(v_x_415_, 0);
lean_inc_ref(v_date_417_);
v_time_418_ = lean_ctor_get(v_x_415_, 1);
lean_inc_ref(v_time_418_);
v_offset_x3f_419_ = lean_ctor_get(v_x_415_, 2);
lean_inc(v_offset_x3f_419_);
lean_dec_ref(v_x_415_);
v_date_420_ = lean_ctor_get(v_x_416_, 0);
lean_inc_ref(v_date_420_);
v_time_421_ = lean_ctor_get(v_x_416_, 1);
lean_inc_ref(v_time_421_);
v_offset_x3f_422_ = lean_ctor_get(v_x_416_, 2);
lean_inc(v_offset_x3f_422_);
lean_dec_ref(v_x_416_);
v___x_423_ = l_Lake_instDecidableEqDate_decEq(v_date_417_, v_date_420_);
lean_dec_ref(v_date_420_);
lean_dec_ref(v_date_417_);
if (v___x_423_ == 0)
{
lean_dec(v_offset_x3f_422_);
lean_dec_ref(v_time_421_);
lean_dec(v_offset_x3f_419_);
lean_dec_ref(v_time_418_);
return v___x_423_;
}
else
{
uint8_t v___x_424_; 
v___x_424_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_418_, v_time_421_);
lean_dec_ref(v_time_421_);
lean_dec_ref(v_time_418_);
if (v___x_424_ == 0)
{
lean_dec(v_offset_x3f_422_);
lean_dec(v_offset_x3f_419_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; lean_object* v___f_426_; lean_object* v___f_427_; uint8_t v___x_428_; 
v___x_425_ = lean_box(v___x_424_);
v___f_426_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed), 3, 1);
lean_closure_set(v___f_426_, 0, v___x_425_);
v___f_427_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed), 3, 1);
lean_closure_set(v___f_427_, 0, v___f_426_);
v___x_428_ = l_Option_instDecidableEq___redArg(v___f_427_, v_offset_x3f_419_, v_offset_x3f_422_);
return v___x_428_;
}
}
}
else
{
uint8_t v___x_429_; 
lean_dec_ref(v_x_415_);
lean_dec_ref(v_x_416_);
v___x_429_ = 0;
return v___x_429_;
}
}
case 1:
{
if (lean_obj_tag(v_x_416_) == 1)
{
lean_object* v_date_430_; lean_object* v_time_431_; lean_object* v_date_432_; lean_object* v_time_433_; uint8_t v___x_434_; 
v_date_430_ = lean_ctor_get(v_x_415_, 0);
lean_inc_ref(v_date_430_);
v_time_431_ = lean_ctor_get(v_x_415_, 1);
lean_inc_ref(v_time_431_);
lean_dec_ref(v_x_415_);
v_date_432_ = lean_ctor_get(v_x_416_, 0);
lean_inc_ref(v_date_432_);
v_time_433_ = lean_ctor_get(v_x_416_, 1);
lean_inc_ref(v_time_433_);
lean_dec_ref(v_x_416_);
v___x_434_ = l_Lake_instDecidableEqDate_decEq(v_date_430_, v_date_432_);
lean_dec_ref(v_date_432_);
lean_dec_ref(v_date_430_);
if (v___x_434_ == 0)
{
lean_dec_ref(v_time_433_);
lean_dec_ref(v_time_431_);
return v___x_434_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_431_, v_time_433_);
lean_dec_ref(v_time_433_);
lean_dec_ref(v_time_431_);
return v___x_435_;
}
}
else
{
uint8_t v___x_436_; 
lean_dec_ref(v_x_415_);
lean_dec_ref(v_x_416_);
v___x_436_ = 0;
return v___x_436_;
}
}
case 2:
{
if (lean_obj_tag(v_x_416_) == 2)
{
lean_object* v_date_437_; lean_object* v_date_438_; uint8_t v___x_439_; 
v_date_437_ = lean_ctor_get(v_x_415_, 0);
lean_inc_ref(v_date_437_);
lean_dec_ref(v_x_415_);
v_date_438_ = lean_ctor_get(v_x_416_, 0);
lean_inc_ref(v_date_438_);
lean_dec_ref(v_x_416_);
v___x_439_ = l_Lake_instDecidableEqDate_decEq(v_date_437_, v_date_438_);
lean_dec_ref(v_date_438_);
lean_dec_ref(v_date_437_);
return v___x_439_;
}
else
{
uint8_t v___x_440_; 
lean_dec_ref(v_x_415_);
lean_dec_ref(v_x_416_);
v___x_440_ = 0;
return v___x_440_;
}
}
default: 
{
if (lean_obj_tag(v_x_416_) == 3)
{
lean_object* v_time_441_; lean_object* v_time_442_; uint8_t v___x_443_; 
v_time_441_ = lean_ctor_get(v_x_415_, 0);
lean_inc_ref(v_time_441_);
lean_dec_ref(v_x_415_);
v_time_442_ = lean_ctor_get(v_x_416_, 0);
lean_inc_ref(v_time_442_);
lean_dec_ref(v_x_416_);
v___x_443_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_441_, v_time_442_);
lean_dec_ref(v_time_442_);
lean_dec_ref(v_time_441_);
return v___x_443_;
}
else
{
uint8_t v___x_444_; 
lean_dec_ref(v_x_415_);
lean_dec_ref(v_x_416_);
v___x_444_ = 0;
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___boxed(lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_445_, v_x_446_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime(lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_449_, v_x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime___boxed(lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
uint8_t v_res_454_; lean_object* v_r_455_; 
v_res_454_ = l_Lake_Toml_instDecidableEqDateTime(v_x_452_, v_x_453_);
v_r_455_ = lean_box(v_res_454_);
return v_r_455_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeDateDateTime___lam__0(lean_object* v_date_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_457_, 0, v_date_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeTimeDateTime___lam__0(lean_object* v_time_460_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_461_, 0, v_time_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(lean_object* v_s_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0));
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___boxed(lean_object* v_s_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(v_s_468_);
lean_dec_ref(v_s_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(lean_object* v_s_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0));
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___boxed(lean_object* v_s_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(v_s_472_);
lean_dec_ref(v_s_472_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(lean_object* v_s_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0));
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___boxed(lean_object* v_s_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(v_s_476_);
lean_dec_ref(v_s_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(lean_object* v_head_478_, lean_object* v_a_479_, lean_object* v_b_480_){
_start:
{
if (lean_obj_tag(v_a_479_) == 0)
{
lean_object* v_currPos_481_; lean_object* v_searcher_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_521_; 
v_currPos_481_ = lean_ctor_get(v_a_479_, 0);
v_searcher_482_ = lean_ctor_get(v_a_479_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_a_479_);
if (v_isSharedCheck_521_ == 0)
{
v___x_484_ = v_a_479_;
v_isShared_485_ = v_isSharedCheck_521_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_searcher_482_);
lean_inc(v_currPos_481_);
lean_dec(v_a_479_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_521_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v_str_486_; lean_object* v_startInclusive_487_; lean_object* v_endExclusive_488_; lean_object* v_it_490_; lean_object* v_startInclusive_491_; lean_object* v_endExclusive_492_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_str_486_ = lean_ctor_get(v_head_478_, 0);
v_startInclusive_487_ = lean_ctor_get(v_head_478_, 1);
v_endExclusive_488_ = lean_ctor_get(v_head_478_, 2);
v___x_499_ = lean_nat_sub(v_endExclusive_488_, v_startInclusive_487_);
v___x_500_ = lean_nat_dec_eq(v_searcher_482_, v___x_499_);
if (v___x_500_ == 0)
{
uint32_t v___x_501_; lean_object* v___x_502_; uint32_t v___x_503_; uint8_t v___x_504_; 
lean_dec(v___x_499_);
v___x_501_ = 43;
v___x_502_ = lean_nat_add(v_startInclusive_487_, v_searcher_482_);
v___x_503_ = lean_string_utf8_get_fast(v_str_486_, v___x_502_);
v___x_504_ = lean_uint32_dec_eq(v___x_503_, v___x_501_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
lean_dec(v_searcher_482_);
v___x_505_ = lean_string_utf8_next_fast(v_str_486_, v___x_502_);
lean_dec(v___x_502_);
v___x_506_ = lean_nat_sub(v___x_505_, v_startInclusive_487_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v___x_506_);
v___x_508_ = v___x_484_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_currPos_481_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_506_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
v_a_479_ = v___x_508_;
goto _start;
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_slice_514_; lean_object* v_nextIt_516_; 
v___x_511_ = lean_string_utf8_next_fast(v_str_486_, v___x_502_);
v___x_512_ = lean_nat_sub(v___x_511_, v___x_502_);
lean_dec(v___x_502_);
v___x_513_ = lean_nat_add(v_searcher_482_, v___x_512_);
lean_dec(v___x_512_);
v_slice_514_ = l_String_Slice_subslice_x21(v_head_478_, v_currPos_481_, v_searcher_482_);
lean_inc(v___x_513_);
if (v_isShared_485_ == 0)
{
lean_ctor_set(v___x_484_, 1, v___x_513_);
lean_ctor_set(v___x_484_, 0, v___x_513_);
v_nextIt_516_ = v___x_484_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_513_);
v_nextIt_516_ = v_reuseFailAlloc_519_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v_startInclusive_517_; lean_object* v_endExclusive_518_; 
v_startInclusive_517_ = lean_ctor_get(v_slice_514_, 0);
lean_inc(v_startInclusive_517_);
v_endExclusive_518_ = lean_ctor_get(v_slice_514_, 1);
lean_inc(v_endExclusive_518_);
lean_dec_ref(v_slice_514_);
v_it_490_ = v_nextIt_516_;
v_startInclusive_491_ = v_startInclusive_517_;
v_endExclusive_492_ = v_endExclusive_518_;
goto v___jp_489_;
}
}
}
else
{
lean_object* v___x_520_; 
lean_del_object(v___x_484_);
lean_dec(v_searcher_482_);
v___x_520_ = lean_box(1);
v_it_490_ = v___x_520_;
v_startInclusive_491_ = v_currPos_481_;
v_endExclusive_492_ = v___x_499_;
goto v___jp_489_;
}
v___jp_489_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_493_ = lean_nat_add(v_startInclusive_487_, v_startInclusive_491_);
lean_dec(v_startInclusive_491_);
v___x_494_ = lean_nat_add(v_startInclusive_487_, v_endExclusive_492_);
lean_dec(v_endExclusive_492_);
lean_inc_ref(v_str_486_);
v___x_495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_495_, 0, v_str_486_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
lean_ctor_set(v___x_495_, 2, v___x_494_);
v___x_496_ = l_String_Slice_toString(v___x_495_);
lean_dec_ref(v___x_495_);
v___x_497_ = lean_array_push(v_b_480_, v___x_496_);
v_a_479_ = v_it_490_;
v_b_480_ = v___x_497_;
goto _start;
}
}
}
else
{
return v_b_480_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg___boxed(lean_object* v_head_522_, lean_object* v_a_523_, lean_object* v_b_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_522_, v_a_523_, v_b_524_);
lean_dec_ref(v_head_522_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(lean_object* v_dt_526_, lean_object* v___x_527_, lean_object* v___x_528_, lean_object* v_a_529_, lean_object* v_b_530_){
_start:
{
lean_object* v_it_532_; lean_object* v_startInclusive_533_; lean_object* v_endExclusive_534_; 
if (lean_obj_tag(v_a_529_) == 0)
{
lean_object* v_currPos_538_; lean_object* v_searcher_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_570_; 
v_currPos_538_ = lean_ctor_get(v_a_529_, 0);
v_searcher_539_ = lean_ctor_get(v_a_529_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_a_529_);
if (v_isSharedCheck_570_ == 0)
{
v___x_541_ = v_a_529_;
v_isShared_542_ = v_isSharedCheck_570_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_searcher_539_);
lean_inc(v_currPos_538_);
lean_dec(v_a_529_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_570_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_startInclusive_553_; lean_object* v_endExclusive_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v_startInclusive_553_ = lean_ctor_get(v___x_527_, 1);
v_endExclusive_554_ = lean_ctor_get(v___x_527_, 2);
v___x_555_ = lean_nat_sub(v_endExclusive_554_, v_startInclusive_553_);
v___x_556_ = lean_nat_dec_eq(v_searcher_539_, v___x_555_);
lean_dec(v___x_555_);
if (v___x_556_ == 0)
{
uint32_t v___x_557_; uint8_t v___y_559_; uint32_t v___x_565_; uint8_t v___x_566_; 
v___x_557_ = lean_string_utf8_get_fast(v_dt_526_, v_searcher_539_);
v___x_565_ = 84;
v___x_566_ = lean_uint32_dec_eq(v___x_557_, v___x_565_);
if (v___x_566_ == 0)
{
uint32_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 116;
v___x_568_ = lean_uint32_dec_eq(v___x_557_, v___x_567_);
v___y_559_ = v___x_568_;
goto v___jp_558_;
}
else
{
v___y_559_ = v___x_566_;
goto v___jp_558_;
}
v___jp_558_:
{
if (v___y_559_ == 0)
{
uint32_t v___x_560_; uint8_t v___x_561_; 
v___x_560_ = 32;
v___x_561_ = lean_uint32_dec_eq(v___x_557_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_del_object(v___x_541_);
v___x_562_ = lean_string_utf8_next_fast(v_dt_526_, v_searcher_539_);
lean_dec(v_searcher_539_);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_currPos_538_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v_a_529_ = v___x_563_;
goto _start;
}
else
{
goto v___jp_543_;
}
}
else
{
goto v___jp_543_;
}
}
}
else
{
lean_object* v___x_569_; 
lean_del_object(v___x_541_);
lean_dec(v_searcher_539_);
v___x_569_ = lean_box(1);
lean_inc(v___x_528_);
v_it_532_ = v___x_569_;
v_startInclusive_533_ = v_currPos_538_;
v_endExclusive_534_ = v___x_528_;
goto v___jp_531_;
}
v___jp_543_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_slice_547_; lean_object* v_nextIt_549_; 
v___x_544_ = lean_string_utf8_next_fast(v_dt_526_, v_searcher_539_);
v___x_545_ = lean_nat_sub(v___x_544_, v_searcher_539_);
v___x_546_ = lean_nat_add(v_searcher_539_, v___x_545_);
lean_dec(v___x_545_);
v_slice_547_ = l_String_Slice_subslice_x21(v___x_527_, v_currPos_538_, v_searcher_539_);
lean_inc(v___x_546_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v___x_546_);
lean_ctor_set(v___x_541_, 0, v___x_546_);
v_nextIt_549_ = v___x_541_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_546_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_546_);
v_nextIt_549_ = v_reuseFailAlloc_552_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v_startInclusive_550_; lean_object* v_endExclusive_551_; 
v_startInclusive_550_ = lean_ctor_get(v_slice_547_, 0);
lean_inc(v_startInclusive_550_);
v_endExclusive_551_ = lean_ctor_get(v_slice_547_, 1);
lean_inc(v_endExclusive_551_);
lean_dec_ref(v_slice_547_);
v_it_532_ = v_nextIt_549_;
v_startInclusive_533_ = v_startInclusive_550_;
v_endExclusive_534_ = v_endExclusive_551_;
goto v___jp_531_;
}
}
}
}
else
{
lean_dec(v___x_528_);
lean_dec_ref(v_dt_526_);
return v_b_530_;
}
v___jp_531_:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_inc_ref(v_dt_526_);
v___x_535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_535_, 0, v_dt_526_);
lean_ctor_set(v___x_535_, 1, v_startInclusive_533_);
lean_ctor_set(v___x_535_, 2, v_endExclusive_534_);
v___x_536_ = lean_array_push(v_b_530_, v___x_535_);
v_a_529_ = v_it_532_;
v_b_530_ = v___x_536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg___boxed(lean_object* v_dt_571_, lean_object* v___x_572_, lean_object* v___x_573_, lean_object* v_a_574_, lean_object* v_b_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_571_, v___x_572_, v___x_573_, v_a_574_, v_b_575_);
lean_dec_ref(v___x_572_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(lean_object* v_head_577_, lean_object* v_a_578_, lean_object* v_b_579_){
_start:
{
if (lean_obj_tag(v_a_578_) == 0)
{
lean_object* v_currPos_580_; lean_object* v_searcher_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_620_; 
v_currPos_580_ = lean_ctor_get(v_a_578_, 0);
v_searcher_581_ = lean_ctor_get(v_a_578_, 1);
v_isSharedCheck_620_ = !lean_is_exclusive(v_a_578_);
if (v_isSharedCheck_620_ == 0)
{
v___x_583_ = v_a_578_;
v_isShared_584_ = v_isSharedCheck_620_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_searcher_581_);
lean_inc(v_currPos_580_);
lean_dec(v_a_578_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_620_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_str_585_; lean_object* v_startInclusive_586_; lean_object* v_endExclusive_587_; lean_object* v_it_589_; lean_object* v_startInclusive_590_; lean_object* v_endExclusive_591_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_str_585_ = lean_ctor_get(v_head_577_, 0);
v_startInclusive_586_ = lean_ctor_get(v_head_577_, 1);
v_endExclusive_587_ = lean_ctor_get(v_head_577_, 2);
v___x_598_ = lean_nat_sub(v_endExclusive_587_, v_startInclusive_586_);
v___x_599_ = lean_nat_dec_eq(v_searcher_581_, v___x_598_);
if (v___x_599_ == 0)
{
uint32_t v___x_600_; lean_object* v___x_601_; uint32_t v___x_602_; uint8_t v___x_603_; 
lean_dec(v___x_598_);
v___x_600_ = 45;
v___x_601_ = lean_nat_add(v_startInclusive_586_, v_searcher_581_);
v___x_602_ = lean_string_utf8_get_fast(v_str_585_, v___x_601_);
v___x_603_ = lean_uint32_dec_eq(v___x_602_, v___x_600_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
lean_dec(v_searcher_581_);
v___x_604_ = lean_string_utf8_next_fast(v_str_585_, v___x_601_);
lean_dec(v___x_601_);
v___x_605_ = lean_nat_sub(v___x_604_, v_startInclusive_586_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v___x_605_);
v___x_607_ = v___x_583_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_currPos_580_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v___x_605_);
v___x_607_ = v_reuseFailAlloc_609_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
v_a_578_ = v___x_607_;
goto _start;
}
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_slice_613_; lean_object* v_nextIt_615_; 
v___x_610_ = lean_string_utf8_next_fast(v_str_585_, v___x_601_);
v___x_611_ = lean_nat_sub(v___x_610_, v___x_601_);
lean_dec(v___x_601_);
v___x_612_ = lean_nat_add(v_searcher_581_, v___x_611_);
lean_dec(v___x_611_);
v_slice_613_ = l_String_Slice_subslice_x21(v_head_577_, v_currPos_580_, v_searcher_581_);
lean_inc(v___x_612_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v___x_612_);
lean_ctor_set(v___x_583_, 0, v___x_612_);
v_nextIt_615_ = v___x_583_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v___x_612_);
v_nextIt_615_ = v_reuseFailAlloc_618_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v_startInclusive_616_; lean_object* v_endExclusive_617_; 
v_startInclusive_616_ = lean_ctor_get(v_slice_613_, 0);
lean_inc(v_startInclusive_616_);
v_endExclusive_617_ = lean_ctor_get(v_slice_613_, 1);
lean_inc(v_endExclusive_617_);
lean_dec_ref(v_slice_613_);
v_it_589_ = v_nextIt_615_;
v_startInclusive_590_ = v_startInclusive_616_;
v_endExclusive_591_ = v_endExclusive_617_;
goto v___jp_588_;
}
}
}
else
{
lean_object* v___x_619_; 
lean_del_object(v___x_583_);
lean_dec(v_searcher_581_);
v___x_619_ = lean_box(1);
v_it_589_ = v___x_619_;
v_startInclusive_590_ = v_currPos_580_;
v_endExclusive_591_ = v___x_598_;
goto v___jp_588_;
}
v___jp_588_:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_592_ = lean_nat_add(v_startInclusive_586_, v_startInclusive_590_);
lean_dec(v_startInclusive_590_);
v___x_593_ = lean_nat_add(v_startInclusive_586_, v_endExclusive_591_);
lean_dec(v_endExclusive_591_);
lean_inc_ref(v_str_585_);
v___x_594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_594_, 0, v_str_585_);
lean_ctor_set(v___x_594_, 1, v___x_592_);
lean_ctor_set(v___x_594_, 2, v___x_593_);
v___x_595_ = l_String_Slice_toString(v___x_594_);
lean_dec_ref(v___x_594_);
v___x_596_ = lean_array_push(v_b_579_, v___x_595_);
v_a_578_ = v_it_589_;
v_b_579_ = v___x_596_;
goto _start;
}
}
}
else
{
return v_b_579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg___boxed(lean_object* v_head_621_, lean_object* v_a_622_, lean_object* v_b_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_621_, v_a_622_, v_b_623_);
lean_dec_ref(v_head_621_);
return v_res_624_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(lean_object* v_s_625_, lean_object* v_a_626_, uint8_t v_b_627_){
_start:
{
lean_object* v_str_628_; lean_object* v_startInclusive_629_; lean_object* v_endExclusive_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_str_628_ = lean_ctor_get(v_s_625_, 0);
v_startInclusive_629_ = lean_ctor_get(v_s_625_, 1);
v_endExclusive_630_ = lean_ctor_get(v_s_625_, 2);
v___x_631_ = lean_nat_sub(v_endExclusive_630_, v_startInclusive_629_);
v___x_632_ = lean_nat_dec_eq(v_a_626_, v___x_631_);
lean_dec(v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; uint32_t v___x_634_; uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_633_ = lean_nat_add(v_startInclusive_629_, v_a_626_);
lean_dec(v_a_626_);
v___x_634_ = lean_string_utf8_get_fast(v_str_628_, v___x_633_);
v___x_635_ = 58;
v___x_636_ = lean_uint32_dec_eq(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_string_utf8_next_fast(v_str_628_, v___x_633_);
lean_dec(v___x_633_);
v___x_638_ = lean_nat_sub(v___x_637_, v_startInclusive_629_);
v_a_626_ = v___x_638_;
v_b_627_ = v___x_636_;
goto _start;
}
else
{
lean_dec(v___x_633_);
return v___x_636_;
}
}
else
{
lean_dec(v_a_626_);
return v_b_627_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_s_640_, lean_object* v_a_641_, lean_object* v_b_642_){
_start:
{
uint8_t v_b_boxed_643_; uint8_t v_res_644_; lean_object* v_r_645_; 
v_b_boxed_643_ = lean_unbox(v_b_642_);
v_res_644_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_640_, v_a_641_, v_b_boxed_643_);
lean_dec_ref(v_s_640_);
v_r_645_ = lean_box(v_res_644_);
return v_r_645_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(lean_object* v_s_646_){
_start:
{
lean_object* v_searcher_647_; uint8_t v___x_648_; uint8_t v___x_649_; 
v_searcher_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = 0;
v___x_649_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_646_, v_searcher_647_, v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2___boxed(lean_object* v_s_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_s_650_);
lean_dec_ref(v_s_650_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ofString_x3f(lean_object* v_dt_653_){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = lean_string_utf8_byte_size(v_dt_653_);
lean_inc_ref(v_dt_653_);
v___x_656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_656_, 0, v_dt_653_);
lean_ctor_set(v___x_656_, 1, v___x_654_);
lean_ctor_set(v___x_656_, 2, v___x_655_);
v___x_657_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(v___x_656_);
v___x_658_ = ((lean_object*)(l_Lake_Toml_Time_ofString_x3f___closed__0));
v___x_659_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_653_, v___x_656_, v___x_655_, v___x_657_, v___x_658_);
lean_dec_ref(v___x_656_);
v___x_660_ = lean_array_to_list(v___x_659_);
if (lean_obj_tag(v___x_660_) == 1)
{
lean_object* v_tail_661_; 
v_tail_661_ = lean_ctor_get(v___x_660_, 1);
lean_inc(v_tail_661_);
if (lean_obj_tag(v_tail_661_) == 0)
{
lean_object* v_head_662_; uint8_t v___x_663_; 
v_head_662_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_head_662_);
lean_dec_ref(v___x_660_);
v___x_663_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_head_662_);
if (v___x_663_ == 0)
{
lean_object* v_str_664_; lean_object* v_startInclusive_665_; lean_object* v_endExclusive_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_str_664_ = lean_ctor_get(v_head_662_, 0);
lean_inc_ref(v_str_664_);
v_startInclusive_665_ = lean_ctor_get(v_head_662_, 1);
lean_inc(v_startInclusive_665_);
v_endExclusive_666_ = lean_ctor_get(v_head_662_, 2);
lean_inc(v_endExclusive_666_);
lean_dec(v_head_662_);
v___x_667_ = lean_string_utf8_extract(v_str_664_, v_startInclusive_665_, v_endExclusive_666_);
lean_dec(v_endExclusive_666_);
lean_dec(v_startInclusive_665_);
lean_dec_ref(v_str_664_);
v___x_668_ = l_Lake_Date_ofString_x3f(v___x_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v___x_669_; 
v___x_669_ = lean_box(0);
return v___x_669_;
}
else
{
lean_object* v_val_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_val_670_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v___x_668_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_val_670_);
lean_dec(v___x_668_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_674_, 0, v_val_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_object* v_str_679_; lean_object* v_startInclusive_680_; lean_object* v_endExclusive_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
v_str_679_ = lean_ctor_get(v_head_662_, 0);
lean_inc_ref(v_str_679_);
v_startInclusive_680_ = lean_ctor_get(v_head_662_, 1);
lean_inc(v_startInclusive_680_);
v_endExclusive_681_ = lean_ctor_get(v_head_662_, 2);
lean_inc(v_endExclusive_681_);
lean_dec(v_head_662_);
v___x_682_ = lean_string_utf8_extract(v_str_679_, v_startInclusive_680_, v_endExclusive_681_);
lean_dec(v_endExclusive_681_);
lean_dec(v_startInclusive_680_);
lean_dec_ref(v_str_679_);
v___x_683_ = l_Lake_Toml_Time_ofString_x3f(v___x_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v___x_684_; 
v___x_684_ = lean_box(0);
return v___x_684_;
}
else
{
lean_object* v_val_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_693_; 
v_val_685_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_693_ == 0)
{
v___x_687_ = v___x_683_;
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_val_685_);
lean_dec(v___x_683_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_689_, 0, v_val_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
else
{
lean_object* v_tail_694_; 
v_tail_694_ = lean_ctor_get(v_tail_661_, 1);
if (lean_obj_tag(v_tail_694_) == 0)
{
lean_object* v_head_695_; lean_object* v_head_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_872_; 
v_head_695_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_head_695_);
lean_dec_ref(v___x_660_);
v_head_696_ = lean_ctor_get(v_tail_661_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v_tail_661_);
if (v_isSharedCheck_872_ == 0)
{
lean_object* v_unused_873_; 
v_unused_873_ = lean_ctor_get(v_tail_661_, 1);
lean_dec(v_unused_873_);
v___x_698_ = v_tail_661_;
v_isShared_699_ = v_isSharedCheck_872_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_head_696_);
lean_dec(v_tail_661_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_872_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_str_700_; lean_object* v_startInclusive_701_; lean_object* v_endExclusive_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_str_700_ = lean_ctor_get(v_head_695_, 0);
lean_inc_ref(v_str_700_);
v_startInclusive_701_ = lean_ctor_get(v_head_695_, 1);
lean_inc(v_startInclusive_701_);
v_endExclusive_702_ = lean_ctor_get(v_head_695_, 2);
lean_inc(v_endExclusive_702_);
lean_dec(v_head_695_);
v___x_703_ = lean_string_utf8_extract(v_str_700_, v_startInclusive_701_, v_endExclusive_702_);
lean_dec(v_endExclusive_702_);
lean_dec(v_startInclusive_701_);
lean_dec_ref(v_str_700_);
v___x_704_ = l_Lake_Date_ofString_x3f(v___x_703_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v___x_705_; 
lean_del_object(v___x_698_);
lean_dec(v_head_696_);
v___x_705_ = lean_box(0);
return v___x_705_;
}
else
{
lean_object* v_val_706_; lean_object* v_str_707_; lean_object* v_startInclusive_708_; lean_object* v_endExclusive_709_; uint8_t v___y_726_; uint8_t v___y_774_; uint32_t v___y_849_; uint32_t v___y_853_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_val_706_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_val_706_);
lean_dec_ref(v___x_704_);
v_str_707_ = lean_ctor_get(v_head_696_, 0);
v_startInclusive_708_ = lean_ctor_get(v_head_696_, 1);
v_endExclusive_709_ = lean_ctor_get(v_head_696_, 2);
v___x_864_ = lean_nat_sub(v_endExclusive_709_, v_startInclusive_708_);
v___x_865_ = l_String_Slice_Pos_prev_x3f(v_head_696_, v___x_864_);
lean_dec(v___x_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
uint32_t v___x_866_; 
v___x_866_ = 65;
v___y_853_ = v___x_866_;
goto v___jp_852_;
}
else
{
lean_object* v_val_867_; lean_object* v___x_868_; 
v_val_867_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_val_867_);
lean_dec_ref(v___x_865_);
v___x_868_ = l_String_Slice_Pos_get_x3f(v_head_696_, v_val_867_);
lean_dec(v_val_867_);
if (lean_obj_tag(v___x_868_) == 0)
{
uint32_t v___x_869_; 
v___x_869_ = 65;
v___y_853_ = v___x_869_;
goto v___jp_852_;
}
else
{
lean_object* v_val_870_; uint32_t v___x_871_; 
v_val_870_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_val_870_);
lean_dec_ref(v___x_868_);
v___x_871_ = lean_unbox_uint32(v_val_870_);
lean_dec(v_val_870_);
v___y_853_ = v___x_871_;
goto v___jp_852_;
}
}
v___jp_710_:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_string_utf8_extract(v_str_707_, v_startInclusive_708_, v_endExclusive_709_);
lean_dec(v_endExclusive_709_);
lean_dec(v_startInclusive_708_);
lean_dec_ref(v_str_707_);
v___x_712_ = l_Lake_Toml_Time_ofString_x3f(v___x_711_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; 
lean_dec(v_val_706_);
lean_del_object(v___x_698_);
v___x_713_ = lean_box(0);
return v___x_713_;
}
else
{
lean_object* v_val_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_724_; 
v_val_714_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_724_ == 0)
{
v___x_716_ = v___x_712_;
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_val_714_);
lean_dec(v___x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_val_714_);
lean_ctor_set(v___x_698_, 0, v_val_706_);
v___x_719_ = v___x_698_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_val_706_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_val_714_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_719_);
v___x_721_ = v___x_716_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
v___jp_725_:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_769_; 
v___x_727_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(v_head_696_);
v___x_728_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_696_, v___x_727_, v___x_658_);
v_isSharedCheck_769_ = !lean_is_exclusive(v_head_696_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; lean_object* v_unused_771_; lean_object* v_unused_772_; 
v_unused_770_ = lean_ctor_get(v_head_696_, 2);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_head_696_, 1);
lean_dec(v_unused_771_);
v_unused_772_ = lean_ctor_get(v_head_696_, 0);
lean_dec(v_unused_772_);
v___x_730_ = v_head_696_;
v_isShared_731_ = v_isSharedCheck_769_;
goto v_resetjp_729_;
}
else
{
lean_dec(v_head_696_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_769_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; 
v___x_732_ = lean_array_to_list(v___x_728_);
if (lean_obj_tag(v___x_732_) == 1)
{
lean_object* v_tail_733_; 
v_tail_733_ = lean_ctor_get(v___x_732_, 1);
lean_inc(v_tail_733_);
if (lean_obj_tag(v_tail_733_) == 1)
{
lean_object* v_tail_734_; 
v_tail_734_ = lean_ctor_get(v_tail_733_, 1);
if (lean_obj_tag(v_tail_734_) == 0)
{
lean_object* v_head_735_; lean_object* v_head_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_endExclusive_709_);
lean_dec(v_startInclusive_708_);
lean_dec_ref(v_str_707_);
lean_del_object(v___x_698_);
v_head_735_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_head_735_);
lean_dec_ref(v___x_732_);
v_head_736_ = lean_ctor_get(v_tail_733_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_tail_733_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v_tail_733_, 1);
lean_dec(v_unused_768_);
v___x_738_ = v_tail_733_;
v_isShared_739_ = v_isSharedCheck_767_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_head_736_);
lean_dec(v_tail_733_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_767_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lake_Toml_Time_ofString_x3f(v_head_735_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v___x_741_; 
lean_del_object(v___x_738_);
lean_dec(v_head_736_);
lean_del_object(v___x_730_);
lean_dec(v_val_706_);
v___x_741_ = lean_box(0);
return v___x_741_;
}
else
{
lean_object* v_val_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_766_; 
v_val_742_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_766_ == 0)
{
v___x_744_ = v___x_740_;
v_isShared_745_ = v_isSharedCheck_766_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_val_742_);
lean_dec(v___x_740_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_766_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lake_Toml_Time_ofString_x3f(v_head_736_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v___x_747_; 
lean_del_object(v___x_744_);
lean_dec(v_val_742_);
lean_del_object(v___x_738_);
lean_del_object(v___x_730_);
lean_dec(v_val_706_);
v___x_747_ = lean_box(0);
return v___x_747_;
}
else
{
lean_object* v_val_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_765_; 
v_val_748_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_765_ == 0)
{
v___x_750_ = v___x_746_;
v_isShared_751_ = v_isSharedCheck_765_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_val_748_);
lean_dec(v___x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_765_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = lean_box(v___y_726_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 0);
lean_ctor_set(v___x_738_, 1, v_val_748_);
lean_ctor_set(v___x_738_, 0, v___x_752_);
v___x_754_ = v___x_738_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_val_748_);
v___x_754_ = v_reuseFailAlloc_764_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_754_);
v___x_756_ = v___x_750_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_763_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 2, v___x_756_);
lean_ctor_set(v___x_730_, 1, v_val_742_);
lean_ctor_set(v___x_730_, 0, v_val_706_);
v___x_758_ = v___x_730_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_val_706_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_val_742_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v___x_756_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_758_);
v___x_760_ = v___x_744_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_tail_733_);
lean_dec_ref(v___x_732_);
lean_del_object(v___x_730_);
goto v___jp_710_;
}
}
else
{
lean_dec_ref(v___x_732_);
lean_dec(v_tail_733_);
lean_del_object(v___x_730_);
goto v___jp_710_;
}
}
else
{
lean_dec(v___x_732_);
lean_del_object(v___x_730_);
goto v___jp_710_;
}
}
}
v___jp_773_:
{
if (v___y_774_ == 0)
{
uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = 1;
v___x_776_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(v_head_696_);
v___x_777_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_696_, v___x_776_, v___x_658_);
v___x_778_ = lean_array_to_list(v___x_777_);
if (lean_obj_tag(v___x_778_) == 1)
{
lean_object* v_tail_779_; 
v_tail_779_ = lean_ctor_get(v___x_778_, 1);
lean_inc(v_tail_779_);
if (lean_obj_tag(v_tail_779_) == 1)
{
lean_object* v_tail_780_; 
v_tail_780_ = lean_ctor_get(v_tail_779_, 1);
if (lean_obj_tag(v_tail_780_) == 0)
{
lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_818_; 
lean_del_object(v___x_698_);
v_isSharedCheck_818_ = !lean_is_exclusive(v_head_696_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; lean_object* v_unused_820_; lean_object* v_unused_821_; 
v_unused_819_ = lean_ctor_get(v_head_696_, 2);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_head_696_, 1);
lean_dec(v_unused_820_);
v_unused_821_ = lean_ctor_get(v_head_696_, 0);
lean_dec(v_unused_821_);
v___x_782_ = v_head_696_;
v_isShared_783_ = v_isSharedCheck_818_;
goto v_resetjp_781_;
}
else
{
lean_dec(v_head_696_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_818_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_head_784_; lean_object* v_head_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_816_; 
v_head_784_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_head_784_);
lean_dec_ref(v___x_778_);
v_head_785_ = lean_ctor_get(v_tail_779_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_tail_779_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; 
v_unused_817_ = lean_ctor_get(v_tail_779_, 1);
lean_dec(v_unused_817_);
v___x_787_ = v_tail_779_;
v_isShared_788_ = v_isSharedCheck_816_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_head_785_);
lean_dec(v_tail_779_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_816_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lake_Toml_Time_ofString_x3f(v_head_784_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v___x_790_; 
lean_del_object(v___x_787_);
lean_dec(v_head_785_);
lean_del_object(v___x_782_);
lean_dec(v_val_706_);
v___x_790_ = lean_box(0);
return v___x_790_;
}
else
{
lean_object* v_val_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_815_; 
v_val_791_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_815_ == 0)
{
v___x_793_ = v___x_789_;
v_isShared_794_ = v_isSharedCheck_815_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_val_791_);
lean_dec(v___x_789_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_815_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lake_Toml_Time_ofString_x3f(v_head_785_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; 
lean_del_object(v___x_793_);
lean_dec(v_val_791_);
lean_del_object(v___x_787_);
lean_del_object(v___x_782_);
lean_dec(v_val_706_);
v___x_796_ = lean_box(0);
return v___x_796_;
}
else
{
lean_object* v_val_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_814_; 
v_val_797_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_814_ == 0)
{
v___x_799_ = v___x_795_;
v_isShared_800_ = v_isSharedCheck_814_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_val_797_);
lean_dec(v___x_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_814_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_box(v___y_774_);
if (v_isShared_788_ == 0)
{
lean_ctor_set_tag(v___x_787_, 0);
lean_ctor_set(v___x_787_, 1, v_val_797_);
lean_ctor_set(v___x_787_, 0, v___x_801_);
v___x_803_ = v___x_787_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_val_797_);
v___x_803_ = v_reuseFailAlloc_813_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v___x_803_);
v___x_805_ = v___x_799_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_812_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 2, v___x_805_);
lean_ctor_set(v___x_782_, 1, v_val_791_);
lean_ctor_set(v___x_782_, 0, v_val_706_);
v___x_807_ = v___x_782_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_val_706_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_val_791_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v___x_805_);
v___x_807_ = v_reuseFailAlloc_811_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
lean_object* v___x_809_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_807_);
v___x_809_ = v___x_793_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_inc(v_endExclusive_709_);
lean_inc(v_startInclusive_708_);
lean_inc_ref(v_str_707_);
lean_dec_ref(v_tail_779_);
lean_dec_ref(v___x_778_);
v___y_726_ = v___x_775_;
goto v___jp_725_;
}
}
else
{
lean_inc(v_endExclusive_709_);
lean_inc(v_startInclusive_708_);
lean_inc_ref(v_str_707_);
lean_dec_ref(v___x_778_);
lean_dec(v_tail_779_);
v___y_726_ = v___x_775_;
goto v___jp_725_;
}
}
else
{
lean_inc(v_endExclusive_709_);
lean_inc(v_startInclusive_708_);
lean_inc_ref(v_str_707_);
lean_dec(v___x_778_);
v___y_726_ = v___x_775_;
goto v___jp_725_;
}
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_844_; 
lean_inc(v_startInclusive_708_);
lean_inc_ref(v_str_707_);
lean_del_object(v___x_698_);
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = lean_nat_sub(v_endExclusive_709_, v_startInclusive_708_);
v___x_824_ = l_String_Slice_Pos_prevn(v_head_696_, v___x_823_, v___x_822_);
v_isSharedCheck_844_ = !lean_is_exclusive(v_head_696_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; lean_object* v_unused_846_; lean_object* v_unused_847_; 
v_unused_845_ = lean_ctor_get(v_head_696_, 2);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_head_696_, 1);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_head_696_, 0);
lean_dec(v_unused_847_);
v___x_826_ = v_head_696_;
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
else
{
lean_dec(v_head_696_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_nat_add(v_startInclusive_708_, v___x_824_);
lean_dec(v___x_824_);
v___x_829_ = lean_string_utf8_extract(v_str_707_, v_startInclusive_708_, v___x_828_);
lean_dec(v___x_828_);
lean_dec(v_startInclusive_708_);
lean_dec_ref(v_str_707_);
v___x_830_ = l_Lake_Toml_Time_ofString_x3f(v___x_829_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_831_; 
lean_del_object(v___x_826_);
lean_dec(v_val_706_);
v___x_831_ = lean_box(0);
return v___x_831_;
}
else
{
lean_object* v_val_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_843_; 
v_val_832_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_843_ == 0)
{
v___x_834_ = v___x_830_;
v_isShared_835_ = v_isSharedCheck_843_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_val_832_);
lean_dec(v___x_830_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_843_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = lean_box(0);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 2, v___x_836_);
lean_ctor_set(v___x_826_, 1, v_val_832_);
lean_ctor_set(v___x_826_, 0, v_val_706_);
v___x_838_ = v___x_826_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_val_706_);
lean_ctor_set(v_reuseFailAlloc_842_, 1, v_val_832_);
lean_ctor_set(v_reuseFailAlloc_842_, 2, v___x_836_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_838_);
v___x_840_ = v___x_834_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
}
v___jp_848_:
{
uint32_t v___x_850_; uint8_t v___x_851_; 
v___x_850_ = 122;
v___x_851_ = lean_uint32_dec_eq(v___y_849_, v___x_850_);
v___y_774_ = v___x_851_;
goto v___jp_773_;
}
v___jp_852_:
{
uint32_t v___x_854_; uint8_t v___x_855_; 
v___x_854_ = 90;
v___x_855_ = lean_uint32_dec_eq(v___y_853_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_nat_sub(v_endExclusive_709_, v_startInclusive_708_);
v___x_857_ = l_String_Slice_Pos_prev_x3f(v_head_696_, v___x_856_);
lean_dec(v___x_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
uint32_t v___x_858_; 
v___x_858_ = 65;
v___y_849_ = v___x_858_;
goto v___jp_848_;
}
else
{
lean_object* v_val_859_; lean_object* v___x_860_; 
v_val_859_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_val_859_);
lean_dec_ref(v___x_857_);
v___x_860_ = l_String_Slice_Pos_get_x3f(v_head_696_, v_val_859_);
lean_dec(v_val_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
uint32_t v___x_861_; 
v___x_861_ = 65;
v___y_849_ = v___x_861_;
goto v___jp_848_;
}
else
{
lean_object* v_val_862_; uint32_t v___x_863_; 
v_val_862_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_val_862_);
lean_dec_ref(v___x_860_);
v___x_863_ = lean_unbox_uint32(v_val_862_);
lean_dec(v_val_862_);
v___y_849_ = v___x_863_;
goto v___jp_848_;
}
}
}
else
{
v___y_774_ = v___x_855_;
goto v___jp_773_;
}
}
}
}
}
else
{
lean_object* v___x_874_; 
lean_dec_ref(v_tail_661_);
lean_dec_ref(v___x_660_);
v___x_874_ = lean_box(0);
return v___x_874_;
}
}
}
else
{
lean_object* v___x_875_; 
lean_dec(v___x_660_);
v___x_875_ = lean_box(0);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(lean_object* v_dt_876_, lean_object* v___x_877_, lean_object* v___x_878_, lean_object* v_inst_879_, lean_object* v_R_880_, lean_object* v_a_881_, lean_object* v_b_882_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_876_, v___x_877_, v___x_878_, v_a_881_, v_b_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___boxed(lean_object* v_dt_884_, lean_object* v___x_885_, lean_object* v___x_886_, lean_object* v_inst_887_, lean_object* v_R_888_, lean_object* v_a_889_, lean_object* v_b_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(v_dt_884_, v___x_885_, v___x_886_, v_inst_887_, v_R_888_, v_a_889_, v_b_890_);
lean_dec_ref(v___x_885_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(lean_object* v_head_892_, lean_object* v_inst_893_, lean_object* v_R_894_, lean_object* v_a_895_, lean_object* v_b_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_892_, v_a_895_, v_b_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___boxed(lean_object* v_head_898_, lean_object* v_inst_899_, lean_object* v_R_900_, lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(v_head_898_, v_inst_899_, v_R_900_, v_a_901_, v_b_902_);
lean_dec_ref(v_head_898_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(lean_object* v_head_904_, lean_object* v_inst_905_, lean_object* v_R_906_, lean_object* v_a_907_, lean_object* v_b_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_904_, v_a_907_, v_b_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___boxed(lean_object* v_head_910_, lean_object* v_inst_911_, lean_object* v_R_912_, lean_object* v_a_913_, lean_object* v_b_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(v_head_910_, v_inst_911_, v_R_912_, v_a_913_, v_b_914_);
lean_dec_ref(v_head_910_);
return v_res_915_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(lean_object* v_s_916_, lean_object* v_inst_917_, lean_object* v_R_918_, lean_object* v_a_919_, uint8_t v_b_920_, lean_object* v_c_921_){
_start:
{
uint8_t v___x_922_; 
v___x_922_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_916_, v_a_919_, v_b_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___boxed(lean_object* v_s_923_, lean_object* v_inst_924_, lean_object* v_R_925_, lean_object* v_a_926_, lean_object* v_b_927_, lean_object* v_c_928_){
_start:
{
uint8_t v_b_boxed_929_; uint8_t v_res_930_; lean_object* v_r_931_; 
v_b_boxed_929_ = lean_unbox(v_b_927_);
v_res_930_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(v_s_923_, v_inst_924_, v_R_925_, v_a_926_, v_b_boxed_929_, v_c_928_);
lean_dec_ref(v_s_923_);
v_r_931_ = lean_box(v_res_930_);
return v_r_931_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_toString(lean_object* v_dt_936_){
_start:
{
switch(lean_obj_tag(v_dt_936_))
{
case 0:
{
lean_object* v_offset_x3f_937_; 
v_offset_x3f_937_ = lean_ctor_get(v_dt_936_, 2);
if (lean_obj_tag(v_offset_x3f_937_) == 1)
{
lean_object* v_val_938_; lean_object* v_fst_939_; uint8_t v___x_940_; 
v_val_938_ = lean_ctor_get(v_offset_x3f_937_, 0);
v_fst_939_ = lean_ctor_get(v_val_938_, 0);
v___x_940_ = lean_unbox(v_fst_939_);
if (v___x_940_ == 0)
{
lean_object* v_snd_941_; lean_object* v_date_942_; lean_object* v_time_943_; lean_object* v_hour_944_; lean_object* v_minute_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_snd_941_ = lean_ctor_get(v_val_938_, 1);
lean_inc(v_snd_941_);
v_date_942_ = lean_ctor_get(v_dt_936_, 0);
lean_inc_ref(v_date_942_);
v_time_943_ = lean_ctor_get(v_dt_936_, 1);
lean_inc_ref(v_time_943_);
lean_dec_ref(v_dt_936_);
v_hour_944_ = lean_ctor_get(v_snd_941_, 0);
lean_inc(v_hour_944_);
v_minute_945_ = lean_ctor_get(v_snd_941_, 1);
lean_inc(v_minute_945_);
lean_dec(v_snd_941_);
v___x_946_ = l_Lake_Date_toString(v_date_942_);
v___x_947_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_948_ = lean_string_append(v___x_946_, v___x_947_);
v___x_949_ = l_Lake_Toml_Time_toString(v_time_943_);
v___x_950_ = lean_string_append(v___x_948_, v___x_949_);
lean_dec_ref(v___x_949_);
v___x_951_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__1));
v___x_952_ = lean_string_append(v___x_950_, v___x_951_);
v___x_953_ = lean_unsigned_to_nat(2u);
v___x_954_ = l_Lake_zpad(v_hour_944_, v___x_953_);
v___x_955_ = lean_string_append(v___x_952_, v___x_954_);
lean_dec_ref(v___x_954_);
v___x_956_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
v___x_958_ = l_Lake_zpad(v_minute_945_, v___x_953_);
v___x_959_ = lean_string_append(v___x_957_, v___x_958_);
lean_dec_ref(v___x_958_);
return v___x_959_;
}
else
{
lean_object* v_snd_960_; lean_object* v_date_961_; lean_object* v_time_962_; lean_object* v_hour_963_; lean_object* v_minute_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_snd_960_ = lean_ctor_get(v_val_938_, 1);
lean_inc(v_snd_960_);
v_date_961_ = lean_ctor_get(v_dt_936_, 0);
lean_inc_ref(v_date_961_);
v_time_962_ = lean_ctor_get(v_dt_936_, 1);
lean_inc_ref(v_time_962_);
lean_dec_ref(v_dt_936_);
v_hour_963_ = lean_ctor_get(v_snd_960_, 0);
lean_inc(v_hour_963_);
v_minute_964_ = lean_ctor_get(v_snd_960_, 1);
lean_inc(v_minute_964_);
lean_dec(v_snd_960_);
v___x_965_ = l_Lake_Date_toString(v_date_961_);
v___x_966_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_967_ = lean_string_append(v___x_965_, v___x_966_);
v___x_968_ = l_Lake_Toml_Time_toString(v_time_962_);
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
lean_dec_ref(v___x_968_);
v___x_970_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__2));
v___x_971_ = lean_string_append(v___x_969_, v___x_970_);
v___x_972_ = lean_unsigned_to_nat(2u);
v___x_973_ = l_Lake_zpad(v_hour_963_, v___x_972_);
v___x_974_ = lean_string_append(v___x_971_, v___x_973_);
lean_dec_ref(v___x_973_);
v___x_975_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_976_ = lean_string_append(v___x_974_, v___x_975_);
v___x_977_ = l_Lake_zpad(v_minute_964_, v___x_972_);
v___x_978_ = lean_string_append(v___x_976_, v___x_977_);
lean_dec_ref(v___x_977_);
return v___x_978_;
}
}
else
{
lean_object* v_date_979_; lean_object* v_time_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v_date_979_ = lean_ctor_get(v_dt_936_, 0);
lean_inc_ref(v_date_979_);
v_time_980_ = lean_ctor_get(v_dt_936_, 1);
lean_inc_ref(v_time_980_);
lean_dec_ref(v_dt_936_);
v___x_981_ = l_Lake_Date_toString(v_date_979_);
v___x_982_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
v___x_984_ = l_Lake_Toml_Time_toString(v_time_980_);
v___x_985_ = lean_string_append(v___x_983_, v___x_984_);
lean_dec_ref(v___x_984_);
v___x_986_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__3));
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
return v___x_987_;
}
}
case 1:
{
lean_object* v_date_988_; lean_object* v_time_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_date_988_ = lean_ctor_get(v_dt_936_, 0);
lean_inc_ref(v_date_988_);
v_time_989_ = lean_ctor_get(v_dt_936_, 1);
lean_inc_ref(v_time_989_);
lean_dec_ref(v_dt_936_);
v___x_990_ = l_Lake_Date_toString(v_date_988_);
v___x_991_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_992_ = lean_string_append(v___x_990_, v___x_991_);
v___x_993_ = l_Lake_Toml_Time_toString(v_time_989_);
v___x_994_ = lean_string_append(v___x_992_, v___x_993_);
lean_dec_ref(v___x_993_);
return v___x_994_;
}
case 2:
{
lean_object* v_date_995_; lean_object* v___x_996_; 
v_date_995_ = lean_ctor_get(v_dt_936_, 0);
lean_inc_ref(v_date_995_);
lean_dec_ref(v_dt_936_);
v___x_996_ = l_Lake_Date_toString(v_date_995_);
return v___x_996_;
}
default: 
{
lean_object* v_time_997_; lean_object* v___x_998_; 
v_time_997_ = lean_ctor_get(v_dt_936_, 0);
lean_inc_ref(v_time_997_);
lean_dec_ref(v_dt_936_);
v___x_998_ = l_Lake_Toml_Time_toString(v_time_997_);
return v___x_998_;
}
}
}
}
lean_object* runtime_initialize_Lake_Util_Date(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Data_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Util_Date(builtin);
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
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Toml_instInhabitedDateTime_default = _init_l_Lake_Toml_instInhabitedDateTime_default();
lean_mark_persistent(l_Lake_Toml_instInhabitedDateTime_default);
l_Lake_Toml_instInhabitedDateTime = _init_l_Lake_Toml_instInhabitedDateTime();
lean_mark_persistent(l_Lake_Toml_instInhabitedDateTime);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Data_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Date(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Data_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Date(builtin);
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
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Data_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Data_DateTime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Data_DateTime(builtin);
}
#ifdef __cplusplus
}
#endif

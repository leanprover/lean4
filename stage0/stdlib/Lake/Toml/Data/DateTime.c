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
lean_object* l_Lake_rpadAscii(lean_object*, uint32_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* l_Lake_Date_toString(lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_39_; lean_object* v___x_44_; uint8_t v___x_45_; uint8_t v___y_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_44_ = lean_unsigned_to_nat(23u);
v___x_45_ = lean_nat_dec_le(v_hour_35_, v___x_44_);
v___x_48_ = lean_unsigned_to_nat(59u);
v___x_49_ = lean_nat_dec_le(v_minute_36_, v___x_48_);
if (v___x_49_ == 0)
{
v___y_47_ = v___x_49_;
goto v___jp_46_;
}
else
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(60u);
v___x_51_ = lean_nat_dec_le(v_second_37_, v___x_50_);
v___y_47_ = v___x_51_;
goto v___jp_46_;
}
v___jp_38_:
{
if (v___y_39_ == 0)
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
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_42_, 0, v_hour_35_);
lean_ctor_set(v___x_42_, 1, v_minute_36_);
lean_ctor_set(v___x_42_, 2, v_second_37_);
lean_ctor_set(v___x_42_, 3, v___x_41_);
lean_ctor_set(v___x_42_, 4, v___x_41_);
v___x_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
return v___x_43_;
}
}
v___jp_46_:
{
if (v___x_45_ == 0)
{
v___y_39_ = v___x_45_;
goto v___jp_38_;
}
else
{
v___y_39_ = v___y_47_;
goto v___jp_38_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(lean_object* v_s_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0));
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___boxed(lean_object* v_s_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(v_s_56_);
lean_dec_ref(v_s_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(lean_object* v_s_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0));
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___boxed(lean_object* v_s_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(v_s_60_);
lean_dec_ref(v_s_60_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(lean_object* v_head_62_, lean_object* v_a_63_, lean_object* v_b_64_){
_start:
{
if (lean_obj_tag(v_a_63_) == 0)
{
lean_object* v_currPos_65_; lean_object* v_searcher_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_104_; 
v_currPos_65_ = lean_ctor_get(v_a_63_, 0);
v_searcher_66_ = lean_ctor_get(v_a_63_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v_a_63_);
if (v_isSharedCheck_104_ == 0)
{
v___x_68_ = v_a_63_;
v_isShared_69_ = v_isSharedCheck_104_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_searcher_66_);
lean_inc(v_currPos_65_);
lean_dec(v_a_63_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_104_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v_str_70_; lean_object* v_startInclusive_71_; lean_object* v_endExclusive_72_; lean_object* v_it_74_; lean_object* v_startInclusive_75_; lean_object* v_endExclusive_76_; lean_object* v___x_82_; uint8_t v_decide_83_; 
v_str_70_ = lean_ctor_get(v_head_62_, 0);
v_startInclusive_71_ = lean_ctor_get(v_head_62_, 1);
v_endExclusive_72_ = lean_ctor_get(v_head_62_, 2);
v___x_82_ = lean_nat_sub(v_endExclusive_72_, v_startInclusive_71_);
v_decide_83_ = lean_nat_dec_eq(v_searcher_66_, v___x_82_);
if (v_decide_83_ == 0)
{
uint32_t v___x_84_; lean_object* v___x_85_; uint32_t v___x_86_; uint8_t v___x_87_; 
lean_dec(v___x_82_);
v___x_84_ = 46;
v___x_85_ = lean_nat_add(v_startInclusive_71_, v_searcher_66_);
v___x_86_ = lean_string_utf8_get_fast(v_str_70_, v___x_85_);
v___x_87_ = lean_uint32_dec_eq(v___x_86_, v___x_84_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
lean_dec(v_searcher_66_);
v___x_88_ = lean_string_utf8_next_fast(v_str_70_, v___x_85_);
lean_dec(v___x_85_);
v___x_89_ = lean_nat_sub(v___x_88_, v_startInclusive_71_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v___x_89_);
v___x_91_ = v___x_68_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_currPos_65_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_93_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
v_a_63_ = v___x_91_;
goto _start;
}
}
else
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v_slice_97_; lean_object* v_nextIt_99_; 
v___x_94_ = lean_string_utf8_next_fast(v_str_70_, v___x_85_);
v___x_95_ = lean_nat_sub(v___x_94_, v___x_85_);
lean_dec(v___x_85_);
v___x_96_ = lean_nat_add(v_searcher_66_, v___x_95_);
lean_dec(v___x_95_);
v_slice_97_ = l_String_Slice_subslice_x21(v_head_62_, v_currPos_65_, v_searcher_66_);
lean_inc(v___x_96_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 1, v___x_96_);
lean_ctor_set(v___x_68_, 0, v___x_96_);
v_nextIt_99_ = v___x_68_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_96_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___x_96_);
v_nextIt_99_ = v_reuseFailAlloc_102_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v_startInclusive_100_; lean_object* v_endExclusive_101_; 
v_startInclusive_100_ = lean_ctor_get(v_slice_97_, 0);
lean_inc(v_startInclusive_100_);
v_endExclusive_101_ = lean_ctor_get(v_slice_97_, 1);
lean_inc(v_endExclusive_101_);
lean_dec_ref(v_slice_97_);
v_it_74_ = v_nextIt_99_;
v_startInclusive_75_ = v_startInclusive_100_;
v_endExclusive_76_ = v_endExclusive_101_;
goto v___jp_73_;
}
}
}
else
{
lean_object* v___x_103_; 
lean_del_object(v___x_68_);
lean_dec(v_searcher_66_);
v___x_103_ = lean_box(1);
v_it_74_ = v___x_103_;
v_startInclusive_75_ = v_currPos_65_;
v_endExclusive_76_ = v___x_82_;
goto v___jp_73_;
}
v___jp_73_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = lean_nat_add(v_startInclusive_71_, v_startInclusive_75_);
lean_dec(v_startInclusive_75_);
v___x_78_ = lean_nat_add(v_startInclusive_71_, v_endExclusive_76_);
lean_dec(v_endExclusive_76_);
lean_inc_ref(v_str_70_);
v___x_79_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_79_, 0, v_str_70_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_78_);
v___x_80_ = lean_array_push(v_b_64_, v___x_79_);
v_a_63_ = v_it_74_;
v_b_64_ = v___x_80_;
goto _start;
}
}
}
else
{
return v_b_64_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg___boxed(lean_object* v_head_105_, lean_object* v_a_106_, lean_object* v_b_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_105_, v_a_106_, v_b_107_);
lean_dec_ref(v_head_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(lean_object* v_t_109_, lean_object* v___x_110_, lean_object* v___x_111_, lean_object* v_a_112_, lean_object* v_b_113_){
_start:
{
lean_object* v_it_115_; lean_object* v_startInclusive_116_; lean_object* v_endExclusive_117_; 
if (lean_obj_tag(v_a_112_) == 0)
{
lean_object* v_currPos_121_; lean_object* v_searcher_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_145_; 
v_currPos_121_ = lean_ctor_get(v_a_112_, 0);
v_searcher_122_ = lean_ctor_get(v_a_112_, 1);
v_isSharedCheck_145_ = !lean_is_exclusive(v_a_112_);
if (v_isSharedCheck_145_ == 0)
{
v___x_124_ = v_a_112_;
v_isShared_125_ = v_isSharedCheck_145_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_searcher_122_);
lean_inc(v_currPos_121_);
lean_dec(v_a_112_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_145_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
uint8_t v_decide_126_; 
v_decide_126_ = lean_nat_dec_eq(v_searcher_122_, v___x_111_);
if (v_decide_126_ == 0)
{
uint32_t v___x_127_; uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_127_ = 58;
v___x_128_ = lean_string_utf8_get_fast(v_t_109_, v_searcher_122_);
v___x_129_ = lean_uint32_dec_eq(v___x_128_, v___x_127_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = lean_string_utf8_next_fast(v_t_109_, v_searcher_122_);
lean_dec(v_searcher_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_130_);
v___x_132_ = v___x_124_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_currPos_121_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_130_);
v___x_132_ = v_reuseFailAlloc_134_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
v_a_112_ = v___x_132_;
goto _start;
}
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_slice_138_; lean_object* v_nextIt_140_; 
v___x_135_ = lean_string_utf8_next_fast(v_t_109_, v_searcher_122_);
v___x_136_ = lean_nat_sub(v___x_135_, v_searcher_122_);
v___x_137_ = lean_nat_add(v_searcher_122_, v___x_136_);
lean_dec(v___x_136_);
v_slice_138_ = l_String_Slice_subslice_x21(v___x_110_, v_currPos_121_, v_searcher_122_);
lean_inc(v___x_137_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_137_);
lean_ctor_set(v___x_124_, 0, v___x_137_);
v_nextIt_140_ = v___x_124_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_137_);
v_nextIt_140_ = v_reuseFailAlloc_143_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v_startInclusive_141_; lean_object* v_endExclusive_142_; 
v_startInclusive_141_ = lean_ctor_get(v_slice_138_, 0);
lean_inc(v_startInclusive_141_);
v_endExclusive_142_ = lean_ctor_get(v_slice_138_, 1);
lean_inc(v_endExclusive_142_);
lean_dec_ref(v_slice_138_);
v_it_115_ = v_nextIt_140_;
v_startInclusive_116_ = v_startInclusive_141_;
v_endExclusive_117_ = v_endExclusive_142_;
goto v___jp_114_;
}
}
}
else
{
lean_object* v___x_144_; 
lean_del_object(v___x_124_);
lean_dec(v_searcher_122_);
v___x_144_ = lean_box(1);
lean_inc(v___x_111_);
v_it_115_ = v___x_144_;
v_startInclusive_116_ = v_currPos_121_;
v_endExclusive_117_ = v___x_111_;
goto v___jp_114_;
}
}
}
else
{
lean_dec(v___x_111_);
lean_dec_ref(v_t_109_);
return v_b_113_;
}
v___jp_114_:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_inc_ref(v_t_109_);
v___x_118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_118_, 0, v_t_109_);
lean_ctor_set(v___x_118_, 1, v_startInclusive_116_);
lean_ctor_set(v___x_118_, 2, v_endExclusive_117_);
v___x_119_ = lean_array_push(v_b_113_, v___x_118_);
v_a_112_ = v_it_115_;
v_b_113_ = v___x_119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg___boxed(lean_object* v_t_146_, lean_object* v___x_147_, lean_object* v___x_148_, lean_object* v_a_149_, lean_object* v_b_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_146_, v___x_147_, v___x_148_, v_a_149_, v_b_150_);
lean_dec_ref(v___x_147_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(lean_object* v_head_152_, lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
lean_object* v_str_155_; lean_object* v_startInclusive_156_; lean_object* v_endExclusive_157_; lean_object* v___x_158_; uint8_t v_decide_159_; 
v_str_155_ = lean_ctor_get(v_head_152_, 0);
v_startInclusive_156_ = lean_ctor_get(v_head_152_, 1);
v_endExclusive_157_ = lean_ctor_get(v_head_152_, 2);
v___x_158_ = lean_nat_sub(v_endExclusive_157_, v_startInclusive_156_);
v_decide_159_ = lean_nat_dec_eq(v_a_153_, v___x_158_);
lean_dec(v___x_158_);
if (v_decide_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_160_ = lean_nat_add(v_startInclusive_156_, v_a_153_);
lean_dec(v_a_153_);
v___x_161_ = lean_string_utf8_next_fast(v_str_155_, v___x_160_);
lean_dec(v___x_160_);
v___x_162_ = lean_nat_sub(v___x_161_, v_startInclusive_156_);
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_add(v_b_154_, v___x_163_);
lean_dec(v_b_154_);
v_a_153_ = v___x_162_;
v_b_154_ = v___x_164_;
goto _start;
}
else
{
lean_dec(v_a_153_);
return v_b_154_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg___boxed(lean_object* v_head_166_, lean_object* v_a_167_, lean_object* v_b_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_166_, v_a_167_, v_b_168_);
lean_dec_ref(v_head_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_ofString_x3f(lean_object* v_t_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_string_utf8_byte_size(v_t_172_);
lean_inc_ref(v_t_172_);
v___x_175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_175_, 0, v_t_172_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___x_174_);
v___x_176_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(v___x_175_);
v___x_177_ = ((lean_object*)(l_Lake_Toml_Time_ofString_x3f___closed__0));
v___x_178_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_172_, v___x_175_, v___x_174_, v___x_176_, v___x_177_);
lean_dec_ref_known(v___x_175_, 3);
v___x_179_ = lean_array_to_list(v___x_178_);
if (lean_obj_tag(v___x_179_) == 1)
{
lean_object* v_tail_180_; 
v_tail_180_ = lean_ctor_get(v___x_179_, 1);
lean_inc(v_tail_180_);
if (lean_obj_tag(v_tail_180_) == 1)
{
lean_object* v_tail_181_; 
v_tail_181_ = lean_ctor_get(v_tail_180_, 1);
if (lean_obj_tag(v_tail_181_) == 0)
{
lean_object* v_head_182_; lean_object* v_head_183_; lean_object* v___x_184_; 
v_head_182_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_head_182_);
lean_dec_ref_known(v___x_179_, 2);
v_head_183_ = lean_ctor_get(v_tail_180_, 0);
lean_inc(v_head_183_);
lean_dec_ref_known(v_tail_180_, 2);
v___x_184_ = l_String_Slice_toNat_x3f(v_head_182_);
lean_dec(v_head_182_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v___x_185_; 
lean_dec(v_head_183_);
v___x_185_ = lean_box(0);
return v___x_185_;
}
else
{
lean_object* v_val_186_; lean_object* v___x_187_; 
v_val_186_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_val_186_);
lean_dec_ref_known(v___x_184_, 1);
v___x_187_ = l_String_Slice_toNat_x3f(v_head_183_);
lean_dec(v_head_183_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v___x_188_; 
lean_dec(v_val_186_);
v___x_188_ = lean_box(0);
return v___x_188_;
}
else
{
lean_object* v_val_189_; lean_object* v___x_190_; 
v_val_189_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_val_189_);
lean_dec_ref_known(v___x_187_, 1);
v___x_190_ = l_Lake_Toml_Time_ofValid_x3f(v_val_186_, v_val_189_, v___x_173_);
return v___x_190_;
}
}
}
else
{
lean_object* v_tail_191_; 
lean_inc_ref(v_tail_181_);
v_tail_191_ = lean_ctor_get(v_tail_181_, 1);
if (lean_obj_tag(v_tail_191_) == 0)
{
lean_object* v_head_192_; lean_object* v_head_193_; lean_object* v_head_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_head_192_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_head_192_);
lean_dec_ref_known(v___x_179_, 2);
v_head_193_ = lean_ctor_get(v_tail_180_, 0);
lean_inc(v_head_193_);
lean_dec_ref_known(v_tail_180_, 2);
v_head_194_ = lean_ctor_get(v_tail_181_, 0);
lean_inc(v_head_194_);
lean_dec_ref_known(v_tail_181_, 2);
v___x_195_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(v_head_194_);
v___x_196_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_194_, v___x_195_, v___x_177_);
lean_dec(v_head_194_);
v___x_197_ = lean_array_to_list(v___x_196_);
if (lean_obj_tag(v___x_197_) == 1)
{
lean_object* v_tail_198_; 
v_tail_198_ = lean_ctor_get(v___x_197_, 1);
lean_inc(v_tail_198_);
if (lean_obj_tag(v_tail_198_) == 0)
{
lean_object* v_head_199_; lean_object* v___x_200_; 
v_head_199_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_head_199_);
lean_dec_ref_known(v___x_197_, 2);
v___x_200_ = l_String_Slice_toNat_x3f(v_head_192_);
lean_dec(v_head_192_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; 
lean_dec(v_head_199_);
lean_dec(v_head_193_);
v___x_201_ = lean_box(0);
return v___x_201_;
}
else
{
lean_object* v_val_202_; lean_object* v___x_203_; 
v_val_202_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___x_200_, 1);
v___x_203_ = l_String_Slice_toNat_x3f(v_head_193_);
lean_dec(v_head_193_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v___x_204_; 
lean_dec(v_val_202_);
lean_dec(v_head_199_);
v___x_204_ = lean_box(0);
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_206_; 
v_val_205_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_val_205_);
lean_dec_ref_known(v___x_203_, 1);
v___x_206_ = l_String_Slice_toNat_x3f(v_head_199_);
lean_dec(v_head_199_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v___x_207_; 
lean_dec(v_val_205_);
lean_dec(v_val_202_);
v___x_207_ = lean_box(0);
return v___x_207_;
}
else
{
lean_object* v_val_208_; lean_object* v___x_209_; 
v_val_208_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_val_208_);
lean_dec_ref_known(v___x_206_, 1);
v___x_209_ = l_Lake_Toml_Time_ofValid_x3f(v_val_202_, v_val_205_, v_val_208_);
return v___x_209_;
}
}
}
}
else
{
lean_object* v_tail_210_; 
v_tail_210_ = lean_ctor_get(v_tail_198_, 1);
if (lean_obj_tag(v_tail_210_) == 0)
{
lean_object* v_head_211_; lean_object* v_head_212_; lean_object* v___x_213_; 
v_head_211_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_head_211_);
lean_dec_ref_known(v___x_197_, 2);
v_head_212_ = lean_ctor_get(v_tail_198_, 0);
lean_inc(v_head_212_);
lean_dec_ref_known(v_tail_198_, 2);
v___x_213_ = l_String_Slice_toNat_x3f(v_head_192_);
lean_dec(v_head_192_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_214_; 
lean_dec(v_head_212_);
lean_dec(v_head_211_);
lean_dec(v_head_193_);
v___x_214_ = lean_box(0);
return v___x_214_;
}
else
{
lean_object* v_val_215_; lean_object* v___x_216_; 
v_val_215_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_val_215_);
lean_dec_ref_known(v___x_213_, 1);
v___x_216_ = l_String_Slice_toNat_x3f(v_head_193_);
lean_dec(v_head_193_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v___x_217_; 
lean_dec(v_val_215_);
lean_dec(v_head_212_);
lean_dec(v_head_211_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v_val_218_; lean_object* v___x_219_; 
v_val_218_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v___x_216_, 1);
v___x_219_ = l_String_Slice_toNat_x3f(v_head_211_);
lean_dec(v_head_211_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v___x_220_; 
lean_dec(v_val_218_);
lean_dec(v_val_215_);
lean_dec(v_head_212_);
v___x_220_ = lean_box(0);
return v___x_220_;
}
else
{
lean_object* v_val_221_; lean_object* v___x_222_; 
v_val_221_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_val_221_);
lean_dec_ref_known(v___x_219_, 1);
v___x_222_ = l_Lake_Toml_Time_ofValid_x3f(v_val_215_, v_val_218_, v_val_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_dec(v_head_212_);
return v___x_222_;
}
else
{
lean_object* v_val_223_; lean_object* v___x_224_; 
v_val_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_222_, 1);
v___x_224_ = l_String_Slice_toNat_x3f(v_head_212_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v___x_225_; 
lean_dec(v_val_223_);
lean_dec(v_head_212_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
else
{
lean_object* v_val_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_249_; 
v_val_226_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_249_ == 0)
{
v___x_228_ = v___x_224_;
v_isShared_229_ = v_isSharedCheck_249_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_val_226_);
lean_dec(v___x_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_249_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v_hour_230_; lean_object* v_minute_231_; lean_object* v_second_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_246_; 
v_hour_230_ = lean_ctor_get(v_val_223_, 0);
v_minute_231_ = lean_ctor_get(v_val_223_, 1);
v_second_232_ = lean_ctor_get(v_val_223_, 2);
v_isSharedCheck_246_ = !lean_is_exclusive(v_val_223_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; lean_object* v_unused_248_; 
v_unused_247_ = lean_ctor_get(v_val_223_, 4);
lean_dec(v_unused_247_);
v_unused_248_ = lean_ctor_get(v_val_223_, 3);
lean_dec(v_unused_248_);
v___x_234_ = v_val_223_;
v_isShared_235_ = v_isSharedCheck_246_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_second_232_);
lean_inc(v_minute_231_);
lean_inc(v_hour_230_);
lean_dec(v_val_223_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_246_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_236_ = l_String_Slice_positions(v_head_212_);
v___x_237_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_212_, v___x_236_, v___x_173_);
lean_dec(v_head_212_);
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_nat_sub(v___x_237_, v___x_238_);
lean_dec(v___x_237_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 4, v_val_226_);
lean_ctor_set(v___x_234_, 3, v___x_239_);
v___x_241_ = v___x_234_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_hour_230_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_minute_231_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_second_232_);
lean_ctor_set(v_reuseFailAlloc_245_, 3, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_245_, 4, v_val_226_);
v___x_241_ = v_reuseFailAlloc_245_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_241_);
v___x_243_ = v___x_228_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
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
lean_object* v___x_250_; 
lean_dec_ref_known(v_tail_198_, 2);
lean_dec_ref_known(v___x_197_, 2);
lean_dec(v_head_193_);
lean_dec(v_head_192_);
v___x_250_ = lean_box(0);
return v___x_250_;
}
}
}
else
{
lean_object* v___x_251_; 
lean_dec(v___x_197_);
lean_dec(v_head_193_);
lean_dec(v_head_192_);
v___x_251_ = lean_box(0);
return v___x_251_;
}
}
else
{
lean_object* v___x_252_; 
lean_dec_ref_known(v_tail_181_, 2);
lean_dec_ref_known(v_tail_180_, 2);
lean_dec_ref_known(v___x_179_, 2);
v___x_252_ = lean_box(0);
return v___x_252_;
}
}
}
else
{
lean_object* v___x_253_; 
lean_dec_ref_known(v___x_179_, 2);
lean_dec(v_tail_180_);
v___x_253_ = lean_box(0);
return v___x_253_;
}
}
else
{
lean_object* v___x_254_; 
lean_dec(v___x_179_);
v___x_254_ = lean_box(0);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(lean_object* v_t_255_, lean_object* v___x_256_, lean_object* v___x_257_, lean_object* v_inst_258_, lean_object* v_R_259_, lean_object* v_a_260_, lean_object* v_b_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_255_, v___x_256_, v___x_257_, v_a_260_, v_b_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___boxed(lean_object* v_t_263_, lean_object* v___x_264_, lean_object* v___x_265_, lean_object* v_inst_266_, lean_object* v_R_267_, lean_object* v_a_268_, lean_object* v_b_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(v_t_263_, v___x_264_, v___x_265_, v_inst_266_, v_R_267_, v_a_268_, v_b_269_);
lean_dec_ref(v___x_264_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(lean_object* v_head_271_, lean_object* v_inst_272_, lean_object* v_R_273_, lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_271_, v_a_274_, v_b_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___boxed(lean_object* v_head_277_, lean_object* v_inst_278_, lean_object* v_R_279_, lean_object* v_a_280_, lean_object* v_b_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(v_head_277_, v_inst_278_, v_R_279_, v_a_280_, v_b_281_);
lean_dec_ref(v_head_277_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(lean_object* v_head_283_, lean_object* v_inst_284_, lean_object* v_R_285_, lean_object* v_a_286_, lean_object* v_b_287_, lean_object* v_c_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_283_, v_a_286_, v_b_287_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___boxed(lean_object* v_head_290_, lean_object* v_inst_291_, lean_object* v_R_292_, lean_object* v_a_293_, lean_object* v_b_294_, lean_object* v_c_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(v_head_290_, v_inst_291_, v_R_292_, v_a_293_, v_b_294_, v_c_295_);
lean_dec_ref(v_head_290_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_toString(lean_object* v_t_299_){
_start:
{
lean_object* v_hour_300_; lean_object* v_minute_301_; lean_object* v_second_302_; lean_object* v_fracExponent_303_; lean_object* v_fracMantissa_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_s_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v_hour_300_ = lean_ctor_get(v_t_299_, 0);
lean_inc(v_hour_300_);
v_minute_301_ = lean_ctor_get(v_t_299_, 1);
lean_inc(v_minute_301_);
v_second_302_ = lean_ctor_get(v_t_299_, 2);
lean_inc(v_second_302_);
v_fracExponent_303_ = lean_ctor_get(v_t_299_, 3);
lean_inc(v_fracExponent_303_);
v_fracMantissa_304_ = lean_ctor_get(v_t_299_, 4);
lean_inc(v_fracMantissa_304_);
lean_dec_ref(v_t_299_);
v___x_305_ = lean_unsigned_to_nat(2u);
v___x_306_ = l_Lake_zpad(v_hour_300_, v___x_305_);
v___x_307_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_308_ = lean_string_append(v___x_306_, v___x_307_);
v___x_309_ = l_Lake_zpad(v_minute_301_, v___x_305_);
v___x_310_ = lean_string_append(v___x_308_, v___x_309_);
lean_dec_ref(v___x_309_);
v___x_311_ = lean_string_append(v___x_310_, v___x_307_);
v___x_312_ = l_Lake_zpad(v_second_302_, v___x_305_);
v_s_313_ = lean_string_append(v___x_311_, v___x_312_);
lean_dec_ref(v___x_312_);
v___x_314_ = lean_unsigned_to_nat(0u);
v___x_315_ = lean_nat_dec_eq(v_fracMantissa_304_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint32_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_316_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__1));
v___x_317_ = lean_string_append(v_s_313_, v___x_316_);
v___x_318_ = l_Lake_zpad(v_fracMantissa_304_, v_fracExponent_303_);
lean_dec(v_fracExponent_303_);
v___x_319_ = 48;
v___x_320_ = lean_unsigned_to_nat(3u);
v___x_321_ = l_Lake_rpadAscii(v___x_318_, v___x_319_, v___x_320_);
v___x_322_ = lean_string_append(v___x_317_, v___x_321_);
lean_dec_ref(v___x_321_);
return v___x_322_;
}
else
{
lean_dec(v_fracMantissa_304_);
lean_dec(v_fracExponent_303_);
return v_s_313_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx(lean_object* v_x_325_){
_start:
{
switch(lean_obj_tag(v_x_325_))
{
case 0:
{
lean_object* v___x_326_; 
v___x_326_ = lean_unsigned_to_nat(0u);
return v___x_326_;
}
case 1:
{
lean_object* v___x_327_; 
v___x_327_ = lean_unsigned_to_nat(1u);
return v___x_327_;
}
case 2:
{
lean_object* v___x_328_; 
v___x_328_ = lean_unsigned_to_nat(2u);
return v___x_328_;
}
default: 
{
lean_object* v___x_329_; 
v___x_329_ = lean_unsigned_to_nat(3u);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx___boxed(lean_object* v_x_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lake_Toml_DateTime_ctorIdx(v_x_330_);
lean_dec_ref(v_x_330_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___redArg(lean_object* v_t_332_, lean_object* v_k_333_){
_start:
{
switch(lean_obj_tag(v_t_332_))
{
case 0:
{
lean_object* v_date_334_; lean_object* v_time_335_; lean_object* v_offset_x3f_336_; lean_object* v___x_337_; 
v_date_334_ = lean_ctor_get(v_t_332_, 0);
lean_inc_ref(v_date_334_);
v_time_335_ = lean_ctor_get(v_t_332_, 1);
lean_inc_ref(v_time_335_);
v_offset_x3f_336_ = lean_ctor_get(v_t_332_, 2);
lean_inc(v_offset_x3f_336_);
lean_dec_ref_known(v_t_332_, 3);
v___x_337_ = lean_apply_3(v_k_333_, v_date_334_, v_time_335_, v_offset_x3f_336_);
return v___x_337_;
}
case 1:
{
lean_object* v_date_338_; lean_object* v_time_339_; lean_object* v___x_340_; 
v_date_338_ = lean_ctor_get(v_t_332_, 0);
lean_inc_ref(v_date_338_);
v_time_339_ = lean_ctor_get(v_t_332_, 1);
lean_inc_ref(v_time_339_);
lean_dec_ref_known(v_t_332_, 2);
v___x_340_ = lean_apply_2(v_k_333_, v_date_338_, v_time_339_);
return v___x_340_;
}
default: 
{
lean_object* v_date_341_; lean_object* v___x_342_; 
v_date_341_ = lean_ctor_get(v_t_332_, 0);
lean_inc_ref(v_date_341_);
lean_dec_ref(v_t_332_);
v___x_342_ = lean_apply_1(v_k_333_, v_date_341_);
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim(lean_object* v_motive_343_, lean_object* v_ctorIdx_344_, lean_object* v_t_345_, lean_object* v_h_346_, lean_object* v_k_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_345_, v_k_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___boxed(lean_object* v_motive_349_, lean_object* v_ctorIdx_350_, lean_object* v_t_351_, lean_object* v_h_352_, lean_object* v_k_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lake_Toml_DateTime_ctorElim(v_motive_349_, v_ctorIdx_350_, v_t_351_, v_h_352_, v_k_353_);
lean_dec(v_ctorIdx_350_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim___redArg(lean_object* v_t_355_, lean_object* v_offsetDateTime_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_355_, v_offsetDateTime_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim(lean_object* v_motive_358_, lean_object* v_t_359_, lean_object* v_h_360_, lean_object* v_offsetDateTime_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_359_, v_offsetDateTime_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim___redArg(lean_object* v_t_363_, lean_object* v_localDateTime_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_363_, v_localDateTime_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim(lean_object* v_motive_366_, lean_object* v_t_367_, lean_object* v_h_368_, lean_object* v_localDateTime_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_367_, v_localDateTime_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim___redArg(lean_object* v_t_371_, lean_object* v_localDate_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_371_, v_localDate_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim(lean_object* v_motive_374_, lean_object* v_t_375_, lean_object* v_h_376_, lean_object* v_localDate_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_375_, v_localDate_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim___redArg(lean_object* v_t_379_, lean_object* v_localTime_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_379_, v_localTime_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim(lean_object* v_motive_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_localTime_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_383_, v_localTime_385_);
return v___x_386_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_387_ = lean_box(0);
v___x_388_ = ((lean_object*)(l_Lake_Toml_instInhabitedTime_default));
v___x_389_ = l_Lake_instInhabitedDate_default;
v___x_390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
lean_ctor_set(v___x_390_, 2, v___x_387_);
return v___x_390_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime_default(void){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_once(&l_Lake_Toml_instInhabitedDateTime_default___closed__0, &l_Lake_Toml_instInhabitedDateTime_default___closed__0_once, _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0);
return v___x_391_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime(void){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lake_Toml_instInhabitedDateTime_default;
return v___x_392_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(uint8_t v___x_393_, uint8_t v___y_394_, uint8_t v___y_395_){
_start:
{
if (v___y_395_ == 0)
{
if (v___y_394_ == 0)
{
return v___x_393_;
}
else
{
return v___y_395_;
}
}
else
{
return v___y_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed(lean_object* v___x_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
uint8_t v___x_874__boxed_399_; uint8_t v___y_875__boxed_400_; uint8_t v___y_876__boxed_401_; uint8_t v_res_402_; lean_object* v_r_403_; 
v___x_874__boxed_399_ = lean_unbox(v___x_396_);
v___y_875__boxed_400_ = lean_unbox(v___y_397_);
v___y_876__boxed_401_ = lean_unbox(v___y_398_);
v_res_402_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(v___x_874__boxed_399_, v___y_875__boxed_400_, v___y_876__boxed_401_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(lean_object* v___f_404_, lean_object* v_a_405_, lean_object* v_b_406_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqTime___boxed), 2, 0);
v___x_408_ = l_instDecidableEqProd___redArg(v___f_404_, v___x_407_, v_a_405_, v_b_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed(lean_object* v___f_409_, lean_object* v_a_410_, lean_object* v_b_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(v___f_409_, v_a_410_, v_b_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq(lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
switch(lean_obj_tag(v_x_414_))
{
case 0:
{
if (lean_obj_tag(v_x_415_) == 0)
{
lean_object* v_date_416_; lean_object* v_time_417_; lean_object* v_offset_x3f_418_; lean_object* v_date_419_; lean_object* v_time_420_; lean_object* v_offset_x3f_421_; uint8_t v___x_422_; 
v_date_416_ = lean_ctor_get(v_x_414_, 0);
lean_inc_ref(v_date_416_);
v_time_417_ = lean_ctor_get(v_x_414_, 1);
lean_inc_ref(v_time_417_);
v_offset_x3f_418_ = lean_ctor_get(v_x_414_, 2);
lean_inc(v_offset_x3f_418_);
lean_dec_ref_known(v_x_414_, 3);
v_date_419_ = lean_ctor_get(v_x_415_, 0);
lean_inc_ref(v_date_419_);
v_time_420_ = lean_ctor_get(v_x_415_, 1);
lean_inc_ref(v_time_420_);
v_offset_x3f_421_ = lean_ctor_get(v_x_415_, 2);
lean_inc(v_offset_x3f_421_);
lean_dec_ref_known(v_x_415_, 3);
v___x_422_ = l_Lake_instDecidableEqDate_decEq(v_date_416_, v_date_419_);
lean_dec_ref(v_date_419_);
lean_dec_ref(v_date_416_);
if (v___x_422_ == 0)
{
lean_dec(v_offset_x3f_421_);
lean_dec_ref(v_time_420_);
lean_dec(v_offset_x3f_418_);
lean_dec_ref(v_time_417_);
return v___x_422_;
}
else
{
uint8_t v___x_423_; 
v___x_423_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_417_, v_time_420_);
lean_dec_ref(v_time_420_);
lean_dec_ref(v_time_417_);
if (v___x_423_ == 0)
{
lean_dec(v_offset_x3f_421_);
lean_dec(v_offset_x3f_418_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___f_425_; lean_object* v___f_426_; uint8_t v___x_427_; 
v___x_424_ = lean_box(v___x_423_);
v___f_425_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed), 3, 1);
lean_closure_set(v___f_425_, 0, v___x_424_);
v___f_426_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed), 3, 1);
lean_closure_set(v___f_426_, 0, v___f_425_);
v___x_427_ = l_Option_instDecidableEq___redArg(v___f_426_, v_offset_x3f_418_, v_offset_x3f_421_);
return v___x_427_;
}
}
}
else
{
uint8_t v___x_428_; 
lean_dec_ref_known(v_x_414_, 3);
lean_dec_ref(v_x_415_);
v___x_428_ = 0;
return v___x_428_;
}
}
case 1:
{
if (lean_obj_tag(v_x_415_) == 1)
{
lean_object* v_date_429_; lean_object* v_time_430_; lean_object* v_date_431_; lean_object* v_time_432_; uint8_t v___x_433_; 
v_date_429_ = lean_ctor_get(v_x_414_, 0);
lean_inc_ref(v_date_429_);
v_time_430_ = lean_ctor_get(v_x_414_, 1);
lean_inc_ref(v_time_430_);
lean_dec_ref_known(v_x_414_, 2);
v_date_431_ = lean_ctor_get(v_x_415_, 0);
lean_inc_ref(v_date_431_);
v_time_432_ = lean_ctor_get(v_x_415_, 1);
lean_inc_ref(v_time_432_);
lean_dec_ref_known(v_x_415_, 2);
v___x_433_ = l_Lake_instDecidableEqDate_decEq(v_date_429_, v_date_431_);
lean_dec_ref(v_date_431_);
lean_dec_ref(v_date_429_);
if (v___x_433_ == 0)
{
lean_dec_ref(v_time_432_);
lean_dec_ref(v_time_430_);
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_430_, v_time_432_);
lean_dec_ref(v_time_432_);
lean_dec_ref(v_time_430_);
return v___x_434_;
}
}
else
{
uint8_t v___x_435_; 
lean_dec_ref_known(v_x_414_, 2);
lean_dec_ref(v_x_415_);
v___x_435_ = 0;
return v___x_435_;
}
}
case 2:
{
if (lean_obj_tag(v_x_415_) == 2)
{
lean_object* v_date_436_; lean_object* v_date_437_; uint8_t v___x_438_; 
v_date_436_ = lean_ctor_get(v_x_414_, 0);
lean_inc_ref(v_date_436_);
lean_dec_ref_known(v_x_414_, 1);
v_date_437_ = lean_ctor_get(v_x_415_, 0);
lean_inc_ref(v_date_437_);
lean_dec_ref_known(v_x_415_, 1);
v___x_438_ = l_Lake_instDecidableEqDate_decEq(v_date_436_, v_date_437_);
lean_dec_ref(v_date_437_);
lean_dec_ref(v_date_436_);
return v___x_438_;
}
else
{
uint8_t v___x_439_; 
lean_dec_ref_known(v_x_414_, 1);
lean_dec_ref(v_x_415_);
v___x_439_ = 0;
return v___x_439_;
}
}
default: 
{
if (lean_obj_tag(v_x_415_) == 3)
{
lean_object* v_time_440_; lean_object* v_time_441_; uint8_t v___x_442_; 
v_time_440_ = lean_ctor_get(v_x_414_, 0);
lean_inc_ref(v_time_440_);
lean_dec_ref_known(v_x_414_, 1);
v_time_441_ = lean_ctor_get(v_x_415_, 0);
lean_inc_ref(v_time_441_);
lean_dec_ref_known(v_x_415_, 1);
v___x_442_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_440_, v_time_441_);
lean_dec_ref(v_time_441_);
lean_dec_ref(v_time_440_);
return v___x_442_;
}
else
{
uint8_t v___x_443_; 
lean_dec_ref_known(v_x_414_, 1);
lean_dec_ref(v_x_415_);
v___x_443_ = 0;
return v___x_443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___boxed(lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_444_, v_x_445_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime(lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_448_, v_x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime___boxed(lean_object* v_x_451_, lean_object* v_x_452_){
_start:
{
uint8_t v_res_453_; lean_object* v_r_454_; 
v_res_453_ = l_Lake_Toml_instDecidableEqDateTime(v_x_451_, v_x_452_);
v_r_454_ = lean_box(v_res_453_);
return v_r_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeDateDateTime___lam__0(lean_object* v_date_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_456_, 0, v_date_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeTimeDateTime___lam__0(lean_object* v_time_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_460_, 0, v_time_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(lean_object* v_s_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0));
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___boxed(lean_object* v_s_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(v_s_467_);
lean_dec_ref(v_s_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(lean_object* v_s_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0));
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___boxed(lean_object* v_s_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(v_s_471_);
lean_dec_ref(v_s_471_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(lean_object* v_s_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0));
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___boxed(lean_object* v_s_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(v_s_475_);
lean_dec_ref(v_s_475_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(lean_object* v_head_477_, lean_object* v_a_478_, lean_object* v_b_479_){
_start:
{
if (lean_obj_tag(v_a_478_) == 0)
{
lean_object* v_currPos_480_; lean_object* v_searcher_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_520_; 
v_currPos_480_ = lean_ctor_get(v_a_478_, 0);
v_searcher_481_ = lean_ctor_get(v_a_478_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_a_478_);
if (v_isSharedCheck_520_ == 0)
{
v___x_483_ = v_a_478_;
v_isShared_484_ = v_isSharedCheck_520_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_searcher_481_);
lean_inc(v_currPos_480_);
lean_dec(v_a_478_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_520_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v_str_485_; lean_object* v_startInclusive_486_; lean_object* v_endExclusive_487_; lean_object* v_it_489_; lean_object* v_startInclusive_490_; lean_object* v_endExclusive_491_; lean_object* v___x_498_; uint8_t v_decide_499_; 
v_str_485_ = lean_ctor_get(v_head_477_, 0);
v_startInclusive_486_ = lean_ctor_get(v_head_477_, 1);
v_endExclusive_487_ = lean_ctor_get(v_head_477_, 2);
v___x_498_ = lean_nat_sub(v_endExclusive_487_, v_startInclusive_486_);
v_decide_499_ = lean_nat_dec_eq(v_searcher_481_, v___x_498_);
if (v_decide_499_ == 0)
{
uint32_t v___x_500_; lean_object* v___x_501_; uint32_t v___x_502_; uint8_t v___x_503_; 
lean_dec(v___x_498_);
v___x_500_ = 43;
v___x_501_ = lean_nat_add(v_startInclusive_486_, v_searcher_481_);
v___x_502_ = lean_string_utf8_get_fast(v_str_485_, v___x_501_);
v___x_503_ = lean_uint32_dec_eq(v___x_502_, v___x_500_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
lean_dec(v_searcher_481_);
v___x_504_ = lean_string_utf8_next_fast(v_str_485_, v___x_501_);
lean_dec(v___x_501_);
v___x_505_ = lean_nat_sub(v___x_504_, v_startInclusive_486_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_505_);
v___x_507_ = v___x_483_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_currPos_480_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_509_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
v_a_478_ = v___x_507_;
goto _start;
}
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v_slice_513_; lean_object* v_nextIt_515_; 
v___x_510_ = lean_string_utf8_next_fast(v_str_485_, v___x_501_);
v___x_511_ = lean_nat_sub(v___x_510_, v___x_501_);
lean_dec(v___x_501_);
v___x_512_ = lean_nat_add(v_searcher_481_, v___x_511_);
lean_dec(v___x_511_);
v_slice_513_ = l_String_Slice_subslice_x21(v_head_477_, v_currPos_480_, v_searcher_481_);
lean_inc(v___x_512_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v___x_512_);
lean_ctor_set(v___x_483_, 0, v___x_512_);
v_nextIt_515_ = v___x_483_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_512_);
v_nextIt_515_ = v_reuseFailAlloc_518_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v_startInclusive_516_; lean_object* v_endExclusive_517_; 
v_startInclusive_516_ = lean_ctor_get(v_slice_513_, 0);
lean_inc(v_startInclusive_516_);
v_endExclusive_517_ = lean_ctor_get(v_slice_513_, 1);
lean_inc(v_endExclusive_517_);
lean_dec_ref(v_slice_513_);
v_it_489_ = v_nextIt_515_;
v_startInclusive_490_ = v_startInclusive_516_;
v_endExclusive_491_ = v_endExclusive_517_;
goto v___jp_488_;
}
}
}
else
{
lean_object* v___x_519_; 
lean_del_object(v___x_483_);
lean_dec(v_searcher_481_);
v___x_519_ = lean_box(1);
v_it_489_ = v___x_519_;
v_startInclusive_490_ = v_currPos_480_;
v_endExclusive_491_ = v___x_498_;
goto v___jp_488_;
}
v___jp_488_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_492_ = lean_nat_add(v_startInclusive_486_, v_startInclusive_490_);
lean_dec(v_startInclusive_490_);
v___x_493_ = lean_nat_add(v_startInclusive_486_, v_endExclusive_491_);
lean_dec(v_endExclusive_491_);
lean_inc_ref(v_str_485_);
v___x_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_494_, 0, v_str_485_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_493_);
v___x_495_ = l_String_Slice_toString(v___x_494_);
lean_dec_ref_known(v___x_494_, 3);
v___x_496_ = lean_array_push(v_b_479_, v___x_495_);
v_a_478_ = v_it_489_;
v_b_479_ = v___x_496_;
goto _start;
}
}
}
else
{
return v_b_479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg___boxed(lean_object* v_head_521_, lean_object* v_a_522_, lean_object* v_b_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_521_, v_a_522_, v_b_523_);
lean_dec_ref(v_head_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(lean_object* v_dt_525_, lean_object* v___x_526_, lean_object* v___x_527_, lean_object* v_a_528_, lean_object* v_b_529_){
_start:
{
lean_object* v_it_531_; lean_object* v_startInclusive_532_; lean_object* v_endExclusive_533_; 
if (lean_obj_tag(v_a_528_) == 0)
{
lean_object* v_currPos_537_; lean_object* v_searcher_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_567_; 
v_currPos_537_ = lean_ctor_get(v_a_528_, 0);
v_searcher_538_ = lean_ctor_get(v_a_528_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_a_528_);
if (v_isSharedCheck_567_ == 0)
{
v___x_540_ = v_a_528_;
v_isShared_541_ = v_isSharedCheck_567_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_searcher_538_);
lean_inc(v_currPos_537_);
lean_dec(v_a_528_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_567_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
uint8_t v___y_543_; uint8_t v_decide_558_; 
v_decide_558_ = lean_nat_dec_eq(v_searcher_538_, v___x_527_);
if (v_decide_558_ == 0)
{
uint32_t v___x_559_; uint32_t v___x_560_; uint8_t v___x_561_; 
v___x_559_ = lean_string_utf8_get_fast(v_dt_525_, v_searcher_538_);
v___x_560_ = 84;
v___x_561_ = lean_uint32_dec_eq(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
uint32_t v___x_562_; uint8_t v___x_563_; 
v___x_562_ = 116;
v___x_563_ = lean_uint32_dec_eq(v___x_559_, v___x_562_);
if (v___x_563_ == 0)
{
uint32_t v___x_564_; uint8_t v___x_565_; 
v___x_564_ = 32;
v___x_565_ = lean_uint32_dec_eq(v___x_559_, v___x_564_);
v___y_543_ = v___x_565_;
goto v___jp_542_;
}
else
{
v___y_543_ = v___x_563_;
goto v___jp_542_;
}
}
else
{
v___y_543_ = v___x_561_;
goto v___jp_542_;
}
}
else
{
lean_object* v___x_566_; 
lean_del_object(v___x_540_);
lean_dec(v_searcher_538_);
v___x_566_ = lean_box(1);
lean_inc(v___x_527_);
v_it_531_ = v___x_566_;
v_startInclusive_532_ = v_currPos_537_;
v_endExclusive_533_ = v___x_527_;
goto v___jp_530_;
}
v___jp_542_:
{
if (v___y_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_string_utf8_next_fast(v_dt_525_, v_searcher_538_);
lean_dec(v_searcher_538_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_544_);
v___x_546_ = v___x_540_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_currPos_537_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_544_);
v___x_546_ = v_reuseFailAlloc_548_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
v_a_528_ = v___x_546_;
goto _start;
}
}
else
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_slice_552_; lean_object* v_nextIt_554_; 
v___x_549_ = lean_string_utf8_next_fast(v_dt_525_, v_searcher_538_);
v___x_550_ = lean_nat_sub(v___x_549_, v_searcher_538_);
v___x_551_ = lean_nat_add(v_searcher_538_, v___x_550_);
lean_dec(v___x_550_);
v_slice_552_ = l_String_Slice_subslice_x21(v___x_526_, v_currPos_537_, v_searcher_538_);
lean_inc(v___x_551_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_551_);
lean_ctor_set(v___x_540_, 0, v___x_551_);
v_nextIt_554_ = v___x_540_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_551_);
v_nextIt_554_ = v_reuseFailAlloc_557_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v_startInclusive_555_; lean_object* v_endExclusive_556_; 
v_startInclusive_555_ = lean_ctor_get(v_slice_552_, 0);
lean_inc(v_startInclusive_555_);
v_endExclusive_556_ = lean_ctor_get(v_slice_552_, 1);
lean_inc(v_endExclusive_556_);
lean_dec_ref(v_slice_552_);
v_it_531_ = v_nextIt_554_;
v_startInclusive_532_ = v_startInclusive_555_;
v_endExclusive_533_ = v_endExclusive_556_;
goto v___jp_530_;
}
}
}
}
}
else
{
lean_dec(v___x_527_);
lean_dec_ref(v_dt_525_);
return v_b_529_;
}
v___jp_530_:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_inc_ref(v_dt_525_);
v___x_534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_534_, 0, v_dt_525_);
lean_ctor_set(v___x_534_, 1, v_startInclusive_532_);
lean_ctor_set(v___x_534_, 2, v_endExclusive_533_);
v___x_535_ = lean_array_push(v_b_529_, v___x_534_);
v_a_528_ = v_it_531_;
v_b_529_ = v___x_535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg___boxed(lean_object* v_dt_568_, lean_object* v___x_569_, lean_object* v___x_570_, lean_object* v_a_571_, lean_object* v_b_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_568_, v___x_569_, v___x_570_, v_a_571_, v_b_572_);
lean_dec_ref(v___x_569_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(lean_object* v_head_574_, lean_object* v_a_575_, lean_object* v_b_576_){
_start:
{
if (lean_obj_tag(v_a_575_) == 0)
{
lean_object* v_currPos_577_; lean_object* v_searcher_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_617_; 
v_currPos_577_ = lean_ctor_get(v_a_575_, 0);
v_searcher_578_ = lean_ctor_get(v_a_575_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_a_575_);
if (v_isSharedCheck_617_ == 0)
{
v___x_580_ = v_a_575_;
v_isShared_581_ = v_isSharedCheck_617_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_searcher_578_);
lean_inc(v_currPos_577_);
lean_dec(v_a_575_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_617_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v_str_582_; lean_object* v_startInclusive_583_; lean_object* v_endExclusive_584_; lean_object* v_it_586_; lean_object* v_startInclusive_587_; lean_object* v_endExclusive_588_; lean_object* v___x_595_; uint8_t v_decide_596_; 
v_str_582_ = lean_ctor_get(v_head_574_, 0);
v_startInclusive_583_ = lean_ctor_get(v_head_574_, 1);
v_endExclusive_584_ = lean_ctor_get(v_head_574_, 2);
v___x_595_ = lean_nat_sub(v_endExclusive_584_, v_startInclusive_583_);
v_decide_596_ = lean_nat_dec_eq(v_searcher_578_, v___x_595_);
if (v_decide_596_ == 0)
{
uint32_t v___x_597_; lean_object* v___x_598_; uint32_t v___x_599_; uint8_t v___x_600_; 
lean_dec(v___x_595_);
v___x_597_ = 45;
v___x_598_ = lean_nat_add(v_startInclusive_583_, v_searcher_578_);
v___x_599_ = lean_string_utf8_get_fast(v_str_582_, v___x_598_);
v___x_600_ = lean_uint32_dec_eq(v___x_599_, v___x_597_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
lean_dec(v_searcher_578_);
v___x_601_ = lean_string_utf8_next_fast(v_str_582_, v___x_598_);
lean_dec(v___x_598_);
v___x_602_ = lean_nat_sub(v___x_601_, v_startInclusive_583_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_602_);
v___x_604_ = v___x_580_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_currPos_577_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v___x_602_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
v_a_575_ = v___x_604_;
goto _start;
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v_slice_610_; lean_object* v_nextIt_612_; 
v___x_607_ = lean_string_utf8_next_fast(v_str_582_, v___x_598_);
v___x_608_ = lean_nat_sub(v___x_607_, v___x_598_);
lean_dec(v___x_598_);
v___x_609_ = lean_nat_add(v_searcher_578_, v___x_608_);
lean_dec(v___x_608_);
v_slice_610_ = l_String_Slice_subslice_x21(v_head_574_, v_currPos_577_, v_searcher_578_);
lean_inc(v___x_609_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 1, v___x_609_);
lean_ctor_set(v___x_580_, 0, v___x_609_);
v_nextIt_612_ = v___x_580_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_609_);
v_nextIt_612_ = v_reuseFailAlloc_615_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v_startInclusive_613_; lean_object* v_endExclusive_614_; 
v_startInclusive_613_ = lean_ctor_get(v_slice_610_, 0);
lean_inc(v_startInclusive_613_);
v_endExclusive_614_ = lean_ctor_get(v_slice_610_, 1);
lean_inc(v_endExclusive_614_);
lean_dec_ref(v_slice_610_);
v_it_586_ = v_nextIt_612_;
v_startInclusive_587_ = v_startInclusive_613_;
v_endExclusive_588_ = v_endExclusive_614_;
goto v___jp_585_;
}
}
}
else
{
lean_object* v___x_616_; 
lean_del_object(v___x_580_);
lean_dec(v_searcher_578_);
v___x_616_ = lean_box(1);
v_it_586_ = v___x_616_;
v_startInclusive_587_ = v_currPos_577_;
v_endExclusive_588_ = v___x_595_;
goto v___jp_585_;
}
v___jp_585_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_589_ = lean_nat_add(v_startInclusive_583_, v_startInclusive_587_);
lean_dec(v_startInclusive_587_);
v___x_590_ = lean_nat_add(v_startInclusive_583_, v_endExclusive_588_);
lean_dec(v_endExclusive_588_);
lean_inc_ref(v_str_582_);
v___x_591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_591_, 0, v_str_582_);
lean_ctor_set(v___x_591_, 1, v___x_589_);
lean_ctor_set(v___x_591_, 2, v___x_590_);
v___x_592_ = l_String_Slice_toString(v___x_591_);
lean_dec_ref_known(v___x_591_, 3);
v___x_593_ = lean_array_push(v_b_576_, v___x_592_);
v_a_575_ = v_it_586_;
v_b_576_ = v___x_593_;
goto _start;
}
}
}
else
{
return v_b_576_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg___boxed(lean_object* v_head_618_, lean_object* v_a_619_, lean_object* v_b_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_618_, v_a_619_, v_b_620_);
lean_dec_ref(v_head_618_);
return v_res_621_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(lean_object* v_s_622_, lean_object* v_a_623_, uint8_t v_b_624_){
_start:
{
lean_object* v_str_625_; lean_object* v_startInclusive_626_; lean_object* v_endExclusive_627_; lean_object* v___x_628_; uint8_t v_decide_629_; 
v_str_625_ = lean_ctor_get(v_s_622_, 0);
v_startInclusive_626_ = lean_ctor_get(v_s_622_, 1);
v_endExclusive_627_ = lean_ctor_get(v_s_622_, 2);
v___x_628_ = lean_nat_sub(v_endExclusive_627_, v_startInclusive_626_);
v_decide_629_ = lean_nat_dec_eq(v_a_623_, v___x_628_);
lean_dec(v___x_628_);
if (v_decide_629_ == 0)
{
lean_object* v___x_630_; uint32_t v___x_631_; uint32_t v___x_632_; uint8_t v___x_633_; 
v___x_630_ = lean_nat_add(v_startInclusive_626_, v_a_623_);
lean_dec(v_a_623_);
v___x_631_ = lean_string_utf8_get_fast(v_str_625_, v___x_630_);
v___x_632_ = 58;
v___x_633_ = lean_uint32_dec_eq(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_string_utf8_next_fast(v_str_625_, v___x_630_);
lean_dec(v___x_630_);
v___x_635_ = lean_nat_sub(v___x_634_, v_startInclusive_626_);
v_a_623_ = v___x_635_;
v_b_624_ = v___x_633_;
goto _start;
}
else
{
lean_dec(v___x_630_);
return v___x_633_;
}
}
else
{
lean_dec(v_a_623_);
return v_b_624_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_s_637_, lean_object* v_a_638_, lean_object* v_b_639_){
_start:
{
uint8_t v_b_boxed_640_; uint8_t v_res_641_; lean_object* v_r_642_; 
v_b_boxed_640_ = lean_unbox(v_b_639_);
v_res_641_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_637_, v_a_638_, v_b_boxed_640_);
lean_dec_ref(v_s_637_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(lean_object* v_s_643_){
_start:
{
lean_object* v_searcher_644_; uint8_t v___x_645_; uint8_t v___x_646_; 
v_searcher_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = 0;
v___x_646_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_643_, v_searcher_644_, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2___boxed(lean_object* v_s_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_s_647_);
lean_dec_ref(v_s_647_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ofString_x3f(lean_object* v_dt_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_string_utf8_byte_size(v_dt_650_);
lean_inc_ref(v_dt_650_);
v___x_653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_653_, 0, v_dt_650_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
lean_ctor_set(v___x_653_, 2, v___x_652_);
v___x_654_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(v___x_653_);
v___x_655_ = ((lean_object*)(l_Lake_Toml_Time_ofString_x3f___closed__0));
v___x_656_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_650_, v___x_653_, v___x_652_, v___x_654_, v___x_655_);
lean_dec_ref_known(v___x_653_, 3);
v___x_657_ = lean_array_to_list(v___x_656_);
if (lean_obj_tag(v___x_657_) == 1)
{
lean_object* v_tail_658_; 
v_tail_658_ = lean_ctor_get(v___x_657_, 1);
lean_inc(v_tail_658_);
if (lean_obj_tag(v_tail_658_) == 0)
{
lean_object* v_head_659_; uint8_t v___x_660_; 
v_head_659_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_head_659_);
lean_dec_ref_known(v___x_657_, 2);
v___x_660_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_head_659_);
if (v___x_660_ == 0)
{
lean_object* v_str_661_; lean_object* v_startInclusive_662_; lean_object* v_endExclusive_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_str_661_ = lean_ctor_get(v_head_659_, 0);
lean_inc_ref(v_str_661_);
v_startInclusive_662_ = lean_ctor_get(v_head_659_, 1);
lean_inc(v_startInclusive_662_);
v_endExclusive_663_ = lean_ctor_get(v_head_659_, 2);
lean_inc(v_endExclusive_663_);
lean_dec(v_head_659_);
v___x_664_ = lean_string_utf8_extract_fast(v_str_661_, v_startInclusive_662_, v_endExclusive_663_);
lean_dec(v_endExclusive_663_);
lean_dec(v_startInclusive_662_);
lean_dec_ref(v_str_661_);
v___x_665_ = l_Lake_Date_ofString_x3f(v___x_664_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v___x_666_; 
v___x_666_ = lean_box(0);
return v___x_666_;
}
else
{
lean_object* v_val_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v_val_667_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v___x_665_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_val_667_);
lean_dec(v___x_665_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_671_, 0, v_val_667_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v_str_676_; lean_object* v_startInclusive_677_; lean_object* v_endExclusive_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_str_676_ = lean_ctor_get(v_head_659_, 0);
lean_inc_ref(v_str_676_);
v_startInclusive_677_ = lean_ctor_get(v_head_659_, 1);
lean_inc(v_startInclusive_677_);
v_endExclusive_678_ = lean_ctor_get(v_head_659_, 2);
lean_inc(v_endExclusive_678_);
lean_dec(v_head_659_);
v___x_679_ = lean_string_utf8_extract_fast(v_str_676_, v_startInclusive_677_, v_endExclusive_678_);
lean_dec(v_endExclusive_678_);
lean_dec(v_startInclusive_677_);
lean_dec_ref(v_str_676_);
v___x_680_ = l_Lake_Toml_Time_ofString_x3f(v___x_679_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; 
v___x_681_ = lean_box(0);
return v___x_681_;
}
else
{
lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_690_; 
v_val_682_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_690_ == 0)
{
v___x_684_ = v___x_680_;
v_isShared_685_ = v_isSharedCheck_690_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v___x_680_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_690_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_686_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_686_, 0, v_val_682_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_686_);
v___x_688_ = v___x_684_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
else
{
lean_object* v_tail_691_; 
v_tail_691_ = lean_ctor_get(v_tail_658_, 1);
if (lean_obj_tag(v_tail_691_) == 0)
{
lean_object* v_head_692_; lean_object* v_head_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_868_; 
v_head_692_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_head_692_);
lean_dec_ref_known(v___x_657_, 2);
v_head_693_ = lean_ctor_get(v_tail_658_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v_tail_658_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; 
v_unused_869_ = lean_ctor_get(v_tail_658_, 1);
lean_dec(v_unused_869_);
v___x_695_ = v_tail_658_;
v_isShared_696_ = v_isSharedCheck_868_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_head_693_);
lean_dec(v_tail_658_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_868_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_str_697_; lean_object* v_startInclusive_698_; lean_object* v_endExclusive_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v_str_697_ = lean_ctor_get(v_head_692_, 0);
lean_inc_ref(v_str_697_);
v_startInclusive_698_ = lean_ctor_get(v_head_692_, 1);
lean_inc(v_startInclusive_698_);
v_endExclusive_699_ = lean_ctor_get(v_head_692_, 2);
lean_inc(v_endExclusive_699_);
lean_dec(v_head_692_);
v___x_700_ = lean_string_utf8_extract_fast(v_str_697_, v_startInclusive_698_, v_endExclusive_699_);
lean_dec(v_endExclusive_699_);
lean_dec(v_startInclusive_698_);
lean_dec_ref(v_str_697_);
v___x_701_ = l_Lake_Date_ofString_x3f(v___x_700_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v___x_702_; 
lean_del_object(v___x_695_);
lean_dec(v_head_693_);
v___x_702_ = lean_box(0);
return v___x_702_;
}
else
{
lean_object* v_val_703_; lean_object* v_str_704_; lean_object* v_startInclusive_705_; lean_object* v_endExclusive_706_; uint8_t v___y_723_; uint32_t v___y_798_; uint32_t v___y_849_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_val_703_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v___x_701_, 1);
v_str_704_ = lean_ctor_get(v_head_693_, 0);
v_startInclusive_705_ = lean_ctor_get(v_head_693_, 1);
v_endExclusive_706_ = lean_ctor_get(v_head_693_, 2);
v___x_860_ = lean_nat_sub(v_endExclusive_706_, v_startInclusive_705_);
v___x_861_ = l_String_Slice_Pos_prev_x3f(v_head_693_, v___x_860_);
lean_dec(v___x_860_);
if (lean_obj_tag(v___x_861_) == 0)
{
uint32_t v___x_862_; 
v___x_862_ = 65;
v___y_849_ = v___x_862_;
goto v___jp_848_;
}
else
{
lean_object* v_val_863_; lean_object* v___x_864_; 
v_val_863_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v___x_861_, 1);
v___x_864_ = l_String_Slice_Pos_get_x3f(v_head_693_, v_val_863_);
lean_dec(v_val_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
uint32_t v___x_865_; 
v___x_865_ = 65;
v___y_849_ = v___x_865_;
goto v___jp_848_;
}
else
{
lean_object* v_val_866_; uint32_t v___x_867_; 
v_val_866_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_val_866_);
lean_dec_ref_known(v___x_864_, 1);
v___x_867_ = lean_unbox_uint32(v_val_866_);
lean_dec(v_val_866_);
v___y_849_ = v___x_867_;
goto v___jp_848_;
}
}
v___jp_707_:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_string_utf8_extract_fast(v_str_704_, v_startInclusive_705_, v_endExclusive_706_);
lean_dec(v_endExclusive_706_);
lean_dec(v_startInclusive_705_);
lean_dec_ref(v_str_704_);
v___x_709_ = l_Lake_Toml_Time_ofString_x3f(v___x_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v___x_710_; 
lean_dec(v_val_703_);
lean_del_object(v___x_695_);
v___x_710_ = lean_box(0);
return v___x_710_;
}
else
{
lean_object* v_val_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_721_; 
v_val_711_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_721_ == 0)
{
v___x_713_ = v___x_709_;
v_isShared_714_ = v_isSharedCheck_721_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_val_711_);
lean_dec(v___x_709_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_721_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v_val_711_);
lean_ctor_set(v___x_695_, 0, v_val_703_);
v___x_716_ = v___x_695_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_val_703_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_val_711_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_716_);
v___x_718_ = v___x_713_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
v___jp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_766_; 
v___x_724_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(v_head_693_);
v___x_725_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_693_, v___x_724_, v___x_655_);
v_isSharedCheck_766_ = !lean_is_exclusive(v_head_693_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; 
v_unused_767_ = lean_ctor_get(v_head_693_, 2);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_head_693_, 1);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_head_693_, 0);
lean_dec(v_unused_769_);
v___x_727_ = v_head_693_;
v_isShared_728_ = v_isSharedCheck_766_;
goto v_resetjp_726_;
}
else
{
lean_dec(v_head_693_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_766_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; 
v___x_729_ = lean_array_to_list(v___x_725_);
if (lean_obj_tag(v___x_729_) == 1)
{
lean_object* v_tail_730_; 
v_tail_730_ = lean_ctor_get(v___x_729_, 1);
lean_inc(v_tail_730_);
if (lean_obj_tag(v_tail_730_) == 1)
{
lean_object* v_tail_731_; 
v_tail_731_ = lean_ctor_get(v_tail_730_, 1);
if (lean_obj_tag(v_tail_731_) == 0)
{
lean_object* v_head_732_; lean_object* v_head_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_764_; 
lean_dec(v_endExclusive_706_);
lean_dec(v_startInclusive_705_);
lean_dec_ref(v_str_704_);
lean_del_object(v___x_695_);
v_head_732_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_head_732_);
lean_dec_ref_known(v___x_729_, 2);
v_head_733_ = lean_ctor_get(v_tail_730_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_tail_730_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v_tail_730_, 1);
lean_dec(v_unused_765_);
v___x_735_ = v_tail_730_;
v_isShared_736_ = v_isSharedCheck_764_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_head_733_);
lean_dec(v_tail_730_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_764_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lake_Toml_Time_ofString_x3f(v_head_732_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_738_; 
lean_del_object(v___x_735_);
lean_dec(v_head_733_);
lean_del_object(v___x_727_);
lean_dec(v_val_703_);
v___x_738_ = lean_box(0);
return v___x_738_;
}
else
{
lean_object* v_val_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_763_; 
v_val_739_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_763_ == 0)
{
v___x_741_ = v___x_737_;
v_isShared_742_ = v_isSharedCheck_763_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_val_739_);
lean_dec(v___x_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_763_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lake_Toml_Time_ofString_x3f(v_head_733_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v___x_744_; 
lean_del_object(v___x_741_);
lean_dec(v_val_739_);
lean_del_object(v___x_735_);
lean_del_object(v___x_727_);
lean_dec(v_val_703_);
v___x_744_ = lean_box(0);
return v___x_744_;
}
else
{
lean_object* v_val_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_762_; 
v_val_745_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_762_ == 0)
{
v___x_747_ = v___x_743_;
v_isShared_748_ = v_isSharedCheck_762_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_val_745_);
lean_dec(v___x_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_762_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = lean_box(v___y_723_);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 0);
lean_ctor_set(v___x_735_, 1, v_val_745_);
lean_ctor_set(v___x_735_, 0, v___x_749_);
v___x_751_ = v___x_735_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_val_745_);
v___x_751_ = v_reuseFailAlloc_761_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_753_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_753_ = v___x_747_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_760_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_755_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 2, v___x_753_);
lean_ctor_set(v___x_727_, 1, v_val_739_);
lean_ctor_set(v___x_727_, 0, v_val_703_);
v___x_755_ = v___x_727_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_val_703_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_val_739_);
lean_ctor_set(v_reuseFailAlloc_759_, 2, v___x_753_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_755_);
v___x_757_ = v___x_741_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
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
lean_dec_ref_known(v_tail_730_, 2);
lean_dec_ref_known(v___x_729_, 2);
lean_del_object(v___x_727_);
goto v___jp_707_;
}
}
else
{
lean_dec_ref_known(v___x_729_, 2);
lean_dec(v_tail_730_);
lean_del_object(v___x_727_);
goto v___jp_707_;
}
}
else
{
lean_dec(v___x_729_);
lean_del_object(v___x_727_);
goto v___jp_707_;
}
}
}
v___jp_770_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_793_; 
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = lean_nat_sub(v_endExclusive_706_, v_startInclusive_705_);
v___x_773_ = l_String_Slice_Pos_prevn(v_head_693_, v___x_772_, v___x_771_);
v_isSharedCheck_793_ = !lean_is_exclusive(v_head_693_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; lean_object* v_unused_795_; lean_object* v_unused_796_; 
v_unused_794_ = lean_ctor_get(v_head_693_, 2);
lean_dec(v_unused_794_);
v_unused_795_ = lean_ctor_get(v_head_693_, 1);
lean_dec(v_unused_795_);
v_unused_796_ = lean_ctor_get(v_head_693_, 0);
lean_dec(v_unused_796_);
v___x_775_ = v_head_693_;
v_isShared_776_ = v_isSharedCheck_793_;
goto v_resetjp_774_;
}
else
{
lean_dec(v_head_693_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_793_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_777_ = lean_nat_add(v_startInclusive_705_, v___x_773_);
lean_dec(v___x_773_);
v___x_778_ = lean_string_utf8_extract_fast(v_str_704_, v_startInclusive_705_, v___x_777_);
lean_dec(v___x_777_);
lean_dec(v_startInclusive_705_);
lean_dec_ref(v_str_704_);
v___x_779_ = l_Lake_Toml_Time_ofString_x3f(v___x_778_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; 
lean_del_object(v___x_775_);
lean_dec(v_val_703_);
v___x_780_ = lean_box(0);
return v___x_780_;
}
else
{
lean_object* v_val_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_792_; 
v_val_781_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_792_ == 0)
{
v___x_783_ = v___x_779_;
v_isShared_784_ = v_isSharedCheck_792_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_val_781_);
lean_dec(v___x_779_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_792_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_785_ = lean_box(0);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 2, v___x_785_);
lean_ctor_set(v___x_775_, 1, v_val_781_);
lean_ctor_set(v___x_775_, 0, v_val_703_);
v___x_787_ = v___x_775_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_val_703_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_val_781_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v___x_785_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_787_);
v___x_789_ = v___x_783_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
}
v___jp_797_:
{
uint32_t v___x_799_; uint8_t v___x_800_; 
v___x_799_ = 122;
v___x_800_ = lean_uint32_dec_eq(v___y_798_, v___x_799_);
if (v___x_800_ == 0)
{
uint8_t v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_801_ = 1;
v___x_802_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(v_head_693_);
v___x_803_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_693_, v___x_802_, v___x_655_);
v___x_804_ = lean_array_to_list(v___x_803_);
if (lean_obj_tag(v___x_804_) == 1)
{
lean_object* v_tail_805_; 
v_tail_805_ = lean_ctor_get(v___x_804_, 1);
lean_inc(v_tail_805_);
if (lean_obj_tag(v_tail_805_) == 1)
{
lean_object* v_tail_806_; 
v_tail_806_ = lean_ctor_get(v_tail_805_, 1);
if (lean_obj_tag(v_tail_806_) == 0)
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_844_; 
lean_del_object(v___x_695_);
v_isSharedCheck_844_ = !lean_is_exclusive(v_head_693_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; lean_object* v_unused_846_; lean_object* v_unused_847_; 
v_unused_845_ = lean_ctor_get(v_head_693_, 2);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_head_693_, 1);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_head_693_, 0);
lean_dec(v_unused_847_);
v___x_808_ = v_head_693_;
v_isShared_809_ = v_isSharedCheck_844_;
goto v_resetjp_807_;
}
else
{
lean_dec(v_head_693_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_844_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_head_810_; lean_object* v_head_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_842_; 
v_head_810_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_head_810_);
lean_dec_ref_known(v___x_804_, 2);
v_head_811_ = lean_ctor_get(v_tail_805_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_tail_805_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_tail_805_, 1);
lean_dec(v_unused_843_);
v___x_813_ = v_tail_805_;
v_isShared_814_ = v_isSharedCheck_842_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_head_811_);
lean_dec(v_tail_805_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_842_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lake_Toml_Time_ofString_x3f(v_head_810_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_816_; 
lean_del_object(v___x_813_);
lean_dec(v_head_811_);
lean_del_object(v___x_808_);
lean_dec(v_val_703_);
v___x_816_ = lean_box(0);
return v___x_816_;
}
else
{
lean_object* v_val_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_841_; 
v_val_817_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_841_ == 0)
{
v___x_819_ = v___x_815_;
v_isShared_820_ = v_isSharedCheck_841_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_val_817_);
lean_dec(v___x_815_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_841_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lake_Toml_Time_ofString_x3f(v_head_811_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v___x_822_; 
lean_del_object(v___x_819_);
lean_dec(v_val_817_);
lean_del_object(v___x_813_);
lean_del_object(v___x_808_);
lean_dec(v_val_703_);
v___x_822_ = lean_box(0);
return v___x_822_;
}
else
{
lean_object* v_val_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_840_; 
v_val_823_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_840_ == 0)
{
v___x_825_ = v___x_821_;
v_isShared_826_ = v_isSharedCheck_840_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_val_823_);
lean_dec(v___x_821_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_840_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_box(v___x_800_);
if (v_isShared_814_ == 0)
{
lean_ctor_set_tag(v___x_813_, 0);
lean_ctor_set(v___x_813_, 1, v_val_823_);
lean_ctor_set(v___x_813_, 0, v___x_827_);
v___x_829_ = v___x_813_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_839_, 1, v_val_823_);
v___x_829_ = v_reuseFailAlloc_839_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_831_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_829_);
v___x_831_ = v___x_825_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_838_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_833_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 2, v___x_831_);
lean_ctor_set(v___x_808_, 1, v_val_817_);
lean_ctor_set(v___x_808_, 0, v_val_703_);
v___x_833_ = v___x_808_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_val_703_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_val_817_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v___x_831_);
v___x_833_ = v_reuseFailAlloc_837_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 0, v___x_833_);
v___x_835_ = v___x_819_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
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
lean_inc(v_endExclusive_706_);
lean_inc(v_startInclusive_705_);
lean_inc_ref(v_str_704_);
lean_dec_ref_known(v_tail_805_, 2);
lean_dec_ref_known(v___x_804_, 2);
v___y_723_ = v___x_801_;
goto v___jp_722_;
}
}
else
{
lean_inc(v_endExclusive_706_);
lean_inc(v_startInclusive_705_);
lean_inc_ref(v_str_704_);
lean_dec(v_tail_805_);
lean_dec_ref_known(v___x_804_, 2);
v___y_723_ = v___x_801_;
goto v___jp_722_;
}
}
else
{
lean_inc(v_endExclusive_706_);
lean_inc(v_startInclusive_705_);
lean_inc_ref(v_str_704_);
lean_dec(v___x_804_);
v___y_723_ = v___x_801_;
goto v___jp_722_;
}
}
else
{
lean_inc(v_startInclusive_705_);
lean_inc_ref(v_str_704_);
lean_del_object(v___x_695_);
goto v___jp_770_;
}
}
v___jp_848_:
{
uint32_t v___x_850_; uint8_t v___x_851_; 
v___x_850_ = 90;
v___x_851_ = lean_uint32_dec_eq(v___y_849_, v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_nat_sub(v_endExclusive_706_, v_startInclusive_705_);
v___x_853_ = l_String_Slice_Pos_prev_x3f(v_head_693_, v___x_852_);
lean_dec(v___x_852_);
if (lean_obj_tag(v___x_853_) == 0)
{
uint32_t v___x_854_; 
v___x_854_ = 65;
v___y_798_ = v___x_854_;
goto v___jp_797_;
}
else
{
lean_object* v_val_855_; lean_object* v___x_856_; 
v_val_855_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v___x_853_, 1);
v___x_856_ = l_String_Slice_Pos_get_x3f(v_head_693_, v_val_855_);
lean_dec(v_val_855_);
if (lean_obj_tag(v___x_856_) == 0)
{
uint32_t v___x_857_; 
v___x_857_ = 65;
v___y_798_ = v___x_857_;
goto v___jp_797_;
}
else
{
lean_object* v_val_858_; uint32_t v___x_859_; 
v_val_858_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v___x_856_, 1);
v___x_859_ = lean_unbox_uint32(v_val_858_);
lean_dec(v_val_858_);
v___y_798_ = v___x_859_;
goto v___jp_797_;
}
}
}
else
{
lean_inc(v_startInclusive_705_);
lean_inc_ref(v_str_704_);
lean_del_object(v___x_695_);
goto v___jp_770_;
}
}
}
}
}
else
{
lean_object* v___x_870_; 
lean_dec_ref_known(v_tail_658_, 2);
lean_dec_ref_known(v___x_657_, 2);
v___x_870_ = lean_box(0);
return v___x_870_;
}
}
}
else
{
lean_object* v___x_871_; 
lean_dec(v___x_657_);
v___x_871_ = lean_box(0);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(lean_object* v_dt_872_, lean_object* v___x_873_, lean_object* v___x_874_, lean_object* v_inst_875_, lean_object* v_R_876_, lean_object* v_a_877_, lean_object* v_b_878_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_872_, v___x_873_, v___x_874_, v_a_877_, v_b_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___boxed(lean_object* v_dt_880_, lean_object* v___x_881_, lean_object* v___x_882_, lean_object* v_inst_883_, lean_object* v_R_884_, lean_object* v_a_885_, lean_object* v_b_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(v_dt_880_, v___x_881_, v___x_882_, v_inst_883_, v_R_884_, v_a_885_, v_b_886_);
lean_dec_ref(v___x_881_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(lean_object* v_head_888_, lean_object* v_inst_889_, lean_object* v_R_890_, lean_object* v_a_891_, lean_object* v_b_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_888_, v_a_891_, v_b_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___boxed(lean_object* v_head_894_, lean_object* v_inst_895_, lean_object* v_R_896_, lean_object* v_a_897_, lean_object* v_b_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(v_head_894_, v_inst_895_, v_R_896_, v_a_897_, v_b_898_);
lean_dec_ref(v_head_894_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(lean_object* v_head_900_, lean_object* v_inst_901_, lean_object* v_R_902_, lean_object* v_a_903_, lean_object* v_b_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_900_, v_a_903_, v_b_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___boxed(lean_object* v_head_906_, lean_object* v_inst_907_, lean_object* v_R_908_, lean_object* v_a_909_, lean_object* v_b_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(v_head_906_, v_inst_907_, v_R_908_, v_a_909_, v_b_910_);
lean_dec_ref(v_head_906_);
return v_res_911_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(lean_object* v_s_912_, lean_object* v_inst_913_, lean_object* v_R_914_, lean_object* v_a_915_, uint8_t v_b_916_, lean_object* v_c_917_){
_start:
{
uint8_t v___x_918_; 
v___x_918_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_912_, v_a_915_, v_b_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___boxed(lean_object* v_s_919_, lean_object* v_inst_920_, lean_object* v_R_921_, lean_object* v_a_922_, lean_object* v_b_923_, lean_object* v_c_924_){
_start:
{
uint8_t v_b_boxed_925_; uint8_t v_res_926_; lean_object* v_r_927_; 
v_b_boxed_925_ = lean_unbox(v_b_923_);
v_res_926_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(v_s_919_, v_inst_920_, v_R_921_, v_a_922_, v_b_boxed_925_, v_c_924_);
lean_dec_ref(v_s_919_);
v_r_927_ = lean_box(v_res_926_);
return v_r_927_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_toString(lean_object* v_dt_932_){
_start:
{
switch(lean_obj_tag(v_dt_932_))
{
case 0:
{
lean_object* v_offset_x3f_933_; 
v_offset_x3f_933_ = lean_ctor_get(v_dt_932_, 2);
if (lean_obj_tag(v_offset_x3f_933_) == 1)
{
lean_object* v_val_934_; lean_object* v_fst_935_; uint8_t v___x_936_; 
v_val_934_ = lean_ctor_get(v_offset_x3f_933_, 0);
v_fst_935_ = lean_ctor_get(v_val_934_, 0);
v___x_936_ = lean_unbox(v_fst_935_);
if (v___x_936_ == 0)
{
lean_object* v_snd_937_; lean_object* v_date_938_; lean_object* v_time_939_; lean_object* v_hour_940_; lean_object* v_minute_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_snd_937_ = lean_ctor_get(v_val_934_, 1);
lean_inc(v_snd_937_);
v_date_938_ = lean_ctor_get(v_dt_932_, 0);
lean_inc_ref(v_date_938_);
v_time_939_ = lean_ctor_get(v_dt_932_, 1);
lean_inc_ref(v_time_939_);
lean_dec_ref_known(v_dt_932_, 3);
v_hour_940_ = lean_ctor_get(v_snd_937_, 0);
lean_inc(v_hour_940_);
v_minute_941_ = lean_ctor_get(v_snd_937_, 1);
lean_inc(v_minute_941_);
lean_dec(v_snd_937_);
v___x_942_ = l_Lake_Date_toString(v_date_938_);
v___x_943_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_944_ = lean_string_append(v___x_942_, v___x_943_);
v___x_945_ = l_Lake_Toml_Time_toString(v_time_939_);
v___x_946_ = lean_string_append(v___x_944_, v___x_945_);
lean_dec_ref(v___x_945_);
v___x_947_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__1));
v___x_948_ = lean_string_append(v___x_946_, v___x_947_);
v___x_949_ = lean_unsigned_to_nat(2u);
v___x_950_ = l_Lake_zpad(v_hour_940_, v___x_949_);
v___x_951_ = lean_string_append(v___x_948_, v___x_950_);
lean_dec_ref(v___x_950_);
v___x_952_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_953_ = lean_string_append(v___x_951_, v___x_952_);
v___x_954_ = l_Lake_zpad(v_minute_941_, v___x_949_);
v___x_955_ = lean_string_append(v___x_953_, v___x_954_);
lean_dec_ref(v___x_954_);
return v___x_955_;
}
else
{
lean_object* v_snd_956_; lean_object* v_date_957_; lean_object* v_time_958_; lean_object* v_hour_959_; lean_object* v_minute_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_snd_956_ = lean_ctor_get(v_val_934_, 1);
lean_inc(v_snd_956_);
v_date_957_ = lean_ctor_get(v_dt_932_, 0);
lean_inc_ref(v_date_957_);
v_time_958_ = lean_ctor_get(v_dt_932_, 1);
lean_inc_ref(v_time_958_);
lean_dec_ref_known(v_dt_932_, 3);
v_hour_959_ = lean_ctor_get(v_snd_956_, 0);
lean_inc(v_hour_959_);
v_minute_960_ = lean_ctor_get(v_snd_956_, 1);
lean_inc(v_minute_960_);
lean_dec(v_snd_956_);
v___x_961_ = l_Lake_Date_toString(v_date_957_);
v___x_962_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_963_ = lean_string_append(v___x_961_, v___x_962_);
v___x_964_ = l_Lake_Toml_Time_toString(v_time_958_);
v___x_965_ = lean_string_append(v___x_963_, v___x_964_);
lean_dec_ref(v___x_964_);
v___x_966_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__2));
v___x_967_ = lean_string_append(v___x_965_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(2u);
v___x_969_ = l_Lake_zpad(v_hour_959_, v___x_968_);
v___x_970_ = lean_string_append(v___x_967_, v___x_969_);
lean_dec_ref(v___x_969_);
v___x_971_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_972_ = lean_string_append(v___x_970_, v___x_971_);
v___x_973_ = l_Lake_zpad(v_minute_960_, v___x_968_);
v___x_974_ = lean_string_append(v___x_972_, v___x_973_);
lean_dec_ref(v___x_973_);
return v___x_974_;
}
}
else
{
lean_object* v_date_975_; lean_object* v_time_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_date_975_ = lean_ctor_get(v_dt_932_, 0);
lean_inc_ref(v_date_975_);
v_time_976_ = lean_ctor_get(v_dt_932_, 1);
lean_inc_ref(v_time_976_);
lean_dec_ref_known(v_dt_932_, 3);
v___x_977_ = l_Lake_Date_toString(v_date_975_);
v___x_978_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
v___x_980_ = l_Lake_Toml_Time_toString(v_time_976_);
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
lean_dec_ref(v___x_980_);
v___x_982_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__3));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
return v___x_983_;
}
}
case 1:
{
lean_object* v_date_984_; lean_object* v_time_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_date_984_ = lean_ctor_get(v_dt_932_, 0);
lean_inc_ref(v_date_984_);
v_time_985_ = lean_ctor_get(v_dt_932_, 1);
lean_inc_ref(v_time_985_);
lean_dec_ref_known(v_dt_932_, 2);
v___x_986_ = l_Lake_Date_toString(v_date_984_);
v___x_987_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_988_ = lean_string_append(v___x_986_, v___x_987_);
v___x_989_ = l_Lake_Toml_Time_toString(v_time_985_);
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
lean_dec_ref(v___x_989_);
return v___x_990_;
}
case 2:
{
lean_object* v_date_991_; lean_object* v___x_992_; 
v_date_991_ = lean_ctor_get(v_dt_932_, 0);
lean_inc_ref(v_date_991_);
lean_dec_ref_known(v_dt_932_, 1);
v___x_992_ = l_Lake_Date_toString(v_date_991_);
return v___x_992_;
}
default: 
{
lean_object* v_time_993_; lean_object* v___x_994_; 
v_time_993_ = lean_ctor_get(v_dt_932_, 0);
lean_inc_ref(v_time_993_);
lean_dec_ref_known(v_dt_932_, 1);
v___x_994_ = l_Lake_Toml_Time_toString(v_time_993_);
return v___x_994_;
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
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Data_DateTime(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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

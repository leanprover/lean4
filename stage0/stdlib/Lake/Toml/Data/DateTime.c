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
lean_object* lean_obj_tag_nat(lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0;
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
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx___impl___boxed(lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0;
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
uint8_t l_Lake_Toml_instDecidableEqTime_decEq(lean_object* v_x_5_, lean_object* v_x_6_){
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
LEAN_EXPORT void l_Lake_Toml_instDecidableEqTime_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5_ = stack[0].m_obj;
lean_object* v_x_6_ = stack[1].m_obj;
uint8_t v_res_22_;
v_res_22_ = l_Lake_Toml_instDecidableEqTime_decEq(v_x_5_, v_x_6_);
stack->m_num = v_res_22_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqTime_decEq___boxed(lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Lake_Toml_instDecidableEqTime_decEq(v_x_23_, v_x_24_);
lean_dec_ref(v_x_24_);
lean_dec_ref(v_x_23_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
uint8_t l_Lake_Toml_instDecidableEqTime(lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v___x_29_; 
v___x_29_ = l_Lake_Toml_instDecidableEqTime_decEq(v_x_27_, v_x_28_);
return v___x_29_;
}
}
LEAN_EXPORT void l_Lake_Toml_instDecidableEqTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_27_ = stack[0].m_obj;
lean_object* v_x_28_ = stack[1].m_obj;
uint8_t v_res_30_;
v_res_30_ = l_Lake_Toml_instDecidableEqTime(v_x_27_, v_x_28_);
stack->m_num = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqTime___boxed(lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Lake_Toml_instDecidableEqTime(v_x_31_, v_x_32_);
lean_dec_ref(v_x_32_);
lean_dec_ref(v_x_31_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_ofValid_x3f(lean_object* v_hour_37_, lean_object* v_minute_38_, lean_object* v_second_39_){
_start:
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = lean_unsigned_to_nat(23u);
v___x_41_ = lean_nat_dec_le(v_hour_37_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_dec(v_second_39_);
lean_dec(v_minute_38_);
lean_dec(v_hour_37_);
v___x_42_ = lean_box(0);
return v___x_42_;
}
else
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(59u);
v___x_44_ = lean_nat_dec_le(v_minute_38_, v___x_43_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; 
lean_dec(v_second_39_);
lean_dec(v_minute_38_);
lean_dec(v_hour_37_);
v___x_45_ = lean_box(0);
return v___x_45_;
}
else
{
lean_object* v___x_46_; uint8_t v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(60u);
v___x_47_ = lean_nat_dec_le(v_second_39_, v___x_46_);
if (v___x_47_ == 0)
{
lean_object* v___x_48_; 
lean_dec(v_second_39_);
lean_dec(v_minute_38_);
lean_dec(v_hour_37_);
v___x_48_ = lean_box(0);
return v___x_48_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_50_, 0, v_hour_37_);
lean_ctor_set(v___x_50_, 1, v_minute_38_);
lean_ctor_set(v___x_50_, 2, v_second_39_);
lean_ctor_set(v___x_50_, 3, v___x_49_);
lean_ctor_set(v___x_50_, 4, v___x_49_);
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
return v___x_51_;
}
}
}
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_55_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_56_;
v_res_56_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg();
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg();
return v_res_58_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg();
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(lean_object* v_s_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___boxed(lean_object* v_s_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(v_s_62_);
lean_dec_ref(v_s_62_);
return v_res_63_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg(){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_65_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_66_;
v_res_66_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg();
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg___boxed(lean_object* v___dummy_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg();
return v_res_68_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg();
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(lean_object* v_s_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___boxed(lean_object* v_s_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(v_s_72_);
lean_dec_ref(v_s_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(lean_object* v_head_74_, lean_object* v_a_75_, lean_object* v_b_76_){
_start:
{
if (lean_obj_tag(v_a_75_) == 0)
{
lean_object* v_currPos_77_; lean_object* v_searcher_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_116_; 
v_currPos_77_ = lean_ctor_get(v_a_75_, 0);
v_searcher_78_ = lean_ctor_get(v_a_75_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_a_75_);
if (v_isSharedCheck_116_ == 0)
{
v___x_80_ = v_a_75_;
v_isShared_81_ = v_isSharedCheck_116_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_searcher_78_);
lean_inc(v_currPos_77_);
lean_dec(v_a_75_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_116_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v_str_82_; lean_object* v_startInclusive_83_; lean_object* v_endExclusive_84_; lean_object* v_it_86_; lean_object* v_startInclusive_87_; lean_object* v_endExclusive_88_; lean_object* v___x_94_; uint8_t v_decide_95_; 
v_str_82_ = lean_ctor_get(v_head_74_, 0);
v_startInclusive_83_ = lean_ctor_get(v_head_74_, 1);
v_endExclusive_84_ = lean_ctor_get(v_head_74_, 2);
v___x_94_ = lean_nat_sub(v_endExclusive_84_, v_startInclusive_83_);
v_decide_95_ = lean_nat_dec_eq(v_searcher_78_, v___x_94_);
if (v_decide_95_ == 0)
{
uint32_t v___x_96_; lean_object* v___x_97_; uint32_t v___x_98_; uint8_t v___x_99_; 
lean_dec(v___x_94_);
v___x_96_ = 46;
v___x_97_ = lean_nat_add(v_startInclusive_83_, v_searcher_78_);
v___x_98_ = lean_string_utf8_get_fast(v_str_82_, v___x_97_);
v___x_99_ = lean_uint32_dec_eq(v___x_98_, v___x_96_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
lean_dec(v_searcher_78_);
v___x_100_ = lean_string_utf8_next_fast(v_str_82_, v___x_97_);
lean_dec(v___x_97_);
v___x_101_ = lean_nat_sub(v___x_100_, v_startInclusive_83_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v___x_101_);
v___x_103_ = v___x_80_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_currPos_77_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_101_);
v___x_103_ = v_reuseFailAlloc_105_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
v_a_75_ = v___x_103_;
goto _start;
}
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v_slice_109_; lean_object* v_nextIt_111_; 
v___x_106_ = lean_string_utf8_next_fast(v_str_82_, v___x_97_);
v___x_107_ = lean_nat_sub(v___x_106_, v___x_97_);
lean_dec(v___x_97_);
v___x_108_ = lean_nat_add(v_searcher_78_, v___x_107_);
lean_dec(v___x_107_);
v_slice_109_ = l_String_Slice_subslice_x21(v_head_74_, v_currPos_77_, v_searcher_78_);
lean_inc(v___x_108_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 1, v___x_108_);
lean_ctor_set(v___x_80_, 0, v___x_108_);
v_nextIt_111_ = v___x_80_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_108_);
v_nextIt_111_ = v_reuseFailAlloc_114_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v_startInclusive_112_; lean_object* v_endExclusive_113_; 
v_startInclusive_112_ = lean_ctor_get(v_slice_109_, 0);
lean_inc(v_startInclusive_112_);
v_endExclusive_113_ = lean_ctor_get(v_slice_109_, 1);
lean_inc(v_endExclusive_113_);
lean_dec_ref(v_slice_109_);
v_it_86_ = v_nextIt_111_;
v_startInclusive_87_ = v_startInclusive_112_;
v_endExclusive_88_ = v_endExclusive_113_;
goto v___jp_85_;
}
}
}
else
{
lean_object* v___x_115_; 
lean_del_object(v___x_80_);
lean_dec(v_searcher_78_);
v___x_115_ = lean_box(1);
v_it_86_ = v___x_115_;
v_startInclusive_87_ = v_currPos_77_;
v_endExclusive_88_ = v___x_94_;
goto v___jp_85_;
}
v___jp_85_:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = lean_nat_add(v_startInclusive_83_, v_startInclusive_87_);
lean_dec(v_startInclusive_87_);
v___x_90_ = lean_nat_add(v_startInclusive_83_, v_endExclusive_88_);
lean_dec(v_endExclusive_88_);
lean_inc_ref(v_str_82_);
v___x_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_91_, 0, v_str_82_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
v___x_92_ = lean_array_push(v_b_76_, v___x_91_);
v_a_75_ = v_it_86_;
v_b_76_ = v___x_92_;
goto _start;
}
}
}
else
{
return v_b_76_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg___boxed(lean_object* v_head_117_, lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_117_, v_a_118_, v_b_119_);
lean_dec_ref(v_head_117_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(lean_object* v_t_121_, lean_object* v___x_122_, lean_object* v___x_123_, lean_object* v_a_124_, lean_object* v_b_125_){
_start:
{
lean_object* v_it_127_; lean_object* v_startInclusive_128_; lean_object* v_endExclusive_129_; 
if (lean_obj_tag(v_a_124_) == 0)
{
lean_object* v_currPos_133_; lean_object* v_searcher_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_157_; 
v_currPos_133_ = lean_ctor_get(v_a_124_, 0);
v_searcher_134_ = lean_ctor_get(v_a_124_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_a_124_);
if (v_isSharedCheck_157_ == 0)
{
v___x_136_ = v_a_124_;
v_isShared_137_ = v_isSharedCheck_157_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_searcher_134_);
lean_inc(v_currPos_133_);
lean_dec(v_a_124_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_157_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
uint8_t v_decide_138_; 
v_decide_138_ = lean_nat_dec_eq(v_searcher_134_, v___x_123_);
if (v_decide_138_ == 0)
{
uint32_t v___x_139_; uint32_t v___x_140_; uint8_t v___x_141_; 
v___x_139_ = 58;
v___x_140_ = lean_string_utf8_get_fast(v_t_121_, v_searcher_134_);
v___x_141_ = lean_uint32_dec_eq(v___x_140_, v___x_139_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_144_; 
v___x_142_ = lean_string_utf8_next_fast(v_t_121_, v_searcher_134_);
lean_dec(v_searcher_134_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_142_);
v___x_144_ = v___x_136_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_currPos_133_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_142_);
v___x_144_ = v_reuseFailAlloc_146_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
v_a_124_ = v___x_144_;
goto _start;
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_slice_150_; lean_object* v_nextIt_152_; 
v___x_147_ = lean_string_utf8_next_fast(v_t_121_, v_searcher_134_);
v___x_148_ = lean_nat_sub(v___x_147_, v_searcher_134_);
v___x_149_ = lean_nat_add(v_searcher_134_, v___x_148_);
lean_dec(v___x_148_);
v_slice_150_ = l_String_Slice_subslice_x21(v___x_122_, v_currPos_133_, v_searcher_134_);
lean_inc(v___x_149_);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 1, v___x_149_);
lean_ctor_set(v___x_136_, 0, v___x_149_);
v_nextIt_152_ = v___x_136_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v___x_149_);
v_nextIt_152_ = v_reuseFailAlloc_155_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v_startInclusive_153_; lean_object* v_endExclusive_154_; 
v_startInclusive_153_ = lean_ctor_get(v_slice_150_, 0);
lean_inc(v_startInclusive_153_);
v_endExclusive_154_ = lean_ctor_get(v_slice_150_, 1);
lean_inc(v_endExclusive_154_);
lean_dec_ref(v_slice_150_);
v_it_127_ = v_nextIt_152_;
v_startInclusive_128_ = v_startInclusive_153_;
v_endExclusive_129_ = v_endExclusive_154_;
goto v___jp_126_;
}
}
}
else
{
lean_object* v___x_156_; 
lean_del_object(v___x_136_);
lean_dec(v_searcher_134_);
v___x_156_ = lean_box(1);
lean_inc(v___x_123_);
v_it_127_ = v___x_156_;
v_startInclusive_128_ = v_currPos_133_;
v_endExclusive_129_ = v___x_123_;
goto v___jp_126_;
}
}
}
else
{
lean_dec(v___x_123_);
lean_dec_ref(v_t_121_);
return v_b_125_;
}
v___jp_126_:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_inc_ref(v_t_121_);
v___x_130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_130_, 0, v_t_121_);
lean_ctor_set(v___x_130_, 1, v_startInclusive_128_);
lean_ctor_set(v___x_130_, 2, v_endExclusive_129_);
v___x_131_ = lean_array_push(v_b_125_, v___x_130_);
v_a_124_ = v_it_127_;
v_b_125_ = v___x_131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg___boxed(lean_object* v_t_158_, lean_object* v___x_159_, lean_object* v___x_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_158_, v___x_159_, v___x_160_, v_a_161_, v_b_162_);
lean_dec_ref(v___x_159_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(lean_object* v_head_164_, lean_object* v_a_165_, lean_object* v_b_166_){
_start:
{
lean_object* v_str_167_; lean_object* v_startInclusive_168_; lean_object* v_endExclusive_169_; lean_object* v___x_170_; uint8_t v_decide_171_; 
v_str_167_ = lean_ctor_get(v_head_164_, 0);
v_startInclusive_168_ = lean_ctor_get(v_head_164_, 1);
v_endExclusive_169_ = lean_ctor_get(v_head_164_, 2);
v___x_170_ = lean_nat_sub(v_endExclusive_169_, v_startInclusive_168_);
v_decide_171_ = lean_nat_dec_eq(v_a_165_, v___x_170_);
lean_dec(v___x_170_);
if (v_decide_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_172_ = lean_nat_add(v_startInclusive_168_, v_a_165_);
lean_dec(v_a_165_);
v___x_173_ = lean_string_utf8_next_fast(v_str_167_, v___x_172_);
lean_dec(v___x_172_);
v___x_174_ = lean_nat_sub(v___x_173_, v_startInclusive_168_);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_add(v_b_166_, v___x_175_);
lean_dec(v_b_166_);
v_a_165_ = v___x_174_;
v_b_166_ = v___x_176_;
goto _start;
}
else
{
lean_dec(v_a_165_);
return v_b_166_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg___boxed(lean_object* v_head_178_, lean_object* v_a_179_, lean_object* v_b_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_178_, v_a_179_, v_b_180_);
lean_dec_ref(v_head_178_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_ofString_x3f(lean_object* v_t_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = lean_string_utf8_byte_size(v_t_184_);
lean_inc_ref(v_t_184_);
v___x_187_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_187_, 0, v_t_184_);
lean_ctor_set(v___x_187_, 1, v___x_185_);
lean_ctor_set(v___x_187_, 2, v___x_186_);
v___x_188_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0);
v___x_189_ = ((lean_object*)(l_Lake_Toml_Time_ofString_x3f___closed__0));
v___x_190_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_184_, v___x_187_, v___x_186_, v___x_188_, v___x_189_);
lean_dec_ref_known(v___x_187_, 3);
v___x_191_ = lean_array_to_list(v___x_190_);
if (lean_obj_tag(v___x_191_) == 1)
{
lean_object* v_tail_192_; 
v_tail_192_ = lean_ctor_get(v___x_191_, 1);
lean_inc(v_tail_192_);
if (lean_obj_tag(v_tail_192_) == 1)
{
lean_object* v_tail_193_; 
v_tail_193_ = lean_ctor_get(v_tail_192_, 1);
if (lean_obj_tag(v_tail_193_) == 0)
{
lean_object* v_head_194_; lean_object* v_head_195_; lean_object* v___x_196_; 
v_head_194_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_head_194_);
lean_dec_ref_known(v___x_191_, 2);
v_head_195_ = lean_ctor_get(v_tail_192_, 0);
lean_inc(v_head_195_);
lean_dec_ref_known(v_tail_192_, 2);
v___x_196_ = l_String_Slice_toNat_x3f(v_head_194_);
lean_dec(v_head_194_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v___x_197_; 
lean_dec(v_head_195_);
v___x_197_ = lean_box(0);
return v___x_197_;
}
else
{
lean_object* v_val_198_; lean_object* v___x_199_; 
v_val_198_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_val_198_);
lean_dec_ref_known(v___x_196_, 1);
v___x_199_ = l_String_Slice_toNat_x3f(v_head_195_);
lean_dec(v_head_195_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; 
lean_dec(v_val_198_);
v___x_200_ = lean_box(0);
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v___x_202_; 
v_val_201_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v___x_199_, 1);
v___x_202_ = l_Lake_Toml_Time_ofValid_x3f(v_val_198_, v_val_201_, v___x_185_);
return v___x_202_;
}
}
}
else
{
lean_object* v_tail_203_; 
lean_inc_ref(v_tail_193_);
v_tail_203_ = lean_ctor_get(v_tail_193_, 1);
if (lean_obj_tag(v_tail_203_) == 0)
{
lean_object* v_head_204_; lean_object* v_head_205_; lean_object* v_head_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v_head_204_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_head_204_);
lean_dec_ref_known(v___x_191_, 2);
v_head_205_ = lean_ctor_get(v_tail_192_, 0);
lean_inc(v_head_205_);
lean_dec_ref_known(v_tail_192_, 2);
v_head_206_ = lean_ctor_get(v_tail_193_, 0);
lean_inc(v_head_206_);
lean_dec_ref_known(v_tail_193_, 2);
v___x_207_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0);
v___x_208_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_206_, v___x_207_, v___x_189_);
lean_dec(v_head_206_);
v___x_209_ = lean_array_to_list(v___x_208_);
if (lean_obj_tag(v___x_209_) == 1)
{
lean_object* v_tail_210_; 
v_tail_210_ = lean_ctor_get(v___x_209_, 1);
if (lean_obj_tag(v_tail_210_) == 0)
{
lean_object* v_head_211_; lean_object* v___x_212_; 
v_head_211_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_head_211_);
lean_dec_ref_known(v___x_209_, 2);
v___x_212_ = l_String_Slice_toNat_x3f(v_head_204_);
lean_dec(v_head_204_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v___x_213_; 
lean_dec(v_head_211_);
lean_dec(v_head_205_);
v___x_213_ = lean_box(0);
return v___x_213_;
}
else
{
lean_object* v_val_214_; lean_object* v___x_215_; 
v_val_214_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_val_214_);
lean_dec_ref_known(v___x_212_, 1);
v___x_215_ = l_String_Slice_toNat_x3f(v_head_205_);
lean_dec(v_head_205_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v___x_216_; 
lean_dec(v_val_214_);
lean_dec(v_head_211_);
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v_val_217_; lean_object* v___x_218_; 
v_val_217_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v___x_215_, 1);
v___x_218_ = l_String_Slice_toNat_x3f(v_head_211_);
lean_dec(v_head_211_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v___x_219_; 
lean_dec(v_val_217_);
lean_dec(v_val_214_);
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v_val_220_; lean_object* v___x_221_; 
v_val_220_ = lean_ctor_get(v___x_218_, 0);
lean_inc(v_val_220_);
lean_dec_ref_known(v___x_218_, 1);
v___x_221_ = l_Lake_Toml_Time_ofValid_x3f(v_val_214_, v_val_217_, v_val_220_);
return v___x_221_;
}
}
}
}
else
{
lean_object* v_tail_222_; 
lean_inc_ref(v_tail_210_);
v_tail_222_ = lean_ctor_get(v_tail_210_, 1);
if (lean_obj_tag(v_tail_222_) == 0)
{
lean_object* v_head_223_; lean_object* v_head_224_; lean_object* v___x_225_; 
v_head_223_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_head_223_);
lean_dec_ref_known(v___x_209_, 2);
v_head_224_ = lean_ctor_get(v_tail_210_, 0);
lean_inc(v_head_224_);
lean_dec_ref_known(v_tail_210_, 2);
v___x_225_ = l_String_Slice_toNat_x3f(v_head_204_);
lean_dec(v_head_204_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v___x_226_; 
lean_dec(v_head_224_);
lean_dec(v_head_223_);
lean_dec(v_head_205_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
lean_object* v_val_227_; lean_object* v___x_228_; 
v_val_227_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_225_, 1);
v___x_228_ = l_String_Slice_toNat_x3f(v_head_205_);
lean_dec(v_head_205_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v___x_229_; 
lean_dec(v_val_227_);
lean_dec(v_head_224_);
lean_dec(v_head_223_);
v___x_229_ = lean_box(0);
return v___x_229_;
}
else
{
lean_object* v_val_230_; lean_object* v___x_231_; 
v_val_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_val_230_);
lean_dec_ref_known(v___x_228_, 1);
v___x_231_ = l_String_Slice_toNat_x3f(v_head_223_);
lean_dec(v_head_223_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; 
lean_dec(v_val_230_);
lean_dec(v_val_227_);
lean_dec(v_head_224_);
v___x_232_ = lean_box(0);
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_234_; 
v_val_233_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v___x_231_, 1);
v___x_234_ = l_Lake_Toml_Time_ofValid_x3f(v_val_227_, v_val_230_, v_val_233_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_dec(v_head_224_);
return v___x_234_;
}
else
{
lean_object* v_val_235_; lean_object* v___x_236_; 
v_val_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v___x_234_, 1);
v___x_236_ = l_String_Slice_toNat_x3f(v_head_224_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; 
lean_dec(v_val_235_);
lean_dec(v_head_224_);
v___x_237_ = lean_box(0);
return v___x_237_;
}
else
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_260_; 
v_val_238_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_260_ == 0)
{
v___x_240_ = v___x_236_;
v_isShared_241_ = v_isSharedCheck_260_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v___x_236_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_260_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_hour_242_; lean_object* v_minute_243_; lean_object* v_second_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_257_; 
v_hour_242_ = lean_ctor_get(v_val_235_, 0);
v_minute_243_ = lean_ctor_get(v_val_235_, 1);
v_second_244_ = lean_ctor_get(v_val_235_, 2);
v_isSharedCheck_257_ = !lean_is_exclusive(v_val_235_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; lean_object* v_unused_259_; 
v_unused_258_ = lean_ctor_get(v_val_235_, 4);
lean_dec(v_unused_258_);
v_unused_259_ = lean_ctor_get(v_val_235_, 3);
lean_dec(v_unused_259_);
v___x_246_ = v_val_235_;
v_isShared_247_ = v_isSharedCheck_257_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_second_244_);
lean_inc(v_minute_243_);
lean_inc(v_hour_242_);
lean_dec(v_val_235_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_257_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_248_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_224_, v___x_185_, v___x_185_);
lean_dec(v_head_224_);
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_sub(v___x_248_, v___x_249_);
lean_dec(v___x_248_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 4, v_val_238_);
lean_ctor_set(v___x_246_, 3, v___x_250_);
v___x_252_ = v___x_246_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_hour_242_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_minute_243_);
lean_ctor_set(v_reuseFailAlloc_256_, 2, v_second_244_);
lean_ctor_set(v_reuseFailAlloc_256_, 3, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_256_, 4, v_val_238_);
v___x_252_ = v_reuseFailAlloc_256_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_252_);
v___x_254_ = v___x_240_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
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
lean_object* v___x_261_; 
lean_dec_ref_known(v_tail_210_, 2);
lean_dec_ref_known(v___x_209_, 2);
lean_dec(v_head_205_);
lean_dec(v_head_204_);
v___x_261_ = lean_box(0);
return v___x_261_;
}
}
}
else
{
lean_object* v___x_262_; 
lean_dec(v___x_209_);
lean_dec(v_head_205_);
lean_dec(v_head_204_);
v___x_262_ = lean_box(0);
return v___x_262_;
}
}
else
{
lean_object* v___x_263_; 
lean_dec_ref_known(v_tail_193_, 2);
lean_dec_ref_known(v_tail_192_, 2);
lean_dec_ref_known(v___x_191_, 2);
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
}
else
{
lean_object* v___x_264_; 
lean_dec(v_tail_192_);
lean_dec_ref_known(v___x_191_, 2);
v___x_264_ = lean_box(0);
return v___x_264_;
}
}
else
{
lean_object* v___x_265_; 
lean_dec(v___x_191_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(lean_object* v_t_266_, lean_object* v___x_267_, lean_object* v___x_268_, lean_object* v_inst_269_, lean_object* v_R_270_, lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_266_, v___x_267_, v___x_268_, v_a_271_, v_b_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___boxed(lean_object* v_t_274_, lean_object* v___x_275_, lean_object* v___x_276_, lean_object* v_inst_277_, lean_object* v_R_278_, lean_object* v_a_279_, lean_object* v_b_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(v_t_274_, v___x_275_, v___x_276_, v_inst_277_, v_R_278_, v_a_279_, v_b_280_);
lean_dec_ref(v___x_275_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(lean_object* v_head_282_, lean_object* v_inst_283_, lean_object* v_R_284_, lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_282_, v_a_285_, v_b_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___boxed(lean_object* v_head_288_, lean_object* v_inst_289_, lean_object* v_R_290_, lean_object* v_a_291_, lean_object* v_b_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(v_head_288_, v_inst_289_, v_R_290_, v_a_291_, v_b_292_);
lean_dec_ref(v_head_288_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(lean_object* v_head_294_, lean_object* v_inst_295_, lean_object* v_R_296_, lean_object* v_a_297_, lean_object* v_b_298_, lean_object* v_c_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_294_, v_a_297_, v_b_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___boxed(lean_object* v_head_301_, lean_object* v_inst_302_, lean_object* v_R_303_, lean_object* v_a_304_, lean_object* v_b_305_, lean_object* v_c_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(v_head_301_, v_inst_302_, v_R_303_, v_a_304_, v_b_305_, v_c_306_);
lean_dec_ref(v_head_301_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_toString(lean_object* v_t_310_){
_start:
{
lean_object* v_hour_311_; lean_object* v_minute_312_; lean_object* v_second_313_; lean_object* v_fracExponent_314_; lean_object* v_fracMantissa_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v_s_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_hour_311_ = lean_ctor_get(v_t_310_, 0);
lean_inc(v_hour_311_);
v_minute_312_ = lean_ctor_get(v_t_310_, 1);
lean_inc(v_minute_312_);
v_second_313_ = lean_ctor_get(v_t_310_, 2);
lean_inc(v_second_313_);
v_fracExponent_314_ = lean_ctor_get(v_t_310_, 3);
lean_inc(v_fracExponent_314_);
v_fracMantissa_315_ = lean_ctor_get(v_t_310_, 4);
lean_inc(v_fracMantissa_315_);
lean_dec_ref(v_t_310_);
v___x_316_ = lean_unsigned_to_nat(2u);
v___x_317_ = l_Lake_zpad(v_hour_311_, v___x_316_);
v___x_318_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_319_ = lean_string_append(v___x_317_, v___x_318_);
v___x_320_ = l_Lake_zpad(v_minute_312_, v___x_316_);
v___x_321_ = lean_string_append(v___x_319_, v___x_320_);
lean_dec_ref(v___x_320_);
v___x_322_ = lean_string_append(v___x_321_, v___x_318_);
v___x_323_ = l_Lake_zpad(v_second_313_, v___x_316_);
v_s_324_ = lean_string_append(v___x_322_, v___x_323_);
lean_dec_ref(v___x_323_);
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_nat_dec_eq(v_fracMantissa_315_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; uint32_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_327_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__1));
v___x_328_ = lean_string_append(v_s_324_, v___x_327_);
v___x_329_ = l_Lake_zpad(v_fracMantissa_315_, v_fracExponent_314_);
lean_dec(v_fracExponent_314_);
v___x_330_ = 48;
v___x_331_ = lean_unsigned_to_nat(3u);
v___x_332_ = l_Lake_rpadAscii(v___x_329_, v___x_330_, v___x_331_);
v___x_333_ = lean_string_append(v___x_328_, v___x_332_);
lean_dec_ref(v___x_332_);
return v___x_333_;
}
else
{
lean_dec(v_fracMantissa_315_);
lean_dec(v_fracExponent_314_);
return v_s_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx___impl(lean_object* v_x_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_obj_tag_nat(v_x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx___impl___boxed(lean_object* v_x_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lake_Toml_DateTime_ctorIdx___impl(v_x_338_);
lean_dec_ref(v_x_338_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___redArg(lean_object* v_t_340_, lean_object* v_k_341_){
_start:
{
switch(lean_obj_tag(v_t_340_))
{
case 0:
{
lean_object* v_date_342_; lean_object* v_time_343_; lean_object* v_offset_x3f_344_; lean_object* v___x_345_; 
v_date_342_ = lean_ctor_get(v_t_340_, 0);
lean_inc_ref(v_date_342_);
v_time_343_ = lean_ctor_get(v_t_340_, 1);
lean_inc_ref(v_time_343_);
v_offset_x3f_344_ = lean_ctor_get(v_t_340_, 2);
lean_inc(v_offset_x3f_344_);
lean_dec_ref_known(v_t_340_, 3);
v___x_345_ = lean_apply_3(v_k_341_, v_date_342_, v_time_343_, v_offset_x3f_344_);
return v___x_345_;
}
case 1:
{
lean_object* v_date_346_; lean_object* v_time_347_; lean_object* v___x_348_; 
v_date_346_ = lean_ctor_get(v_t_340_, 0);
lean_inc_ref(v_date_346_);
v_time_347_ = lean_ctor_get(v_t_340_, 1);
lean_inc_ref(v_time_347_);
lean_dec_ref_known(v_t_340_, 2);
v___x_348_ = lean_apply_2(v_k_341_, v_date_346_, v_time_347_);
return v___x_348_;
}
default: 
{
lean_object* v_date_349_; lean_object* v___x_350_; 
v_date_349_ = lean_ctor_get(v_t_340_, 0);
lean_inc_ref(v_date_349_);
lean_dec_ref(v_t_340_);
v___x_350_ = lean_apply_1(v_k_341_, v_date_349_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim(lean_object* v_motive_351_, lean_object* v_ctorIdx_352_, lean_object* v_t_353_, lean_object* v_h_354_, lean_object* v_k_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_353_, v_k_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___boxed(lean_object* v_motive_357_, lean_object* v_ctorIdx_358_, lean_object* v_t_359_, lean_object* v_h_360_, lean_object* v_k_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lake_Toml_DateTime_ctorElim(v_motive_357_, v_ctorIdx_358_, v_t_359_, v_h_360_, v_k_361_);
lean_dec(v_ctorIdx_358_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim___redArg(lean_object* v_t_363_, lean_object* v_offsetDateTime_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_363_, v_offsetDateTime_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim(lean_object* v_motive_366_, lean_object* v_t_367_, lean_object* v_h_368_, lean_object* v_offsetDateTime_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_367_, v_offsetDateTime_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim___redArg(lean_object* v_t_371_, lean_object* v_localDateTime_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_371_, v_localDateTime_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim(lean_object* v_motive_374_, lean_object* v_t_375_, lean_object* v_h_376_, lean_object* v_localDateTime_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_375_, v_localDateTime_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim___redArg(lean_object* v_t_379_, lean_object* v_localDate_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_379_, v_localDate_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim(lean_object* v_motive_382_, lean_object* v_t_383_, lean_object* v_h_384_, lean_object* v_localDate_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_383_, v_localDate_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim___redArg(lean_object* v_t_387_, lean_object* v_localTime_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_387_, v_localTime_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim(lean_object* v_motive_390_, lean_object* v_t_391_, lean_object* v_h_392_, lean_object* v_localTime_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_391_, v_localTime_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = lean_box(0);
v___x_396_ = ((lean_object*)(l_Lake_Toml_instInhabitedTime_default));
v___x_397_ = l_Lake_instInhabitedDate_default;
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___x_395_);
return v___x_398_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime_default(void){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = lean_obj_once(&l_Lake_Toml_instInhabitedDateTime_default___closed__0, &l_Lake_Toml_instInhabitedDateTime_default___closed__0_once, _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0);
return v___x_399_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime(void){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lake_Toml_instInhabitedDateTime_default;
return v___x_400_;
}
}
uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(uint8_t v___x_401_, uint8_t v___y_402_, uint8_t v___y_403_){
_start:
{
if (v___y_403_ == 0)
{
if (v___y_402_ == 0)
{
return v___x_401_;
}
else
{
return v___y_403_;
}
}
else
{
return v___y_402_;
}
}
}
LEAN_EXPORT void l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_401_ = stack[0].m_num;
uint8_t v___y_402_ = stack[1].m_num;
uint8_t v___y_403_ = stack[2].m_num;
uint8_t v_res_404_;
v_res_404_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(v___x_401_, v___y_402_, v___y_403_);
stack->m_num = v_res_404_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed(lean_object* v___x_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
uint8_t v___x_876__boxed_408_; uint8_t v___y_877__boxed_409_; uint8_t v___y_878__boxed_410_; uint8_t v_res_411_; lean_object* v_r_412_; 
v___x_876__boxed_408_ = lean_unbox(v___x_405_);
v___y_877__boxed_409_ = lean_unbox(v___y_406_);
v___y_878__boxed_410_ = lean_unbox(v___y_407_);
v_res_411_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(v___x_876__boxed_408_, v___y_877__boxed_409_, v___y_878__boxed_410_);
v_r_412_ = lean_box(v_res_411_);
return v_r_412_;
}
}
uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(lean_object* v___f_413_, lean_object* v_a_414_, lean_object* v_b_415_){
_start:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqTime___boxed), 2, 0);
v___x_417_ = l_instDecidableEqProd___redArg(v___f_413_, v___x_416_, v_a_414_, v_b_415_);
return v___x_417_;
}
}
LEAN_EXPORT void l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_413_ = stack[0].m_obj;
lean_object* v_a_414_ = stack[1].m_obj;
lean_object* v_b_415_ = stack[2].m_obj;
uint8_t v_res_418_;
v_res_418_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(v___f_413_, v_a_414_, v_b_415_);
stack->m_num = v_res_418_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed(lean_object* v___f_419_, lean_object* v_a_420_, lean_object* v_b_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(v___f_419_, v_a_420_, v_b_421_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq(lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
switch(lean_obj_tag(v_x_424_))
{
case 0:
{
if (lean_obj_tag(v_x_425_) == 0)
{
lean_object* v_date_426_; lean_object* v_time_427_; lean_object* v_offset_x3f_428_; lean_object* v_date_429_; lean_object* v_time_430_; lean_object* v_offset_x3f_431_; uint8_t v___x_432_; 
v_date_426_ = lean_ctor_get(v_x_424_, 0);
lean_inc_ref(v_date_426_);
v_time_427_ = lean_ctor_get(v_x_424_, 1);
lean_inc_ref(v_time_427_);
v_offset_x3f_428_ = lean_ctor_get(v_x_424_, 2);
lean_inc(v_offset_x3f_428_);
lean_dec_ref_known(v_x_424_, 3);
v_date_429_ = lean_ctor_get(v_x_425_, 0);
lean_inc_ref(v_date_429_);
v_time_430_ = lean_ctor_get(v_x_425_, 1);
lean_inc_ref(v_time_430_);
v_offset_x3f_431_ = lean_ctor_get(v_x_425_, 2);
lean_inc(v_offset_x3f_431_);
lean_dec_ref_known(v_x_425_, 3);
v___x_432_ = l_Lake_instDecidableEqDate_decEq(v_date_426_, v_date_429_);
lean_dec_ref(v_date_429_);
lean_dec_ref(v_date_426_);
if (v___x_432_ == 0)
{
lean_dec(v_offset_x3f_431_);
lean_dec_ref(v_time_430_);
lean_dec(v_offset_x3f_428_);
lean_dec_ref(v_time_427_);
return v___x_432_;
}
else
{
uint8_t v___x_433_; 
v___x_433_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_427_, v_time_430_);
lean_dec_ref(v_time_430_);
lean_dec_ref(v_time_427_);
if (v___x_433_ == 0)
{
lean_dec(v_offset_x3f_431_);
lean_dec(v_offset_x3f_428_);
return v___x_433_;
}
else
{
lean_object* v___x_434_; lean_object* v___f_435_; lean_object* v___f_436_; uint8_t v___x_437_; 
v___x_434_ = lean_box(v___x_433_);
v___f_435_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed), 3, 1);
lean_closure_set(v___f_435_, 0, v___x_434_);
v___f_436_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed), 3, 1);
lean_closure_set(v___f_436_, 0, v___f_435_);
v___x_437_ = l_Option_instDecidableEq___redArg(v___f_436_, v_offset_x3f_428_, v_offset_x3f_431_);
return v___x_437_;
}
}
}
else
{
uint8_t v___x_438_; 
lean_dec_ref_known(v_x_424_, 3);
lean_dec_ref(v_x_425_);
v___x_438_ = 0;
return v___x_438_;
}
}
case 1:
{
if (lean_obj_tag(v_x_425_) == 1)
{
lean_object* v_date_439_; lean_object* v_time_440_; lean_object* v_date_441_; lean_object* v_time_442_; uint8_t v___x_443_; 
v_date_439_ = lean_ctor_get(v_x_424_, 0);
lean_inc_ref(v_date_439_);
v_time_440_ = lean_ctor_get(v_x_424_, 1);
lean_inc_ref(v_time_440_);
lean_dec_ref_known(v_x_424_, 2);
v_date_441_ = lean_ctor_get(v_x_425_, 0);
lean_inc_ref(v_date_441_);
v_time_442_ = lean_ctor_get(v_x_425_, 1);
lean_inc_ref(v_time_442_);
lean_dec_ref_known(v_x_425_, 2);
v___x_443_ = l_Lake_instDecidableEqDate_decEq(v_date_439_, v_date_441_);
lean_dec_ref(v_date_441_);
lean_dec_ref(v_date_439_);
if (v___x_443_ == 0)
{
lean_dec_ref(v_time_442_);
lean_dec_ref(v_time_440_);
return v___x_443_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_440_, v_time_442_);
lean_dec_ref(v_time_442_);
lean_dec_ref(v_time_440_);
return v___x_444_;
}
}
else
{
uint8_t v___x_445_; 
lean_dec_ref_known(v_x_424_, 2);
lean_dec_ref(v_x_425_);
v___x_445_ = 0;
return v___x_445_;
}
}
case 2:
{
if (lean_obj_tag(v_x_425_) == 2)
{
lean_object* v_date_446_; lean_object* v_date_447_; uint8_t v___x_448_; 
v_date_446_ = lean_ctor_get(v_x_424_, 0);
lean_inc_ref(v_date_446_);
lean_dec_ref_known(v_x_424_, 1);
v_date_447_ = lean_ctor_get(v_x_425_, 0);
lean_inc_ref(v_date_447_);
lean_dec_ref_known(v_x_425_, 1);
v___x_448_ = l_Lake_instDecidableEqDate_decEq(v_date_446_, v_date_447_);
lean_dec_ref(v_date_447_);
lean_dec_ref(v_date_446_);
return v___x_448_;
}
else
{
uint8_t v___x_449_; 
lean_dec_ref_known(v_x_424_, 1);
lean_dec_ref(v_x_425_);
v___x_449_ = 0;
return v___x_449_;
}
}
default: 
{
if (lean_obj_tag(v_x_425_) == 3)
{
lean_object* v_time_450_; lean_object* v_time_451_; uint8_t v___x_452_; 
v_time_450_ = lean_ctor_get(v_x_424_, 0);
lean_inc_ref(v_time_450_);
lean_dec_ref_known(v_x_424_, 1);
v_time_451_ = lean_ctor_get(v_x_425_, 0);
lean_inc_ref(v_time_451_);
lean_dec_ref_known(v_x_425_, 1);
v___x_452_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_450_, v_time_451_);
lean_dec_ref(v_time_451_);
lean_dec_ref(v_time_450_);
return v___x_452_;
}
else
{
uint8_t v___x_453_; 
lean_dec_ref_known(v_x_424_, 1);
lean_dec_ref(v_x_425_);
v___x_453_ = 0;
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Toml_instDecidableEqDateTime_decEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_424_ = stack[0].m_obj;
lean_object* v_x_425_ = stack[1].m_obj;
uint8_t v_res_454_;
v_res_454_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_424_, v_x_425_);
stack->m_num = v_res_454_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___boxed(lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_455_, v_x_456_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
uint8_t l_Lake_Toml_instDecidableEqDateTime(lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_459_, v_x_460_);
return v___x_461_;
}
}
LEAN_EXPORT void l_Lake_Toml_instDecidableEqDateTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_459_ = stack[0].m_obj;
lean_object* v_x_460_ = stack[1].m_obj;
uint8_t v_res_462_;
v_res_462_ = l_Lake_Toml_instDecidableEqDateTime(v_x_459_, v_x_460_);
stack->m_num = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime___boxed(lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
uint8_t v_res_465_; lean_object* v_r_466_; 
v_res_465_ = l_Lake_Toml_instDecidableEqDateTime(v_x_463_, v_x_464_);
v_r_466_ = lean_box(v_res_465_);
return v_r_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeDateDateTime___lam__0(lean_object* v_date_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_468_, 0, v_date_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeTimeDateTime___lam__0(lean_object* v_time_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_472_, 0, v_time_471_);
return v___x_472_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg___closed__0));
return v___x_478_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_479_;
v_res_479_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg();
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg();
return v_res_481_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg();
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(lean_object* v_s_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___boxed(lean_object* v_s_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(v_s_485_);
lean_dec_ref(v_s_485_);
return v_res_486_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg(){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_488_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_489_;
v_res_489_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg();
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg___boxed(lean_object* v___dummy_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg();
return v_res_491_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0(void){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg();
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(lean_object* v_s_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___boxed(lean_object* v_s_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(v_s_495_);
lean_dec_ref(v_s_495_);
return v_res_496_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg(){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_498_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_499_;
v_res_499_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg();
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg___boxed(lean_object* v___dummy_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg();
return v_res_501_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0(void){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg();
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(lean_object* v_s_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___boxed(lean_object* v_s_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(v_s_505_);
lean_dec_ref(v_s_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(lean_object* v_head_507_, lean_object* v_a_508_, lean_object* v_b_509_){
_start:
{
if (lean_obj_tag(v_a_508_) == 0)
{
lean_object* v_currPos_510_; lean_object* v_searcher_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_550_; 
v_currPos_510_ = lean_ctor_get(v_a_508_, 0);
v_searcher_511_ = lean_ctor_get(v_a_508_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_a_508_);
if (v_isSharedCheck_550_ == 0)
{
v___x_513_ = v_a_508_;
v_isShared_514_ = v_isSharedCheck_550_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_searcher_511_);
lean_inc(v_currPos_510_);
lean_dec(v_a_508_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_550_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_str_515_; lean_object* v_startInclusive_516_; lean_object* v_endExclusive_517_; lean_object* v_it_519_; lean_object* v_startInclusive_520_; lean_object* v_endExclusive_521_; lean_object* v___x_528_; uint8_t v_decide_529_; 
v_str_515_ = lean_ctor_get(v_head_507_, 0);
v_startInclusive_516_ = lean_ctor_get(v_head_507_, 1);
v_endExclusive_517_ = lean_ctor_get(v_head_507_, 2);
v___x_528_ = lean_nat_sub(v_endExclusive_517_, v_startInclusive_516_);
v_decide_529_ = lean_nat_dec_eq(v_searcher_511_, v___x_528_);
if (v_decide_529_ == 0)
{
uint32_t v___x_530_; lean_object* v___x_531_; uint32_t v___x_532_; uint8_t v___x_533_; 
lean_dec(v___x_528_);
v___x_530_ = 43;
v___x_531_ = lean_nat_add(v_startInclusive_516_, v_searcher_511_);
v___x_532_ = lean_string_utf8_get_fast(v_str_515_, v___x_531_);
v___x_533_ = lean_uint32_dec_eq(v___x_532_, v___x_530_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
lean_dec(v_searcher_511_);
v___x_534_ = lean_string_utf8_next_fast(v_str_515_, v___x_531_);
lean_dec(v___x_531_);
v___x_535_ = lean_nat_sub(v___x_534_, v_startInclusive_516_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v___x_535_);
v___x_537_ = v___x_513_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_currPos_510_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_535_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
v_a_508_ = v___x_537_;
goto _start;
}
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_slice_543_; lean_object* v_nextIt_545_; 
v___x_540_ = lean_string_utf8_next_fast(v_str_515_, v___x_531_);
v___x_541_ = lean_nat_sub(v___x_540_, v___x_531_);
lean_dec(v___x_531_);
v___x_542_ = lean_nat_add(v_searcher_511_, v___x_541_);
lean_dec(v___x_541_);
v_slice_543_ = l_String_Slice_subslice_x21(v_head_507_, v_currPos_510_, v_searcher_511_);
lean_inc(v___x_542_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v___x_542_);
lean_ctor_set(v___x_513_, 0, v___x_542_);
v_nextIt_545_ = v___x_513_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v___x_542_);
v_nextIt_545_ = v_reuseFailAlloc_548_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v_startInclusive_546_; lean_object* v_endExclusive_547_; 
v_startInclusive_546_ = lean_ctor_get(v_slice_543_, 0);
lean_inc(v_startInclusive_546_);
v_endExclusive_547_ = lean_ctor_get(v_slice_543_, 1);
lean_inc(v_endExclusive_547_);
lean_dec_ref(v_slice_543_);
v_it_519_ = v_nextIt_545_;
v_startInclusive_520_ = v_startInclusive_546_;
v_endExclusive_521_ = v_endExclusive_547_;
goto v___jp_518_;
}
}
}
else
{
lean_object* v___x_549_; 
lean_del_object(v___x_513_);
lean_dec(v_searcher_511_);
v___x_549_ = lean_box(1);
v_it_519_ = v___x_549_;
v_startInclusive_520_ = v_currPos_510_;
v_endExclusive_521_ = v___x_528_;
goto v___jp_518_;
}
v___jp_518_:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_522_ = lean_nat_add(v_startInclusive_516_, v_startInclusive_520_);
lean_dec(v_startInclusive_520_);
v___x_523_ = lean_nat_add(v_startInclusive_516_, v_endExclusive_521_);
lean_dec(v_endExclusive_521_);
lean_inc_ref(v_str_515_);
v___x_524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_524_, 0, v_str_515_);
lean_ctor_set(v___x_524_, 1, v___x_522_);
lean_ctor_set(v___x_524_, 2, v___x_523_);
v___x_525_ = l_String_Slice_toString(v___x_524_);
lean_dec_ref_known(v___x_524_, 3);
v___x_526_ = lean_array_push(v_b_509_, v___x_525_);
v_a_508_ = v_it_519_;
v_b_509_ = v___x_526_;
goto _start;
}
}
}
else
{
return v_b_509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg___boxed(lean_object* v_head_551_, lean_object* v_a_552_, lean_object* v_b_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_551_, v_a_552_, v_b_553_);
lean_dec_ref(v_head_551_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(lean_object* v_dt_555_, lean_object* v___x_556_, lean_object* v___x_557_, lean_object* v_a_558_, lean_object* v_b_559_){
_start:
{
lean_object* v_it_561_; lean_object* v_startInclusive_562_; lean_object* v_endExclusive_563_; 
if (lean_obj_tag(v_a_558_) == 0)
{
lean_object* v_currPos_567_; lean_object* v_searcher_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_597_; 
v_currPos_567_ = lean_ctor_get(v_a_558_, 0);
v_searcher_568_ = lean_ctor_get(v_a_558_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_558_);
if (v_isSharedCheck_597_ == 0)
{
v___x_570_ = v_a_558_;
v_isShared_571_ = v_isSharedCheck_597_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_searcher_568_);
lean_inc(v_currPos_567_);
lean_dec(v_a_558_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_597_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint8_t v___y_573_; uint8_t v_decide_588_; 
v_decide_588_ = lean_nat_dec_eq(v_searcher_568_, v___x_557_);
if (v_decide_588_ == 0)
{
uint32_t v___x_589_; uint32_t v___x_590_; uint8_t v___x_591_; 
v___x_589_ = lean_string_utf8_get_fast(v_dt_555_, v_searcher_568_);
v___x_590_ = 84;
v___x_591_ = lean_uint32_dec_eq(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
uint32_t v___x_592_; uint8_t v___x_593_; 
v___x_592_ = 116;
v___x_593_ = lean_uint32_dec_eq(v___x_589_, v___x_592_);
if (v___x_593_ == 0)
{
uint32_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = 32;
v___x_595_ = lean_uint32_dec_eq(v___x_589_, v___x_594_);
v___y_573_ = v___x_595_;
goto v___jp_572_;
}
else
{
v___y_573_ = v___x_593_;
goto v___jp_572_;
}
}
else
{
v___y_573_ = v___x_591_;
goto v___jp_572_;
}
}
else
{
lean_object* v___x_596_; 
lean_del_object(v___x_570_);
lean_dec(v_searcher_568_);
v___x_596_ = lean_box(1);
lean_inc(v___x_557_);
v_it_561_ = v___x_596_;
v_startInclusive_562_ = v_currPos_567_;
v_endExclusive_563_ = v___x_557_;
goto v___jp_560_;
}
v___jp_572_:
{
if (v___y_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_574_ = lean_string_utf8_next_fast(v_dt_555_, v_searcher_568_);
lean_dec(v_searcher_568_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___x_574_);
v___x_576_ = v___x_570_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_currPos_567_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_574_);
v___x_576_ = v_reuseFailAlloc_578_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
v_a_558_ = v___x_576_;
goto _start;
}
}
else
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v_slice_582_; lean_object* v_nextIt_584_; 
v___x_579_ = lean_string_utf8_next_fast(v_dt_555_, v_searcher_568_);
v___x_580_ = lean_nat_sub(v___x_579_, v_searcher_568_);
v___x_581_ = lean_nat_add(v_searcher_568_, v___x_580_);
lean_dec(v___x_580_);
v_slice_582_ = l_String_Slice_subslice_x21(v___x_556_, v_currPos_567_, v_searcher_568_);
lean_inc(v___x_581_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___x_581_);
lean_ctor_set(v___x_570_, 0, v___x_581_);
v_nextIt_584_ = v___x_570_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_581_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___x_581_);
v_nextIt_584_ = v_reuseFailAlloc_587_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v_startInclusive_585_; lean_object* v_endExclusive_586_; 
v_startInclusive_585_ = lean_ctor_get(v_slice_582_, 0);
lean_inc(v_startInclusive_585_);
v_endExclusive_586_ = lean_ctor_get(v_slice_582_, 1);
lean_inc(v_endExclusive_586_);
lean_dec_ref(v_slice_582_);
v_it_561_ = v_nextIt_584_;
v_startInclusive_562_ = v_startInclusive_585_;
v_endExclusive_563_ = v_endExclusive_586_;
goto v___jp_560_;
}
}
}
}
}
else
{
lean_dec(v___x_557_);
lean_dec_ref(v_dt_555_);
return v_b_559_;
}
v___jp_560_:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
lean_inc_ref(v_dt_555_);
v___x_564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_564_, 0, v_dt_555_);
lean_ctor_set(v___x_564_, 1, v_startInclusive_562_);
lean_ctor_set(v___x_564_, 2, v_endExclusive_563_);
v___x_565_ = lean_array_push(v_b_559_, v___x_564_);
v_a_558_ = v_it_561_;
v_b_559_ = v___x_565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg___boxed(lean_object* v_dt_598_, lean_object* v___x_599_, lean_object* v___x_600_, lean_object* v_a_601_, lean_object* v_b_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_598_, v___x_599_, v___x_600_, v_a_601_, v_b_602_);
lean_dec_ref(v___x_599_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(lean_object* v_head_604_, lean_object* v_a_605_, lean_object* v_b_606_){
_start:
{
if (lean_obj_tag(v_a_605_) == 0)
{
lean_object* v_currPos_607_; lean_object* v_searcher_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_647_; 
v_currPos_607_ = lean_ctor_get(v_a_605_, 0);
v_searcher_608_ = lean_ctor_get(v_a_605_, 1);
v_isSharedCheck_647_ = !lean_is_exclusive(v_a_605_);
if (v_isSharedCheck_647_ == 0)
{
v___x_610_ = v_a_605_;
v_isShared_611_ = v_isSharedCheck_647_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_searcher_608_);
lean_inc(v_currPos_607_);
lean_dec(v_a_605_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_647_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_str_612_; lean_object* v_startInclusive_613_; lean_object* v_endExclusive_614_; lean_object* v_it_616_; lean_object* v_startInclusive_617_; lean_object* v_endExclusive_618_; lean_object* v___x_625_; uint8_t v_decide_626_; 
v_str_612_ = lean_ctor_get(v_head_604_, 0);
v_startInclusive_613_ = lean_ctor_get(v_head_604_, 1);
v_endExclusive_614_ = lean_ctor_get(v_head_604_, 2);
v___x_625_ = lean_nat_sub(v_endExclusive_614_, v_startInclusive_613_);
v_decide_626_ = lean_nat_dec_eq(v_searcher_608_, v___x_625_);
if (v_decide_626_ == 0)
{
uint32_t v___x_627_; lean_object* v___x_628_; uint32_t v___x_629_; uint8_t v___x_630_; 
lean_dec(v___x_625_);
v___x_627_ = 45;
v___x_628_ = lean_nat_add(v_startInclusive_613_, v_searcher_608_);
v___x_629_ = lean_string_utf8_get_fast(v_str_612_, v___x_628_);
v___x_630_ = lean_uint32_dec_eq(v___x_629_, v___x_627_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
lean_dec(v_searcher_608_);
v___x_631_ = lean_string_utf8_next_fast(v_str_612_, v___x_628_);
lean_dec(v___x_628_);
v___x_632_ = lean_nat_sub(v___x_631_, v_startInclusive_613_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 1, v___x_632_);
v___x_634_ = v___x_610_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_currPos_607_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v___x_632_);
v___x_634_ = v_reuseFailAlloc_636_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
v_a_605_ = v___x_634_;
goto _start;
}
}
else
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_slice_640_; lean_object* v_nextIt_642_; 
v___x_637_ = lean_string_utf8_next_fast(v_str_612_, v___x_628_);
v___x_638_ = lean_nat_sub(v___x_637_, v___x_628_);
lean_dec(v___x_628_);
v___x_639_ = lean_nat_add(v_searcher_608_, v___x_638_);
lean_dec(v___x_638_);
v_slice_640_ = l_String_Slice_subslice_x21(v_head_604_, v_currPos_607_, v_searcher_608_);
lean_inc(v___x_639_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 1, v___x_639_);
lean_ctor_set(v___x_610_, 0, v___x_639_);
v_nextIt_642_ = v___x_610_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_639_);
v_nextIt_642_ = v_reuseFailAlloc_645_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v_startInclusive_643_; lean_object* v_endExclusive_644_; 
v_startInclusive_643_ = lean_ctor_get(v_slice_640_, 0);
lean_inc(v_startInclusive_643_);
v_endExclusive_644_ = lean_ctor_get(v_slice_640_, 1);
lean_inc(v_endExclusive_644_);
lean_dec_ref(v_slice_640_);
v_it_616_ = v_nextIt_642_;
v_startInclusive_617_ = v_startInclusive_643_;
v_endExclusive_618_ = v_endExclusive_644_;
goto v___jp_615_;
}
}
}
else
{
lean_object* v___x_646_; 
lean_del_object(v___x_610_);
lean_dec(v_searcher_608_);
v___x_646_ = lean_box(1);
v_it_616_ = v___x_646_;
v_startInclusive_617_ = v_currPos_607_;
v_endExclusive_618_ = v___x_625_;
goto v___jp_615_;
}
v___jp_615_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_619_ = lean_nat_add(v_startInclusive_613_, v_startInclusive_617_);
lean_dec(v_startInclusive_617_);
v___x_620_ = lean_nat_add(v_startInclusive_613_, v_endExclusive_618_);
lean_dec(v_endExclusive_618_);
lean_inc_ref(v_str_612_);
v___x_621_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_621_, 0, v_str_612_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
lean_ctor_set(v___x_621_, 2, v___x_620_);
v___x_622_ = l_String_Slice_toString(v___x_621_);
lean_dec_ref_known(v___x_621_, 3);
v___x_623_ = lean_array_push(v_b_606_, v___x_622_);
v_a_605_ = v_it_616_;
v_b_606_ = v___x_623_;
goto _start;
}
}
}
else
{
return v_b_606_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg___boxed(lean_object* v_head_648_, lean_object* v_a_649_, lean_object* v_b_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_648_, v_a_649_, v_b_650_);
lean_dec_ref(v_head_648_);
return v_res_651_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(lean_object* v_s_652_, lean_object* v_a_653_, uint8_t v_b_654_){
_start:
{
lean_object* v_str_655_; lean_object* v_startInclusive_656_; lean_object* v_endExclusive_657_; lean_object* v___x_658_; uint8_t v_decide_659_; 
v_str_655_ = lean_ctor_get(v_s_652_, 0);
v_startInclusive_656_ = lean_ctor_get(v_s_652_, 1);
v_endExclusive_657_ = lean_ctor_get(v_s_652_, 2);
v___x_658_ = lean_nat_sub(v_endExclusive_657_, v_startInclusive_656_);
v_decide_659_ = lean_nat_dec_eq(v_a_653_, v___x_658_);
lean_dec(v___x_658_);
if (v_decide_659_ == 0)
{
lean_object* v___x_660_; uint32_t v___x_661_; uint32_t v___x_662_; uint8_t v___x_663_; 
v___x_660_ = lean_nat_add(v_startInclusive_656_, v_a_653_);
lean_dec(v_a_653_);
v___x_661_ = lean_string_utf8_get_fast(v_str_655_, v___x_660_);
v___x_662_ = 58;
v___x_663_ = lean_uint32_dec_eq(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_string_utf8_next_fast(v_str_655_, v___x_660_);
lean_dec(v___x_660_);
v___x_665_ = lean_nat_sub(v___x_664_, v_startInclusive_656_);
v_a_653_ = v___x_665_;
v_b_654_ = v___x_663_;
goto _start;
}
else
{
lean_dec(v___x_660_);
return v___x_663_;
}
}
else
{
lean_dec(v_a_653_);
return v_b_654_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_652_ = stack[0].m_obj;
lean_object* v_a_653_ = stack[1].m_obj;
uint8_t v_b_654_ = stack[2].m_num;
uint8_t v_res_667_;
v_res_667_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_652_, v_a_653_, v_b_654_);
stack->m_num = v_res_667_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_s_668_, lean_object* v_a_669_, lean_object* v_b_670_){
_start:
{
uint8_t v_b_boxed_671_; uint8_t v_res_672_; lean_object* v_r_673_; 
v_b_boxed_671_ = lean_unbox(v_b_670_);
v_res_672_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_668_, v_a_669_, v_b_boxed_671_);
lean_dec_ref(v_s_668_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
uint8_t l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(lean_object* v_s_674_){
_start:
{
lean_object* v_searcher_675_; uint8_t v___x_676_; uint8_t v___x_677_; 
v_searcher_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = 0;
v___x_677_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_674_, v_searcher_675_, v___x_676_);
return v___x_677_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_674_ = stack[0].m_obj;
uint8_t v_res_678_;
v_res_678_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_s_674_);
stack->m_num = v_res_678_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2___boxed(lean_object* v_s_679_){
_start:
{
uint8_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_s_679_);
lean_dec_ref(v_s_679_);
v_r_681_ = lean_box(v_res_680_);
return v_r_681_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ofString_x3f(lean_object* v_dt_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_string_utf8_byte_size(v_dt_682_);
lean_inc_ref(v_dt_682_);
v___x_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_685_, 0, v_dt_682_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
lean_ctor_set(v___x_685_, 2, v___x_684_);
v___x_686_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0);
v___x_687_ = ((lean_object*)(l_Lake_Toml_Time_ofString_x3f___closed__0));
v___x_688_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_682_, v___x_685_, v___x_684_, v___x_686_, v___x_687_);
lean_dec_ref_known(v___x_685_, 3);
v___x_689_ = lean_array_to_list(v___x_688_);
if (lean_obj_tag(v___x_689_) == 1)
{
lean_object* v_tail_690_; 
v_tail_690_ = lean_ctor_get(v___x_689_, 1);
lean_inc(v_tail_690_);
if (lean_obj_tag(v_tail_690_) == 0)
{
lean_object* v_head_691_; uint8_t v___x_692_; 
v_head_691_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_head_691_);
lean_dec_ref_known(v___x_689_, 2);
v___x_692_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_head_691_);
if (v___x_692_ == 0)
{
lean_object* v_str_693_; lean_object* v_startInclusive_694_; lean_object* v_endExclusive_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v_str_693_ = lean_ctor_get(v_head_691_, 0);
lean_inc_ref(v_str_693_);
v_startInclusive_694_ = lean_ctor_get(v_head_691_, 1);
lean_inc(v_startInclusive_694_);
v_endExclusive_695_ = lean_ctor_get(v_head_691_, 2);
lean_inc(v_endExclusive_695_);
lean_dec(v_head_691_);
v___x_696_ = lean_string_utf8_extract_fast(v_str_693_, v_startInclusive_694_, v_endExclusive_695_);
lean_dec(v_endExclusive_695_);
lean_dec(v_startInclusive_694_);
lean_dec_ref(v_str_693_);
v___x_697_ = l_Lake_Date_ofString_x3f(v___x_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; 
v___x_698_ = lean_box(0);
return v___x_698_;
}
else
{
lean_object* v_val_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_707_; 
v_val_699_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_707_ == 0)
{
v___x_701_ = v___x_697_;
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_val_699_);
lean_dec(v___x_697_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_707_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_703_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_703_, 0, v_val_699_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_703_);
v___x_705_ = v___x_701_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_str_708_; lean_object* v_startInclusive_709_; lean_object* v_endExclusive_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_str_708_ = lean_ctor_get(v_head_691_, 0);
lean_inc_ref(v_str_708_);
v_startInclusive_709_ = lean_ctor_get(v_head_691_, 1);
lean_inc(v_startInclusive_709_);
v_endExclusive_710_ = lean_ctor_get(v_head_691_, 2);
lean_inc(v_endExclusive_710_);
lean_dec(v_head_691_);
v___x_711_ = lean_string_utf8_extract_fast(v_str_708_, v_startInclusive_709_, v_endExclusive_710_);
lean_dec(v_endExclusive_710_);
lean_dec(v_startInclusive_709_);
lean_dec_ref(v_str_708_);
v___x_712_ = l_Lake_Toml_Time_ofString_x3f(v___x_711_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; 
v___x_713_ = lean_box(0);
return v___x_713_;
}
else
{
lean_object* v_val_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_722_; 
v_val_714_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_722_ == 0)
{
v___x_716_ = v___x_712_;
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_val_714_);
lean_dec(v___x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_718_, 0, v_val_714_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
else
{
lean_object* v_tail_723_; 
v_tail_723_ = lean_ctor_get(v_tail_690_, 1);
if (lean_obj_tag(v_tail_723_) == 0)
{
lean_object* v_head_724_; lean_object* v_head_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_900_; 
v_head_724_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_head_724_);
lean_dec_ref_known(v___x_689_, 2);
v_head_725_ = lean_ctor_get(v_tail_690_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v_tail_690_);
if (v_isSharedCheck_900_ == 0)
{
lean_object* v_unused_901_; 
v_unused_901_ = lean_ctor_get(v_tail_690_, 1);
lean_dec(v_unused_901_);
v___x_727_ = v_tail_690_;
v_isShared_728_ = v_isSharedCheck_900_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_head_725_);
lean_dec(v_tail_690_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_900_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_str_729_; lean_object* v_startInclusive_730_; lean_object* v_endExclusive_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_str_729_ = lean_ctor_get(v_head_724_, 0);
lean_inc_ref(v_str_729_);
v_startInclusive_730_ = lean_ctor_get(v_head_724_, 1);
lean_inc(v_startInclusive_730_);
v_endExclusive_731_ = lean_ctor_get(v_head_724_, 2);
lean_inc(v_endExclusive_731_);
lean_dec(v_head_724_);
v___x_732_ = lean_string_utf8_extract_fast(v_str_729_, v_startInclusive_730_, v_endExclusive_731_);
lean_dec(v_endExclusive_731_);
lean_dec(v_startInclusive_730_);
lean_dec_ref(v_str_729_);
v___x_733_ = l_Lake_Date_ofString_x3f(v___x_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; 
lean_del_object(v___x_727_);
lean_dec(v_head_725_);
v___x_734_ = lean_box(0);
return v___x_734_;
}
else
{
lean_object* v_val_735_; lean_object* v_str_736_; lean_object* v_startInclusive_737_; lean_object* v_endExclusive_738_; uint8_t v___y_755_; uint32_t v___y_830_; uint32_t v___y_883_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_val_735_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_val_735_);
lean_dec_ref_known(v___x_733_, 1);
v_str_736_ = lean_ctor_get(v_head_725_, 0);
v_startInclusive_737_ = lean_ctor_get(v_head_725_, 1);
v_endExclusive_738_ = lean_ctor_get(v_head_725_, 2);
v___x_894_ = lean_nat_sub(v_endExclusive_738_, v_startInclusive_737_);
v___x_895_ = l_String_Slice_Pos_prev_x3f(v_head_725_, v___x_894_);
lean_dec(v___x_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
goto v___jp_892_;
}
else
{
lean_object* v_val_896_; lean_object* v___x_897_; 
v_val_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = l_String_Slice_Pos_get_x3f(v_head_725_, v_val_896_);
lean_dec(v_val_896_);
if (lean_obj_tag(v___x_897_) == 0)
{
goto v___jp_892_;
}
else
{
lean_object* v_val_898_; uint32_t v___x_899_; 
v_val_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_val_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = lean_unbox_uint32(v_val_898_);
lean_dec(v_val_898_);
v___y_883_ = v___x_899_;
goto v___jp_882_;
}
}
v___jp_739_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_string_utf8_extract_fast(v_str_736_, v_startInclusive_737_, v_endExclusive_738_);
lean_dec(v_endExclusive_738_);
lean_dec(v_startInclusive_737_);
lean_dec_ref(v_str_736_);
v___x_741_ = l_Lake_Toml_Time_ofString_x3f(v___x_740_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v___x_742_; 
lean_dec(v_val_735_);
lean_del_object(v___x_727_);
v___x_742_ = lean_box(0);
return v___x_742_;
}
else
{
lean_object* v_val_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_753_; 
v_val_743_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_753_ == 0)
{
v___x_745_ = v___x_741_;
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_val_743_);
lean_dec(v___x_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_val_743_);
lean_ctor_set(v___x_727_, 0, v_val_735_);
v___x_748_ = v___x_727_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_val_735_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_val_743_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_748_);
v___x_750_ = v___x_745_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
v___jp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_798_; 
v___x_756_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0);
v___x_757_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_725_, v___x_756_, v___x_687_);
v_isSharedCheck_798_ = !lean_is_exclusive(v_head_725_);
if (v_isSharedCheck_798_ == 0)
{
lean_object* v_unused_799_; lean_object* v_unused_800_; lean_object* v_unused_801_; 
v_unused_799_ = lean_ctor_get(v_head_725_, 2);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_head_725_, 1);
lean_dec(v_unused_800_);
v_unused_801_ = lean_ctor_get(v_head_725_, 0);
lean_dec(v_unused_801_);
v___x_759_ = v_head_725_;
v_isShared_760_ = v_isSharedCheck_798_;
goto v_resetjp_758_;
}
else
{
lean_dec(v_head_725_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_798_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; 
v___x_761_ = lean_array_to_list(v___x_757_);
if (lean_obj_tag(v___x_761_) == 1)
{
lean_object* v_tail_762_; 
v_tail_762_ = lean_ctor_get(v___x_761_, 1);
lean_inc(v_tail_762_);
if (lean_obj_tag(v_tail_762_) == 1)
{
lean_object* v_tail_763_; 
v_tail_763_ = lean_ctor_get(v_tail_762_, 1);
if (lean_obj_tag(v_tail_763_) == 0)
{
lean_object* v_head_764_; lean_object* v_head_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_796_; 
lean_dec(v_endExclusive_738_);
lean_dec(v_startInclusive_737_);
lean_dec_ref(v_str_736_);
lean_del_object(v___x_727_);
v_head_764_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_head_764_);
lean_dec_ref_known(v___x_761_, 2);
v_head_765_ = lean_ctor_get(v_tail_762_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_tail_762_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_tail_762_, 1);
lean_dec(v_unused_797_);
v___x_767_ = v_tail_762_;
v_isShared_768_ = v_isSharedCheck_796_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_head_765_);
lean_dec(v_tail_762_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_796_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lake_Toml_Time_ofString_x3f(v_head_764_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; 
lean_del_object(v___x_767_);
lean_dec(v_head_765_);
lean_del_object(v___x_759_);
lean_dec(v_val_735_);
v___x_770_ = lean_box(0);
return v___x_770_;
}
else
{
lean_object* v_val_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_795_; 
v_val_771_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_795_ == 0)
{
v___x_773_ = v___x_769_;
v_isShared_774_ = v_isSharedCheck_795_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_val_771_);
lean_dec(v___x_769_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_795_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lake_Toml_Time_ofString_x3f(v_head_765_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v___x_776_; 
lean_del_object(v___x_773_);
lean_dec(v_val_771_);
lean_del_object(v___x_767_);
lean_del_object(v___x_759_);
lean_dec(v_val_735_);
v___x_776_ = lean_box(0);
return v___x_776_;
}
else
{
lean_object* v_val_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_794_; 
v_val_777_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_794_ == 0)
{
v___x_779_ = v___x_775_;
v_isShared_780_ = v_isSharedCheck_794_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_val_777_);
lean_dec(v___x_775_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_794_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_box(v___y_755_);
if (v_isShared_768_ == 0)
{
lean_ctor_set_tag(v___x_767_, 0);
lean_ctor_set(v___x_767_, 1, v_val_777_);
lean_ctor_set(v___x_767_, 0, v___x_781_);
v___x_783_ = v___x_767_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_781_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_val_777_);
v___x_783_ = v_reuseFailAlloc_793_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_783_);
v___x_785_ = v___x_779_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_792_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_787_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 2, v___x_785_);
lean_ctor_set(v___x_759_, 1, v_val_771_);
lean_ctor_set(v___x_759_, 0, v_val_735_);
v___x_787_ = v___x_759_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_val_735_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_val_771_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v___x_785_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_787_);
v___x_789_ = v___x_773_;
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
}
}
}
}
else
{
lean_dec_ref_known(v_tail_762_, 2);
lean_dec_ref_known(v___x_761_, 2);
lean_del_object(v___x_759_);
goto v___jp_739_;
}
}
else
{
lean_dec_ref_known(v___x_761_, 2);
lean_dec(v_tail_762_);
lean_del_object(v___x_759_);
goto v___jp_739_;
}
}
else
{
lean_dec(v___x_761_);
lean_del_object(v___x_759_);
goto v___jp_739_;
}
}
}
v___jp_802_:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_825_; 
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = lean_nat_sub(v_endExclusive_738_, v_startInclusive_737_);
v___x_805_ = l_String_Slice_Pos_prevn(v_head_725_, v___x_804_, v___x_803_);
v_isSharedCheck_825_ = !lean_is_exclusive(v_head_725_);
if (v_isSharedCheck_825_ == 0)
{
lean_object* v_unused_826_; lean_object* v_unused_827_; lean_object* v_unused_828_; 
v_unused_826_ = lean_ctor_get(v_head_725_, 2);
lean_dec(v_unused_826_);
v_unused_827_ = lean_ctor_get(v_head_725_, 1);
lean_dec(v_unused_827_);
v_unused_828_ = lean_ctor_get(v_head_725_, 0);
lean_dec(v_unused_828_);
v___x_807_ = v_head_725_;
v_isShared_808_ = v_isSharedCheck_825_;
goto v_resetjp_806_;
}
else
{
lean_dec(v_head_725_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_825_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = lean_nat_add(v_startInclusive_737_, v___x_805_);
lean_dec(v___x_805_);
v___x_810_ = lean_string_utf8_extract_fast(v_str_736_, v_startInclusive_737_, v___x_809_);
lean_dec(v___x_809_);
lean_dec(v_startInclusive_737_);
lean_dec_ref(v_str_736_);
v___x_811_ = l_Lake_Toml_Time_ofString_x3f(v___x_810_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v___x_812_; 
lean_del_object(v___x_807_);
lean_dec(v_val_735_);
v___x_812_ = lean_box(0);
return v___x_812_;
}
else
{
lean_object* v_val_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_824_; 
v_val_813_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_824_ == 0)
{
v___x_815_ = v___x_811_;
v_isShared_816_ = v_isSharedCheck_824_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_val_813_);
lean_dec(v___x_811_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_824_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_819_; 
v___x_817_ = lean_box(0);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 2, v___x_817_);
lean_ctor_set(v___x_807_, 1, v_val_813_);
lean_ctor_set(v___x_807_, 0, v_val_735_);
v___x_819_ = v___x_807_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_val_735_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_val_813_);
lean_ctor_set(v_reuseFailAlloc_823_, 2, v___x_817_);
v___x_819_ = v_reuseFailAlloc_823_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_821_; 
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_819_);
v___x_821_ = v___x_815_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
}
}
v___jp_829_:
{
uint32_t v___x_831_; uint8_t v___x_832_; 
v___x_831_ = 122;
v___x_832_ = lean_uint32_dec_eq(v___y_830_, v___x_831_);
if (v___x_832_ == 0)
{
uint8_t v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_833_ = 1;
v___x_834_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0);
v___x_835_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_725_, v___x_834_, v___x_687_);
v___x_836_ = lean_array_to_list(v___x_835_);
if (lean_obj_tag(v___x_836_) == 1)
{
lean_object* v_tail_837_; 
v_tail_837_ = lean_ctor_get(v___x_836_, 1);
lean_inc(v_tail_837_);
if (lean_obj_tag(v_tail_837_) == 1)
{
lean_object* v_tail_838_; 
v_tail_838_ = lean_ctor_get(v_tail_837_, 1);
if (lean_obj_tag(v_tail_838_) == 0)
{
lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_876_; 
lean_del_object(v___x_727_);
v_isSharedCheck_876_ = !lean_is_exclusive(v_head_725_);
if (v_isSharedCheck_876_ == 0)
{
lean_object* v_unused_877_; lean_object* v_unused_878_; lean_object* v_unused_879_; 
v_unused_877_ = lean_ctor_get(v_head_725_, 2);
lean_dec(v_unused_877_);
v_unused_878_ = lean_ctor_get(v_head_725_, 1);
lean_dec(v_unused_878_);
v_unused_879_ = lean_ctor_get(v_head_725_, 0);
lean_dec(v_unused_879_);
v___x_840_ = v_head_725_;
v_isShared_841_ = v_isSharedCheck_876_;
goto v_resetjp_839_;
}
else
{
lean_dec(v_head_725_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_876_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_head_842_; lean_object* v_head_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_874_; 
v_head_842_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_head_842_);
lean_dec_ref_known(v___x_836_, 2);
v_head_843_ = lean_ctor_get(v_tail_837_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v_tail_837_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v_tail_837_, 1);
lean_dec(v_unused_875_);
v___x_845_ = v_tail_837_;
v_isShared_846_ = v_isSharedCheck_874_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_head_843_);
lean_dec(v_tail_837_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_874_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lake_Toml_Time_ofString_x3f(v_head_842_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v___x_848_; 
lean_del_object(v___x_845_);
lean_dec(v_head_843_);
lean_del_object(v___x_840_);
lean_dec(v_val_735_);
v___x_848_ = lean_box(0);
return v___x_848_;
}
else
{
lean_object* v_val_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_873_; 
v_val_849_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_873_ == 0)
{
v___x_851_ = v___x_847_;
v_isShared_852_ = v_isSharedCheck_873_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_val_849_);
lean_dec(v___x_847_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_873_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; 
v___x_853_ = l_Lake_Toml_Time_ofString_x3f(v_head_843_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v___x_854_; 
lean_del_object(v___x_851_);
lean_dec(v_val_849_);
lean_del_object(v___x_845_);
lean_del_object(v___x_840_);
lean_dec(v_val_735_);
v___x_854_ = lean_box(0);
return v___x_854_;
}
else
{
lean_object* v_val_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_872_; 
v_val_855_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_872_ == 0)
{
v___x_857_ = v___x_853_;
v_isShared_858_ = v_isSharedCheck_872_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_val_855_);
lean_dec(v___x_853_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_872_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = lean_box(v___x_832_);
if (v_isShared_846_ == 0)
{
lean_ctor_set_tag(v___x_845_, 0);
lean_ctor_set(v___x_845_, 1, v_val_855_);
lean_ctor_set(v___x_845_, 0, v___x_859_);
v___x_861_ = v___x_845_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_859_);
lean_ctor_set(v_reuseFailAlloc_871_, 1, v_val_855_);
v___x_861_ = v_reuseFailAlloc_871_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_861_);
v___x_863_ = v___x_857_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_870_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 2, v___x_863_);
lean_ctor_set(v___x_840_, 1, v_val_849_);
lean_ctor_set(v___x_840_, 0, v_val_735_);
v___x_865_ = v___x_840_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_val_735_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_val_849_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v___x_863_);
v___x_865_ = v_reuseFailAlloc_869_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
lean_object* v___x_867_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_865_);
v___x_867_ = v___x_851_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
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
lean_inc(v_endExclusive_738_);
lean_inc(v_startInclusive_737_);
lean_inc_ref(v_str_736_);
lean_dec_ref_known(v_tail_837_, 2);
lean_dec_ref_known(v___x_836_, 2);
v___y_755_ = v___x_833_;
goto v___jp_754_;
}
}
else
{
lean_inc(v_endExclusive_738_);
lean_inc(v_startInclusive_737_);
lean_inc_ref(v_str_736_);
lean_dec(v_tail_837_);
lean_dec_ref_known(v___x_836_, 2);
v___y_755_ = v___x_833_;
goto v___jp_754_;
}
}
else
{
lean_inc(v_endExclusive_738_);
lean_inc(v_startInclusive_737_);
lean_inc_ref(v_str_736_);
lean_dec(v___x_836_);
v___y_755_ = v___x_833_;
goto v___jp_754_;
}
}
else
{
lean_inc(v_startInclusive_737_);
lean_inc_ref(v_str_736_);
lean_del_object(v___x_727_);
goto v___jp_802_;
}
}
v___jp_880_:
{
uint32_t v___x_881_; 
v___x_881_ = 65;
v___y_830_ = v___x_881_;
goto v___jp_829_;
}
v___jp_882_:
{
uint32_t v___x_884_; uint8_t v___x_885_; 
v___x_884_ = 90;
v___x_885_ = lean_uint32_dec_eq(v___y_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = lean_nat_sub(v_endExclusive_738_, v_startInclusive_737_);
v___x_887_ = l_String_Slice_Pos_prev_x3f(v_head_725_, v___x_886_);
lean_dec(v___x_886_);
if (lean_obj_tag(v___x_887_) == 0)
{
goto v___jp_880_;
}
else
{
lean_object* v_val_888_; lean_object* v___x_889_; 
v_val_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_val_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_889_ = l_String_Slice_Pos_get_x3f(v_head_725_, v_val_888_);
lean_dec(v_val_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
goto v___jp_880_;
}
else
{
lean_object* v_val_890_; uint32_t v___x_891_; 
v_val_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_891_ = lean_unbox_uint32(v_val_890_);
lean_dec(v_val_890_);
v___y_830_ = v___x_891_;
goto v___jp_829_;
}
}
}
else
{
lean_inc(v_startInclusive_737_);
lean_inc_ref(v_str_736_);
lean_del_object(v___x_727_);
goto v___jp_802_;
}
}
v___jp_892_:
{
uint32_t v___x_893_; 
v___x_893_ = 65;
v___y_883_ = v___x_893_;
goto v___jp_882_;
}
}
}
}
else
{
lean_object* v___x_902_; 
lean_dec_ref_known(v_tail_690_, 2);
lean_dec_ref_known(v___x_689_, 2);
v___x_902_ = lean_box(0);
return v___x_902_;
}
}
}
else
{
lean_object* v___x_903_; 
lean_dec(v___x_689_);
v___x_903_ = lean_box(0);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(lean_object* v_dt_904_, lean_object* v___x_905_, lean_object* v___x_906_, lean_object* v_inst_907_, lean_object* v_R_908_, lean_object* v_a_909_, lean_object* v_b_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_904_, v___x_905_, v___x_906_, v_a_909_, v_b_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___boxed(lean_object* v_dt_912_, lean_object* v___x_913_, lean_object* v___x_914_, lean_object* v_inst_915_, lean_object* v_R_916_, lean_object* v_a_917_, lean_object* v_b_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(v_dt_912_, v___x_913_, v___x_914_, v_inst_915_, v_R_916_, v_a_917_, v_b_918_);
lean_dec_ref(v___x_913_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(lean_object* v_head_920_, lean_object* v_inst_921_, lean_object* v_R_922_, lean_object* v_a_923_, lean_object* v_b_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_920_, v_a_923_, v_b_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___boxed(lean_object* v_head_926_, lean_object* v_inst_927_, lean_object* v_R_928_, lean_object* v_a_929_, lean_object* v_b_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(v_head_926_, v_inst_927_, v_R_928_, v_a_929_, v_b_930_);
lean_dec_ref(v_head_926_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(lean_object* v_head_932_, lean_object* v_inst_933_, lean_object* v_R_934_, lean_object* v_a_935_, lean_object* v_b_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_932_, v_a_935_, v_b_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___boxed(lean_object* v_head_938_, lean_object* v_inst_939_, lean_object* v_R_940_, lean_object* v_a_941_, lean_object* v_b_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(v_head_938_, v_inst_939_, v_R_940_, v_a_941_, v_b_942_);
lean_dec_ref(v_head_938_);
return v_res_943_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(lean_object* v_s_944_, lean_object* v_inst_945_, lean_object* v_R_946_, lean_object* v_a_947_, uint8_t v_b_948_, lean_object* v_c_949_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_944_, v_a_947_, v_b_948_);
return v___x_950_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_944_ = stack[0].m_obj;
lean_object* v_a_947_ = stack[3].m_obj;
uint8_t v_b_948_ = stack[4].m_num;
uint8_t v_res_951_;
v_res_951_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(v_s_944_, lean_box(0), lean_box(0), v_a_947_, v_b_948_, lean_box(0));
stack->m_num = v_res_951_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___boxed(lean_object* v_s_952_, lean_object* v_inst_953_, lean_object* v_R_954_, lean_object* v_a_955_, lean_object* v_b_956_, lean_object* v_c_957_){
_start:
{
uint8_t v_b_boxed_958_; uint8_t v_res_959_; lean_object* v_r_960_; 
v_b_boxed_958_ = lean_unbox(v_b_956_);
v_res_959_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(v_s_952_, v_inst_953_, v_R_954_, v_a_955_, v_b_boxed_958_, v_c_957_);
lean_dec_ref(v_s_952_);
v_r_960_ = lean_box(v_res_959_);
return v_r_960_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_toString(lean_object* v_dt_965_){
_start:
{
switch(lean_obj_tag(v_dt_965_))
{
case 0:
{
lean_object* v_offset_x3f_966_; 
v_offset_x3f_966_ = lean_ctor_get(v_dt_965_, 2);
if (lean_obj_tag(v_offset_x3f_966_) == 1)
{
lean_object* v_val_967_; lean_object* v_fst_968_; uint8_t v___x_969_; 
v_val_967_ = lean_ctor_get(v_offset_x3f_966_, 0);
v_fst_968_ = lean_ctor_get(v_val_967_, 0);
v___x_969_ = lean_unbox(v_fst_968_);
if (v___x_969_ == 0)
{
lean_object* v_snd_970_; lean_object* v_date_971_; lean_object* v_time_972_; lean_object* v_hour_973_; lean_object* v_minute_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_snd_970_ = lean_ctor_get(v_val_967_, 1);
lean_inc(v_snd_970_);
v_date_971_ = lean_ctor_get(v_dt_965_, 0);
lean_inc_ref(v_date_971_);
v_time_972_ = lean_ctor_get(v_dt_965_, 1);
lean_inc_ref(v_time_972_);
lean_dec_ref_known(v_dt_965_, 3);
v_hour_973_ = lean_ctor_get(v_snd_970_, 0);
lean_inc(v_hour_973_);
v_minute_974_ = lean_ctor_get(v_snd_970_, 1);
lean_inc(v_minute_974_);
lean_dec(v_snd_970_);
v___x_975_ = l_Lake_Date_toString(v_date_971_);
v___x_976_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
v___x_978_ = l_Lake_Toml_Time_toString(v_time_972_);
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
lean_dec_ref(v___x_978_);
v___x_980_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__1));
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
v___x_982_ = lean_unsigned_to_nat(2u);
v___x_983_ = l_Lake_zpad(v_hour_973_, v___x_982_);
v___x_984_ = lean_string_append(v___x_981_, v___x_983_);
lean_dec_ref(v___x_983_);
v___x_985_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_986_ = lean_string_append(v___x_984_, v___x_985_);
v___x_987_ = l_Lake_zpad(v_minute_974_, v___x_982_);
v___x_988_ = lean_string_append(v___x_986_, v___x_987_);
lean_dec_ref(v___x_987_);
return v___x_988_;
}
else
{
lean_object* v_snd_989_; lean_object* v_date_990_; lean_object* v_time_991_; lean_object* v_hour_992_; lean_object* v_minute_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_snd_989_ = lean_ctor_get(v_val_967_, 1);
lean_inc(v_snd_989_);
v_date_990_ = lean_ctor_get(v_dt_965_, 0);
lean_inc_ref(v_date_990_);
v_time_991_ = lean_ctor_get(v_dt_965_, 1);
lean_inc_ref(v_time_991_);
lean_dec_ref_known(v_dt_965_, 3);
v_hour_992_ = lean_ctor_get(v_snd_989_, 0);
lean_inc(v_hour_992_);
v_minute_993_ = lean_ctor_get(v_snd_989_, 1);
lean_inc(v_minute_993_);
lean_dec(v_snd_989_);
v___x_994_ = l_Lake_Date_toString(v_date_990_);
v___x_995_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_996_ = lean_string_append(v___x_994_, v___x_995_);
v___x_997_ = l_Lake_Toml_Time_toString(v_time_991_);
v___x_998_ = lean_string_append(v___x_996_, v___x_997_);
lean_dec_ref(v___x_997_);
v___x_999_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__2));
v___x_1000_ = lean_string_append(v___x_998_, v___x_999_);
v___x_1001_ = lean_unsigned_to_nat(2u);
v___x_1002_ = l_Lake_zpad(v_hour_992_, v___x_1001_);
v___x_1003_ = lean_string_append(v___x_1000_, v___x_1002_);
lean_dec_ref(v___x_1002_);
v___x_1004_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_1005_ = lean_string_append(v___x_1003_, v___x_1004_);
v___x_1006_ = l_Lake_zpad(v_minute_993_, v___x_1001_);
v___x_1007_ = lean_string_append(v___x_1005_, v___x_1006_);
lean_dec_ref(v___x_1006_);
return v___x_1007_;
}
}
else
{
lean_object* v_date_1008_; lean_object* v_time_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_date_1008_ = lean_ctor_get(v_dt_965_, 0);
lean_inc_ref(v_date_1008_);
v_time_1009_ = lean_ctor_get(v_dt_965_, 1);
lean_inc_ref(v_time_1009_);
lean_dec_ref_known(v_dt_965_, 3);
v___x_1010_ = l_Lake_Date_toString(v_date_1008_);
v___x_1011_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_1012_ = lean_string_append(v___x_1010_, v___x_1011_);
v___x_1013_ = l_Lake_Toml_Time_toString(v_time_1009_);
v___x_1014_ = lean_string_append(v___x_1012_, v___x_1013_);
lean_dec_ref(v___x_1013_);
v___x_1015_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__3));
v___x_1016_ = lean_string_append(v___x_1014_, v___x_1015_);
return v___x_1016_;
}
}
case 1:
{
lean_object* v_date_1017_; lean_object* v_time_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v_date_1017_ = lean_ctor_get(v_dt_965_, 0);
lean_inc_ref(v_date_1017_);
v_time_1018_ = lean_ctor_get(v_dt_965_, 1);
lean_inc_ref(v_time_1018_);
lean_dec_ref_known(v_dt_965_, 2);
v___x_1019_ = l_Lake_Date_toString(v_date_1017_);
v___x_1020_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_1021_ = lean_string_append(v___x_1019_, v___x_1020_);
v___x_1022_ = l_Lake_Toml_Time_toString(v_time_1018_);
v___x_1023_ = lean_string_append(v___x_1021_, v___x_1022_);
lean_dec_ref(v___x_1022_);
return v___x_1023_;
}
case 2:
{
lean_object* v_date_1024_; lean_object* v___x_1025_; 
v_date_1024_ = lean_ctor_get(v_dt_965_, 0);
lean_inc_ref(v_date_1024_);
lean_dec_ref_known(v_dt_965_, 1);
v___x_1025_ = l_Lake_Date_toString(v_date_1024_);
return v___x_1025_;
}
default: 
{
lean_object* v_time_1026_; lean_object* v___x_1027_; 
v_time_1026_ = lean_ctor_get(v_dt_965_, 0);
lean_inc_ref(v_time_1026_);
lean_dec_ref_known(v_dt_965_, 1);
v___x_1027_ = l_Lake_Toml_Time_toString(v_time_1026_);
return v___x_1027_;
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

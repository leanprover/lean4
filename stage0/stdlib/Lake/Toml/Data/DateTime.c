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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg();
return v_res_55_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg();
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(lean_object* v_s_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___boxed(lean_object* v_s_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(v_s_59_);
lean_dec_ref(v_s_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg(){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg___boxed(lean_object* v___dummy_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg();
return v_res_64_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg();
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(lean_object* v_s_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___boxed(lean_object* v_s_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(v_s_68_);
lean_dec_ref(v_s_68_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(lean_object* v_head_70_, lean_object* v_a_71_, lean_object* v_b_72_){
_start:
{
if (lean_obj_tag(v_a_71_) == 0)
{
lean_object* v_currPos_73_; lean_object* v_searcher_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_112_; 
v_currPos_73_ = lean_ctor_get(v_a_71_, 0);
v_searcher_74_ = lean_ctor_get(v_a_71_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_a_71_);
if (v_isSharedCheck_112_ == 0)
{
v___x_76_ = v_a_71_;
v_isShared_77_ = v_isSharedCheck_112_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_searcher_74_);
lean_inc(v_currPos_73_);
lean_dec(v_a_71_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_112_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v_str_78_; lean_object* v_startInclusive_79_; lean_object* v_endExclusive_80_; lean_object* v_it_82_; lean_object* v_startInclusive_83_; lean_object* v_endExclusive_84_; lean_object* v___x_90_; uint8_t v_decide_91_; 
v_str_78_ = lean_ctor_get(v_head_70_, 0);
v_startInclusive_79_ = lean_ctor_get(v_head_70_, 1);
v_endExclusive_80_ = lean_ctor_get(v_head_70_, 2);
v___x_90_ = lean_nat_sub(v_endExclusive_80_, v_startInclusive_79_);
v_decide_91_ = lean_nat_dec_eq(v_searcher_74_, v___x_90_);
if (v_decide_91_ == 0)
{
uint32_t v___x_92_; lean_object* v___x_93_; uint32_t v___x_94_; uint8_t v___x_95_; 
lean_dec(v___x_90_);
v___x_92_ = 46;
v___x_93_ = lean_nat_add(v_startInclusive_79_, v_searcher_74_);
v___x_94_ = lean_string_utf8_get_fast(v_str_78_, v___x_93_);
v___x_95_ = lean_uint32_dec_eq(v___x_94_, v___x_92_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
lean_dec(v_searcher_74_);
v___x_96_ = lean_string_utf8_next_fast(v_str_78_, v___x_93_);
lean_dec(v___x_93_);
v___x_97_ = lean_nat_sub(v___x_96_, v_startInclusive_79_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___x_97_);
v___x_99_ = v___x_76_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_currPos_73_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___x_97_);
v___x_99_ = v_reuseFailAlloc_101_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
v_a_71_ = v___x_99_;
goto _start;
}
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v_slice_105_; lean_object* v_nextIt_107_; 
v___x_102_ = lean_string_utf8_next_fast(v_str_78_, v___x_93_);
v___x_103_ = lean_nat_sub(v___x_102_, v___x_93_);
lean_dec(v___x_93_);
v___x_104_ = lean_nat_add(v_searcher_74_, v___x_103_);
lean_dec(v___x_103_);
v_slice_105_ = l_String_Slice_subslice_x21(v_head_70_, v_currPos_73_, v_searcher_74_);
lean_inc(v___x_104_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 1, v___x_104_);
lean_ctor_set(v___x_76_, 0, v___x_104_);
v_nextIt_107_ = v___x_76_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___x_104_);
v_nextIt_107_ = v_reuseFailAlloc_110_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v_startInclusive_108_; lean_object* v_endExclusive_109_; 
v_startInclusive_108_ = lean_ctor_get(v_slice_105_, 0);
lean_inc(v_startInclusive_108_);
v_endExclusive_109_ = lean_ctor_get(v_slice_105_, 1);
lean_inc(v_endExclusive_109_);
lean_dec_ref(v_slice_105_);
v_it_82_ = v_nextIt_107_;
v_startInclusive_83_ = v_startInclusive_108_;
v_endExclusive_84_ = v_endExclusive_109_;
goto v___jp_81_;
}
}
}
else
{
lean_object* v___x_111_; 
lean_del_object(v___x_76_);
lean_dec(v_searcher_74_);
v___x_111_ = lean_box(1);
v_it_82_ = v___x_111_;
v_startInclusive_83_ = v_currPos_73_;
v_endExclusive_84_ = v___x_90_;
goto v___jp_81_;
}
v___jp_81_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_nat_add(v_startInclusive_79_, v_startInclusive_83_);
lean_dec(v_startInclusive_83_);
v___x_86_ = lean_nat_add(v_startInclusive_79_, v_endExclusive_84_);
lean_dec(v_endExclusive_84_);
lean_inc_ref(v_str_78_);
v___x_87_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_87_, 0, v_str_78_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_86_);
v___x_88_ = lean_array_push(v_b_72_, v___x_87_);
v_a_71_ = v_it_82_;
v_b_72_ = v___x_88_;
goto _start;
}
}
}
else
{
return v_b_72_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg___boxed(lean_object* v_head_113_, lean_object* v_a_114_, lean_object* v_b_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_113_, v_a_114_, v_b_115_);
lean_dec_ref(v_head_113_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(lean_object* v_t_117_, lean_object* v___x_118_, lean_object* v___x_119_, lean_object* v_a_120_, lean_object* v_b_121_){
_start:
{
lean_object* v_it_123_; lean_object* v_startInclusive_124_; lean_object* v_endExclusive_125_; 
if (lean_obj_tag(v_a_120_) == 0)
{
lean_object* v_currPos_129_; lean_object* v_searcher_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_153_; 
v_currPos_129_ = lean_ctor_get(v_a_120_, 0);
v_searcher_130_ = lean_ctor_get(v_a_120_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_a_120_);
if (v_isSharedCheck_153_ == 0)
{
v___x_132_ = v_a_120_;
v_isShared_133_ = v_isSharedCheck_153_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_searcher_130_);
lean_inc(v_currPos_129_);
lean_dec(v_a_120_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_153_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
uint8_t v_decide_134_; 
v_decide_134_ = lean_nat_dec_eq(v_searcher_130_, v___x_119_);
if (v_decide_134_ == 0)
{
uint32_t v___x_135_; uint32_t v___x_136_; uint8_t v___x_137_; 
v___x_135_ = 58;
v___x_136_ = lean_string_utf8_get_fast(v_t_117_, v_searcher_130_);
v___x_137_ = lean_uint32_dec_eq(v___x_136_, v___x_135_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_string_utf8_next_fast(v_t_117_, v_searcher_130_);
lean_dec(v_searcher_130_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_138_);
v___x_140_ = v___x_132_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_currPos_129_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_138_);
v___x_140_ = v_reuseFailAlloc_142_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
v_a_120_ = v___x_140_;
goto _start;
}
}
else
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v_slice_146_; lean_object* v_nextIt_148_; 
v___x_143_ = lean_string_utf8_next_fast(v_t_117_, v_searcher_130_);
v___x_144_ = lean_nat_sub(v___x_143_, v_searcher_130_);
v___x_145_ = lean_nat_add(v_searcher_130_, v___x_144_);
lean_dec(v___x_144_);
v_slice_146_ = l_String_Slice_subslice_x21(v___x_118_, v_currPos_129_, v_searcher_130_);
lean_inc(v___x_145_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_145_);
lean_ctor_set(v___x_132_, 0, v___x_145_);
v_nextIt_148_ = v___x_132_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_145_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_145_);
v_nextIt_148_ = v_reuseFailAlloc_151_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v_startInclusive_149_; lean_object* v_endExclusive_150_; 
v_startInclusive_149_ = lean_ctor_get(v_slice_146_, 0);
lean_inc(v_startInclusive_149_);
v_endExclusive_150_ = lean_ctor_get(v_slice_146_, 1);
lean_inc(v_endExclusive_150_);
lean_dec_ref(v_slice_146_);
v_it_123_ = v_nextIt_148_;
v_startInclusive_124_ = v_startInclusive_149_;
v_endExclusive_125_ = v_endExclusive_150_;
goto v___jp_122_;
}
}
}
else
{
lean_object* v___x_152_; 
lean_del_object(v___x_132_);
lean_dec(v_searcher_130_);
v___x_152_ = lean_box(1);
lean_inc(v___x_119_);
v_it_123_ = v___x_152_;
v_startInclusive_124_ = v_currPos_129_;
v_endExclusive_125_ = v___x_119_;
goto v___jp_122_;
}
}
}
else
{
lean_dec(v___x_119_);
lean_dec_ref(v_t_117_);
return v_b_121_;
}
v___jp_122_:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
lean_inc_ref(v_t_117_);
v___x_126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_126_, 0, v_t_117_);
lean_ctor_set(v___x_126_, 1, v_startInclusive_124_);
lean_ctor_set(v___x_126_, 2, v_endExclusive_125_);
v___x_127_ = lean_array_push(v_b_121_, v___x_126_);
v_a_120_ = v_it_123_;
v_b_121_ = v___x_127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg___boxed(lean_object* v_t_154_, lean_object* v___x_155_, lean_object* v___x_156_, lean_object* v_a_157_, lean_object* v_b_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_154_, v___x_155_, v___x_156_, v_a_157_, v_b_158_);
lean_dec_ref(v___x_155_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(lean_object* v_head_160_, lean_object* v_a_161_, lean_object* v_b_162_){
_start:
{
lean_object* v_str_163_; lean_object* v_startInclusive_164_; lean_object* v_endExclusive_165_; lean_object* v___x_166_; uint8_t v_decide_167_; 
v_str_163_ = lean_ctor_get(v_head_160_, 0);
v_startInclusive_164_ = lean_ctor_get(v_head_160_, 1);
v_endExclusive_165_ = lean_ctor_get(v_head_160_, 2);
v___x_166_ = lean_nat_sub(v_endExclusive_165_, v_startInclusive_164_);
v_decide_167_ = lean_nat_dec_eq(v_a_161_, v___x_166_);
lean_dec(v___x_166_);
if (v_decide_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_168_ = lean_nat_add(v_startInclusive_164_, v_a_161_);
lean_dec(v_a_161_);
v___x_169_ = lean_string_utf8_next_fast(v_str_163_, v___x_168_);
lean_dec(v___x_168_);
v___x_170_ = lean_nat_sub(v___x_169_, v_startInclusive_164_);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = lean_nat_add(v_b_162_, v___x_171_);
lean_dec(v_b_162_);
v_a_161_ = v___x_170_;
v_b_162_ = v___x_172_;
goto _start;
}
else
{
lean_dec(v_a_161_);
return v_b_162_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg___boxed(lean_object* v_head_174_, lean_object* v_a_175_, lean_object* v_b_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_174_, v_a_175_, v_b_176_);
lean_dec_ref(v_head_174_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_ofString_x3f(lean_object* v_t_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_string_utf8_byte_size(v_t_180_);
lean_inc_ref(v_t_180_);
v___x_183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_183_, 0, v_t_180_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
lean_ctor_set(v___x_183_, 2, v___x_182_);
v___x_184_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0);
v___x_185_ = ((lean_object*)(l_Lake_Toml_Time_ofString_x3f___closed__0));
v___x_186_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_180_, v___x_183_, v___x_182_, v___x_184_, v___x_185_);
lean_dec_ref_known(v___x_183_, 3);
v___x_187_ = lean_array_to_list(v___x_186_);
if (lean_obj_tag(v___x_187_) == 1)
{
lean_object* v_tail_188_; 
v_tail_188_ = lean_ctor_get(v___x_187_, 1);
lean_inc(v_tail_188_);
if (lean_obj_tag(v_tail_188_) == 1)
{
lean_object* v_tail_189_; 
v_tail_189_ = lean_ctor_get(v_tail_188_, 1);
if (lean_obj_tag(v_tail_189_) == 0)
{
lean_object* v_head_190_; lean_object* v_head_191_; lean_object* v___x_192_; 
v_head_190_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_head_190_);
lean_dec_ref_known(v___x_187_, 2);
v_head_191_ = lean_ctor_get(v_tail_188_, 0);
lean_inc(v_head_191_);
lean_dec_ref_known(v_tail_188_, 2);
v___x_192_ = l_String_Slice_toNat_x3f(v_head_190_);
lean_dec(v_head_190_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_object* v___x_193_; 
lean_dec(v_head_191_);
v___x_193_ = lean_box(0);
return v___x_193_;
}
else
{
lean_object* v_val_194_; lean_object* v___x_195_; 
v_val_194_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_val_194_);
lean_dec_ref_known(v___x_192_, 1);
v___x_195_ = l_String_Slice_toNat_x3f(v_head_191_);
lean_dec(v_head_191_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v___x_196_; 
lean_dec(v_val_194_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
else
{
lean_object* v_val_197_; lean_object* v___x_198_; 
v_val_197_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v___x_195_, 1);
v___x_198_ = l_Lake_Toml_Time_ofValid_x3f(v_val_194_, v_val_197_, v___x_181_);
return v___x_198_;
}
}
}
else
{
lean_object* v_tail_199_; 
lean_inc_ref(v_tail_189_);
v_tail_199_ = lean_ctor_get(v_tail_189_, 1);
if (lean_obj_tag(v_tail_199_) == 0)
{
lean_object* v_head_200_; lean_object* v_head_201_; lean_object* v_head_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_head_200_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_head_200_);
lean_dec_ref_known(v___x_187_, 2);
v_head_201_ = lean_ctor_get(v_tail_188_, 0);
lean_inc(v_head_201_);
lean_dec_ref_known(v_tail_188_, 2);
v_head_202_ = lean_ctor_get(v_tail_189_, 0);
lean_inc(v_head_202_);
lean_dec_ref_known(v_tail_189_, 2);
v___x_203_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0);
v___x_204_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_202_, v___x_203_, v___x_185_);
lean_dec(v_head_202_);
v___x_205_ = lean_array_to_list(v___x_204_);
if (lean_obj_tag(v___x_205_) == 1)
{
lean_object* v_tail_206_; 
v_tail_206_ = lean_ctor_get(v___x_205_, 1);
if (lean_obj_tag(v_tail_206_) == 0)
{
lean_object* v_head_207_; lean_object* v___x_208_; 
v_head_207_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_head_207_);
lean_dec_ref_known(v___x_205_, 2);
v___x_208_ = l_String_Slice_toNat_x3f(v_head_200_);
lean_dec(v_head_200_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_209_; 
lean_dec(v_head_207_);
lean_dec(v_head_201_);
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
lean_object* v_val_210_; lean_object* v___x_211_; 
v_val_210_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v___x_208_, 1);
v___x_211_ = l_String_Slice_toNat_x3f(v_head_201_);
lean_dec(v_head_201_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v___x_212_; 
lean_dec(v_val_210_);
lean_dec(v_head_207_);
v___x_212_ = lean_box(0);
return v___x_212_;
}
else
{
lean_object* v_val_213_; lean_object* v___x_214_; 
v_val_213_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v___x_211_, 1);
v___x_214_ = l_String_Slice_toNat_x3f(v_head_207_);
lean_dec(v_head_207_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v___x_215_; 
lean_dec(v_val_213_);
lean_dec(v_val_210_);
v___x_215_ = lean_box(0);
return v___x_215_;
}
else
{
lean_object* v_val_216_; lean_object* v___x_217_; 
v_val_216_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_val_216_);
lean_dec_ref_known(v___x_214_, 1);
v___x_217_ = l_Lake_Toml_Time_ofValid_x3f(v_val_210_, v_val_213_, v_val_216_);
return v___x_217_;
}
}
}
}
else
{
lean_object* v_tail_218_; 
lean_inc_ref(v_tail_206_);
v_tail_218_ = lean_ctor_get(v_tail_206_, 1);
if (lean_obj_tag(v_tail_218_) == 0)
{
lean_object* v_head_219_; lean_object* v_head_220_; lean_object* v___x_221_; 
v_head_219_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_head_219_);
lean_dec_ref_known(v___x_205_, 2);
v_head_220_ = lean_ctor_get(v_tail_206_, 0);
lean_inc(v_head_220_);
lean_dec_ref_known(v_tail_206_, 2);
v___x_221_ = l_String_Slice_toNat_x3f(v_head_200_);
lean_dec(v_head_200_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v___x_222_; 
lean_dec(v_head_220_);
lean_dec(v_head_219_);
lean_dec(v_head_201_);
v___x_222_ = lean_box(0);
return v___x_222_;
}
else
{
lean_object* v_val_223_; lean_object* v___x_224_; 
v_val_223_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_221_, 1);
v___x_224_ = l_String_Slice_toNat_x3f(v_head_201_);
lean_dec(v_head_201_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v___x_225_; 
lean_dec(v_val_223_);
lean_dec(v_head_220_);
lean_dec(v_head_219_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
else
{
lean_object* v_val_226_; lean_object* v___x_227_; 
v_val_226_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_226_);
lean_dec_ref_known(v___x_224_, 1);
v___x_227_ = l_String_Slice_toNat_x3f(v_head_219_);
lean_dec(v_head_219_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v___x_228_; 
lean_dec(v_val_226_);
lean_dec(v_val_223_);
lean_dec(v_head_220_);
v___x_228_ = lean_box(0);
return v___x_228_;
}
else
{
lean_object* v_val_229_; lean_object* v___x_230_; 
v_val_229_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v___x_227_, 1);
v___x_230_ = l_Lake_Toml_Time_ofValid_x3f(v_val_223_, v_val_226_, v_val_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_dec(v_head_220_);
return v___x_230_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_232_; 
v_val_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = l_String_Slice_toNat_x3f(v_head_220_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; 
lean_dec(v_val_231_);
lean_dec(v_head_220_);
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_256_; 
v_val_234_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_256_ == 0)
{
v___x_236_ = v___x_232_;
v_isShared_237_ = v_isSharedCheck_256_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_val_234_);
lean_dec(v___x_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_256_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v_hour_238_; lean_object* v_minute_239_; lean_object* v_second_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_253_; 
v_hour_238_ = lean_ctor_get(v_val_231_, 0);
v_minute_239_ = lean_ctor_get(v_val_231_, 1);
v_second_240_ = lean_ctor_get(v_val_231_, 2);
v_isSharedCheck_253_ = !lean_is_exclusive(v_val_231_);
if (v_isSharedCheck_253_ == 0)
{
lean_object* v_unused_254_; lean_object* v_unused_255_; 
v_unused_254_ = lean_ctor_get(v_val_231_, 4);
lean_dec(v_unused_254_);
v_unused_255_ = lean_ctor_get(v_val_231_, 3);
lean_dec(v_unused_255_);
v___x_242_ = v_val_231_;
v_isShared_243_ = v_isSharedCheck_253_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_second_240_);
lean_inc(v_minute_239_);
lean_inc(v_hour_238_);
lean_dec(v_val_231_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_253_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_244_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_220_, v___x_181_, v___x_181_);
lean_dec(v_head_220_);
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_sub(v___x_244_, v___x_245_);
lean_dec(v___x_244_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 4, v_val_234_);
lean_ctor_set(v___x_242_, 3, v___x_246_);
v___x_248_ = v___x_242_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_hour_238_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_minute_239_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v_second_240_);
lean_ctor_set(v_reuseFailAlloc_252_, 3, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_252_, 4, v_val_234_);
v___x_248_ = v_reuseFailAlloc_252_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; 
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_248_);
v___x_250_ = v___x_236_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
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
lean_object* v___x_257_; 
lean_dec_ref_known(v_tail_206_, 2);
lean_dec_ref_known(v___x_205_, 2);
lean_dec(v_head_201_);
lean_dec(v_head_200_);
v___x_257_ = lean_box(0);
return v___x_257_;
}
}
}
else
{
lean_object* v___x_258_; 
lean_dec(v___x_205_);
lean_dec(v_head_201_);
lean_dec(v_head_200_);
v___x_258_ = lean_box(0);
return v___x_258_;
}
}
else
{
lean_object* v___x_259_; 
lean_dec_ref_known(v_tail_189_, 2);
lean_dec_ref_known(v_tail_188_, 2);
lean_dec_ref_known(v___x_187_, 2);
v___x_259_ = lean_box(0);
return v___x_259_;
}
}
}
else
{
lean_object* v___x_260_; 
lean_dec(v_tail_188_);
lean_dec_ref_known(v___x_187_, 2);
v___x_260_ = lean_box(0);
return v___x_260_;
}
}
else
{
lean_object* v___x_261_; 
lean_dec(v___x_187_);
v___x_261_ = lean_box(0);
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(lean_object* v_t_262_, lean_object* v___x_263_, lean_object* v___x_264_, lean_object* v_inst_265_, lean_object* v_R_266_, lean_object* v_a_267_, lean_object* v_b_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_262_, v___x_263_, v___x_264_, v_a_267_, v_b_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___boxed(lean_object* v_t_270_, lean_object* v___x_271_, lean_object* v___x_272_, lean_object* v_inst_273_, lean_object* v_R_274_, lean_object* v_a_275_, lean_object* v_b_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(v_t_270_, v___x_271_, v___x_272_, v_inst_273_, v_R_274_, v_a_275_, v_b_276_);
lean_dec_ref(v___x_271_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(lean_object* v_head_278_, lean_object* v_inst_279_, lean_object* v_R_280_, lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_278_, v_a_281_, v_b_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___boxed(lean_object* v_head_284_, lean_object* v_inst_285_, lean_object* v_R_286_, lean_object* v_a_287_, lean_object* v_b_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(v_head_284_, v_inst_285_, v_R_286_, v_a_287_, v_b_288_);
lean_dec_ref(v_head_284_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(lean_object* v_head_290_, lean_object* v_inst_291_, lean_object* v_R_292_, lean_object* v_a_293_, lean_object* v_b_294_, lean_object* v_c_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_290_, v_a_293_, v_b_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___boxed(lean_object* v_head_297_, lean_object* v_inst_298_, lean_object* v_R_299_, lean_object* v_a_300_, lean_object* v_b_301_, lean_object* v_c_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(v_head_297_, v_inst_298_, v_R_299_, v_a_300_, v_b_301_, v_c_302_);
lean_dec_ref(v_head_297_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_toString(lean_object* v_t_306_){
_start:
{
lean_object* v_hour_307_; lean_object* v_minute_308_; lean_object* v_second_309_; lean_object* v_fracExponent_310_; lean_object* v_fracMantissa_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_s_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_hour_307_ = lean_ctor_get(v_t_306_, 0);
lean_inc(v_hour_307_);
v_minute_308_ = lean_ctor_get(v_t_306_, 1);
lean_inc(v_minute_308_);
v_second_309_ = lean_ctor_get(v_t_306_, 2);
lean_inc(v_second_309_);
v_fracExponent_310_ = lean_ctor_get(v_t_306_, 3);
lean_inc(v_fracExponent_310_);
v_fracMantissa_311_ = lean_ctor_get(v_t_306_, 4);
lean_inc(v_fracMantissa_311_);
lean_dec_ref(v_t_306_);
v___x_312_ = lean_unsigned_to_nat(2u);
v___x_313_ = l_Lake_zpad(v_hour_307_, v___x_312_);
v___x_314_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_315_ = lean_string_append(v___x_313_, v___x_314_);
v___x_316_ = l_Lake_zpad(v_minute_308_, v___x_312_);
v___x_317_ = lean_string_append(v___x_315_, v___x_316_);
lean_dec_ref(v___x_316_);
v___x_318_ = lean_string_append(v___x_317_, v___x_314_);
v___x_319_ = l_Lake_zpad(v_second_309_, v___x_312_);
v_s_320_ = lean_string_append(v___x_318_, v___x_319_);
lean_dec_ref(v___x_319_);
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_nat_dec_eq(v_fracMantissa_311_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint32_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_323_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__1));
v___x_324_ = lean_string_append(v_s_320_, v___x_323_);
v___x_325_ = l_Lake_zpad(v_fracMantissa_311_, v_fracExponent_310_);
lean_dec(v_fracExponent_310_);
v___x_326_ = 48;
v___x_327_ = lean_unsigned_to_nat(3u);
v___x_328_ = l_Lake_rpadAscii(v___x_325_, v___x_326_, v___x_327_);
v___x_329_ = lean_string_append(v___x_324_, v___x_328_);
lean_dec_ref(v___x_328_);
return v___x_329_;
}
else
{
lean_dec(v_fracMantissa_311_);
lean_dec(v_fracExponent_310_);
return v_s_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx___impl(lean_object* v_x_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_obj_tag_nat(v_x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx___impl___boxed(lean_object* v_x_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lake_Toml_DateTime_ctorIdx___impl(v_x_334_);
lean_dec_ref(v_x_334_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___redArg(lean_object* v_t_336_, lean_object* v_k_337_){
_start:
{
switch(lean_obj_tag(v_t_336_))
{
case 0:
{
lean_object* v_date_338_; lean_object* v_time_339_; lean_object* v_offset_x3f_340_; lean_object* v___x_341_; 
v_date_338_ = lean_ctor_get(v_t_336_, 0);
lean_inc_ref(v_date_338_);
v_time_339_ = lean_ctor_get(v_t_336_, 1);
lean_inc_ref(v_time_339_);
v_offset_x3f_340_ = lean_ctor_get(v_t_336_, 2);
lean_inc(v_offset_x3f_340_);
lean_dec_ref_known(v_t_336_, 3);
v___x_341_ = lean_apply_3(v_k_337_, v_date_338_, v_time_339_, v_offset_x3f_340_);
return v___x_341_;
}
case 1:
{
lean_object* v_date_342_; lean_object* v_time_343_; lean_object* v___x_344_; 
v_date_342_ = lean_ctor_get(v_t_336_, 0);
lean_inc_ref(v_date_342_);
v_time_343_ = lean_ctor_get(v_t_336_, 1);
lean_inc_ref(v_time_343_);
lean_dec_ref_known(v_t_336_, 2);
v___x_344_ = lean_apply_2(v_k_337_, v_date_342_, v_time_343_);
return v___x_344_;
}
default: 
{
lean_object* v_date_345_; lean_object* v___x_346_; 
v_date_345_ = lean_ctor_get(v_t_336_, 0);
lean_inc_ref(v_date_345_);
lean_dec_ref(v_t_336_);
v___x_346_ = lean_apply_1(v_k_337_, v_date_345_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim(lean_object* v_motive_347_, lean_object* v_ctorIdx_348_, lean_object* v_t_349_, lean_object* v_h_350_, lean_object* v_k_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_349_, v_k_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___boxed(lean_object* v_motive_353_, lean_object* v_ctorIdx_354_, lean_object* v_t_355_, lean_object* v_h_356_, lean_object* v_k_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lake_Toml_DateTime_ctorElim(v_motive_353_, v_ctorIdx_354_, v_t_355_, v_h_356_, v_k_357_);
lean_dec(v_ctorIdx_354_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim___redArg(lean_object* v_t_359_, lean_object* v_offsetDateTime_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_359_, v_offsetDateTime_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim(lean_object* v_motive_362_, lean_object* v_t_363_, lean_object* v_h_364_, lean_object* v_offsetDateTime_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_363_, v_offsetDateTime_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim___redArg(lean_object* v_t_367_, lean_object* v_localDateTime_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_367_, v_localDateTime_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim(lean_object* v_motive_370_, lean_object* v_t_371_, lean_object* v_h_372_, lean_object* v_localDateTime_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_371_, v_localDateTime_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim___redArg(lean_object* v_t_375_, lean_object* v_localDate_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_375_, v_localDate_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim(lean_object* v_motive_378_, lean_object* v_t_379_, lean_object* v_h_380_, lean_object* v_localDate_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_379_, v_localDate_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim___redArg(lean_object* v_t_383_, lean_object* v_localTime_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_383_, v_localTime_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim(lean_object* v_motive_386_, lean_object* v_t_387_, lean_object* v_h_388_, lean_object* v_localTime_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_387_, v_localTime_389_);
return v___x_390_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_391_ = lean_box(0);
v___x_392_ = ((lean_object*)(l_Lake_Toml_instInhabitedTime_default));
v___x_393_ = l_Lake_instInhabitedDate_default;
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_391_);
return v___x_394_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime_default(void){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = lean_obj_once(&l_Lake_Toml_instInhabitedDateTime_default___closed__0, &l_Lake_Toml_instInhabitedDateTime_default___closed__0_once, _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0);
return v___x_395_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime(void){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lake_Toml_instInhabitedDateTime_default;
return v___x_396_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(uint8_t v___x_397_, uint8_t v___y_398_, uint8_t v___y_399_){
_start:
{
if (v___y_399_ == 0)
{
if (v___y_398_ == 0)
{
return v___x_397_;
}
else
{
return v___y_399_;
}
}
else
{
return v___y_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed(lean_object* v___x_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
uint8_t v___x_876__boxed_403_; uint8_t v___y_877__boxed_404_; uint8_t v___y_878__boxed_405_; uint8_t v_res_406_; lean_object* v_r_407_; 
v___x_876__boxed_403_ = lean_unbox(v___x_400_);
v___y_877__boxed_404_ = lean_unbox(v___y_401_);
v___y_878__boxed_405_ = lean_unbox(v___y_402_);
v_res_406_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(v___x_876__boxed_403_, v___y_877__boxed_404_, v___y_878__boxed_405_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(lean_object* v___f_408_, lean_object* v_a_409_, lean_object* v_b_410_){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqTime___boxed), 2, 0);
v___x_412_ = l_instDecidableEqProd___redArg(v___f_408_, v___x_411_, v_a_409_, v_b_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed(lean_object* v___f_413_, lean_object* v_a_414_, lean_object* v_b_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(v___f_413_, v_a_414_, v_b_415_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
switch(lean_obj_tag(v_x_418_))
{
case 0:
{
if (lean_obj_tag(v_x_419_) == 0)
{
lean_object* v_date_420_; lean_object* v_time_421_; lean_object* v_offset_x3f_422_; lean_object* v_date_423_; lean_object* v_time_424_; lean_object* v_offset_x3f_425_; uint8_t v___x_426_; 
v_date_420_ = lean_ctor_get(v_x_418_, 0);
lean_inc_ref(v_date_420_);
v_time_421_ = lean_ctor_get(v_x_418_, 1);
lean_inc_ref(v_time_421_);
v_offset_x3f_422_ = lean_ctor_get(v_x_418_, 2);
lean_inc(v_offset_x3f_422_);
lean_dec_ref_known(v_x_418_, 3);
v_date_423_ = lean_ctor_get(v_x_419_, 0);
lean_inc_ref(v_date_423_);
v_time_424_ = lean_ctor_get(v_x_419_, 1);
lean_inc_ref(v_time_424_);
v_offset_x3f_425_ = lean_ctor_get(v_x_419_, 2);
lean_inc(v_offset_x3f_425_);
lean_dec_ref_known(v_x_419_, 3);
v___x_426_ = l_Lake_instDecidableEqDate_decEq(v_date_420_, v_date_423_);
lean_dec_ref(v_date_423_);
lean_dec_ref(v_date_420_);
if (v___x_426_ == 0)
{
lean_dec(v_offset_x3f_425_);
lean_dec_ref(v_time_424_);
lean_dec(v_offset_x3f_422_);
lean_dec_ref(v_time_421_);
return v___x_426_;
}
else
{
uint8_t v___x_427_; 
v___x_427_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_421_, v_time_424_);
lean_dec_ref(v_time_424_);
lean_dec_ref(v_time_421_);
if (v___x_427_ == 0)
{
lean_dec(v_offset_x3f_425_);
lean_dec(v_offset_x3f_422_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v___f_429_; lean_object* v___f_430_; uint8_t v___x_431_; 
v___x_428_ = lean_box(v___x_427_);
v___f_429_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed), 3, 1);
lean_closure_set(v___f_429_, 0, v___x_428_);
v___f_430_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed), 3, 1);
lean_closure_set(v___f_430_, 0, v___f_429_);
v___x_431_ = l_Option_instDecidableEq___redArg(v___f_430_, v_offset_x3f_422_, v_offset_x3f_425_);
return v___x_431_;
}
}
}
else
{
uint8_t v___x_432_; 
lean_dec_ref_known(v_x_418_, 3);
lean_dec_ref(v_x_419_);
v___x_432_ = 0;
return v___x_432_;
}
}
case 1:
{
if (lean_obj_tag(v_x_419_) == 1)
{
lean_object* v_date_433_; lean_object* v_time_434_; lean_object* v_date_435_; lean_object* v_time_436_; uint8_t v___x_437_; 
v_date_433_ = lean_ctor_get(v_x_418_, 0);
lean_inc_ref(v_date_433_);
v_time_434_ = lean_ctor_get(v_x_418_, 1);
lean_inc_ref(v_time_434_);
lean_dec_ref_known(v_x_418_, 2);
v_date_435_ = lean_ctor_get(v_x_419_, 0);
lean_inc_ref(v_date_435_);
v_time_436_ = lean_ctor_get(v_x_419_, 1);
lean_inc_ref(v_time_436_);
lean_dec_ref_known(v_x_419_, 2);
v___x_437_ = l_Lake_instDecidableEqDate_decEq(v_date_433_, v_date_435_);
lean_dec_ref(v_date_435_);
lean_dec_ref(v_date_433_);
if (v___x_437_ == 0)
{
lean_dec_ref(v_time_436_);
lean_dec_ref(v_time_434_);
return v___x_437_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_434_, v_time_436_);
lean_dec_ref(v_time_436_);
lean_dec_ref(v_time_434_);
return v___x_438_;
}
}
else
{
uint8_t v___x_439_; 
lean_dec_ref_known(v_x_418_, 2);
lean_dec_ref(v_x_419_);
v___x_439_ = 0;
return v___x_439_;
}
}
case 2:
{
if (lean_obj_tag(v_x_419_) == 2)
{
lean_object* v_date_440_; lean_object* v_date_441_; uint8_t v___x_442_; 
v_date_440_ = lean_ctor_get(v_x_418_, 0);
lean_inc_ref(v_date_440_);
lean_dec_ref_known(v_x_418_, 1);
v_date_441_ = lean_ctor_get(v_x_419_, 0);
lean_inc_ref(v_date_441_);
lean_dec_ref_known(v_x_419_, 1);
v___x_442_ = l_Lake_instDecidableEqDate_decEq(v_date_440_, v_date_441_);
lean_dec_ref(v_date_441_);
lean_dec_ref(v_date_440_);
return v___x_442_;
}
else
{
uint8_t v___x_443_; 
lean_dec_ref_known(v_x_418_, 1);
lean_dec_ref(v_x_419_);
v___x_443_ = 0;
return v___x_443_;
}
}
default: 
{
if (lean_obj_tag(v_x_419_) == 3)
{
lean_object* v_time_444_; lean_object* v_time_445_; uint8_t v___x_446_; 
v_time_444_ = lean_ctor_get(v_x_418_, 0);
lean_inc_ref(v_time_444_);
lean_dec_ref_known(v_x_418_, 1);
v_time_445_ = lean_ctor_get(v_x_419_, 0);
lean_inc_ref(v_time_445_);
lean_dec_ref_known(v_x_419_, 1);
v___x_446_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_444_, v_time_445_);
lean_dec_ref(v_time_445_);
lean_dec_ref(v_time_444_);
return v___x_446_;
}
else
{
uint8_t v___x_447_; 
lean_dec_ref_known(v_x_418_, 1);
lean_dec_ref(v_x_419_);
v___x_447_ = 0;
return v___x_447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___boxed(lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_448_, v_x_449_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime(lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_452_, v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime___boxed(lean_object* v_x_455_, lean_object* v_x_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = l_Lake_Toml_instDecidableEqDateTime(v_x_455_, v_x_456_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeDateDateTime___lam__0(lean_object* v_date_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_460_, 0, v_date_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeTimeDateTime___lam__0(lean_object* v_time_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_464_, 0, v_time_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg___closed__0));
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg();
return v_res_472_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg();
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(lean_object* v_s_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___boxed(lean_object* v_s_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(v_s_476_);
lean_dec_ref(v_s_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg(){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg___boxed(lean_object* v___dummy_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg();
return v_res_481_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0(void){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg();
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(lean_object* v_s_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___boxed(lean_object* v_s_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(v_s_485_);
lean_dec_ref(v_s_485_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg(){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg___boxed(lean_object* v___dummy_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg();
return v_res_490_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0(void){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg();
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(lean_object* v_s_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___boxed(lean_object* v_s_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(v_s_494_);
lean_dec_ref(v_s_494_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(lean_object* v_head_496_, lean_object* v_a_497_, lean_object* v_b_498_){
_start:
{
if (lean_obj_tag(v_a_497_) == 0)
{
lean_object* v_currPos_499_; lean_object* v_searcher_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_539_; 
v_currPos_499_ = lean_ctor_get(v_a_497_, 0);
v_searcher_500_ = lean_ctor_get(v_a_497_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_a_497_);
if (v_isSharedCheck_539_ == 0)
{
v___x_502_ = v_a_497_;
v_isShared_503_ = v_isSharedCheck_539_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_searcher_500_);
lean_inc(v_currPos_499_);
lean_dec(v_a_497_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_539_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_str_504_; lean_object* v_startInclusive_505_; lean_object* v_endExclusive_506_; lean_object* v_it_508_; lean_object* v_startInclusive_509_; lean_object* v_endExclusive_510_; lean_object* v___x_517_; uint8_t v_decide_518_; 
v_str_504_ = lean_ctor_get(v_head_496_, 0);
v_startInclusive_505_ = lean_ctor_get(v_head_496_, 1);
v_endExclusive_506_ = lean_ctor_get(v_head_496_, 2);
v___x_517_ = lean_nat_sub(v_endExclusive_506_, v_startInclusive_505_);
v_decide_518_ = lean_nat_dec_eq(v_searcher_500_, v___x_517_);
if (v_decide_518_ == 0)
{
uint32_t v___x_519_; lean_object* v___x_520_; uint32_t v___x_521_; uint8_t v___x_522_; 
lean_dec(v___x_517_);
v___x_519_ = 43;
v___x_520_ = lean_nat_add(v_startInclusive_505_, v_searcher_500_);
v___x_521_ = lean_string_utf8_get_fast(v_str_504_, v___x_520_);
v___x_522_ = lean_uint32_dec_eq(v___x_521_, v___x_519_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_searcher_500_);
v___x_523_ = lean_string_utf8_next_fast(v_str_504_, v___x_520_);
lean_dec(v___x_520_);
v___x_524_ = lean_nat_sub(v___x_523_, v_startInclusive_505_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___x_524_);
v___x_526_ = v___x_502_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_currPos_499_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v___x_524_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v_a_497_ = v___x_526_;
goto _start;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_slice_532_; lean_object* v_nextIt_534_; 
v___x_529_ = lean_string_utf8_next_fast(v_str_504_, v___x_520_);
v___x_530_ = lean_nat_sub(v___x_529_, v___x_520_);
lean_dec(v___x_520_);
v___x_531_ = lean_nat_add(v_searcher_500_, v___x_530_);
lean_dec(v___x_530_);
v_slice_532_ = l_String_Slice_subslice_x21(v_head_496_, v_currPos_499_, v_searcher_500_);
lean_inc(v___x_531_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 1, v___x_531_);
lean_ctor_set(v___x_502_, 0, v___x_531_);
v_nextIt_534_ = v___x_502_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_531_);
v_nextIt_534_ = v_reuseFailAlloc_537_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v_startInclusive_535_; lean_object* v_endExclusive_536_; 
v_startInclusive_535_ = lean_ctor_get(v_slice_532_, 0);
lean_inc(v_startInclusive_535_);
v_endExclusive_536_ = lean_ctor_get(v_slice_532_, 1);
lean_inc(v_endExclusive_536_);
lean_dec_ref(v_slice_532_);
v_it_508_ = v_nextIt_534_;
v_startInclusive_509_ = v_startInclusive_535_;
v_endExclusive_510_ = v_endExclusive_536_;
goto v___jp_507_;
}
}
}
else
{
lean_object* v___x_538_; 
lean_del_object(v___x_502_);
lean_dec(v_searcher_500_);
v___x_538_ = lean_box(1);
v_it_508_ = v___x_538_;
v_startInclusive_509_ = v_currPos_499_;
v_endExclusive_510_ = v___x_517_;
goto v___jp_507_;
}
v___jp_507_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_511_ = lean_nat_add(v_startInclusive_505_, v_startInclusive_509_);
lean_dec(v_startInclusive_509_);
v___x_512_ = lean_nat_add(v_startInclusive_505_, v_endExclusive_510_);
lean_dec(v_endExclusive_510_);
lean_inc_ref(v_str_504_);
v___x_513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_513_, 0, v_str_504_);
lean_ctor_set(v___x_513_, 1, v___x_511_);
lean_ctor_set(v___x_513_, 2, v___x_512_);
v___x_514_ = l_String_Slice_toString(v___x_513_);
lean_dec_ref_known(v___x_513_, 3);
v___x_515_ = lean_array_push(v_b_498_, v___x_514_);
v_a_497_ = v_it_508_;
v_b_498_ = v___x_515_;
goto _start;
}
}
}
else
{
return v_b_498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg___boxed(lean_object* v_head_540_, lean_object* v_a_541_, lean_object* v_b_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_540_, v_a_541_, v_b_542_);
lean_dec_ref(v_head_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(lean_object* v_dt_544_, lean_object* v___x_545_, lean_object* v___x_546_, lean_object* v_a_547_, lean_object* v_b_548_){
_start:
{
lean_object* v_it_550_; lean_object* v_startInclusive_551_; lean_object* v_endExclusive_552_; 
if (lean_obj_tag(v_a_547_) == 0)
{
lean_object* v_currPos_556_; lean_object* v_searcher_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_583_; 
v_currPos_556_ = lean_ctor_get(v_a_547_, 0);
v_searcher_557_ = lean_ctor_get(v_a_547_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_a_547_);
if (v_isSharedCheck_583_ == 0)
{
v___x_559_ = v_a_547_;
v_isShared_560_ = v_isSharedCheck_583_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_searcher_557_);
lean_inc(v_currPos_556_);
lean_dec(v_a_547_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_583_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
uint8_t v_decide_571_; 
v_decide_571_ = lean_nat_dec_eq(v_searcher_557_, v___x_546_);
if (v_decide_571_ == 0)
{
uint32_t v___x_572_; uint32_t v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_string_utf8_get_fast(v_dt_544_, v_searcher_557_);
v___x_573_ = 84;
v___x_574_ = lean_uint32_dec_eq(v___x_572_, v___x_573_);
if (v___x_574_ == 0)
{
uint32_t v___x_575_; uint8_t v___x_576_; 
v___x_575_ = 116;
v___x_576_ = lean_uint32_dec_eq(v___x_572_, v___x_575_);
if (v___x_576_ == 0)
{
uint32_t v___x_577_; uint8_t v___x_578_; 
v___x_577_ = 32;
v___x_578_ = lean_uint32_dec_eq(v___x_572_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_del_object(v___x_559_);
v___x_579_ = lean_string_utf8_next_fast(v_dt_544_, v_searcher_557_);
lean_dec(v_searcher_557_);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_currPos_556_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v_a_547_ = v___x_580_;
goto _start;
}
else
{
goto v___jp_561_;
}
}
else
{
goto v___jp_561_;
}
}
else
{
goto v___jp_561_;
}
}
else
{
lean_object* v___x_582_; 
lean_del_object(v___x_559_);
lean_dec(v_searcher_557_);
v___x_582_ = lean_box(1);
lean_inc(v___x_546_);
v_it_550_ = v___x_582_;
v_startInclusive_551_ = v_currPos_556_;
v_endExclusive_552_ = v___x_546_;
goto v___jp_549_;
}
v___jp_561_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_slice_565_; lean_object* v_nextIt_567_; 
v___x_562_ = lean_string_utf8_next_fast(v_dt_544_, v_searcher_557_);
v___x_563_ = lean_nat_sub(v___x_562_, v_searcher_557_);
v___x_564_ = lean_nat_add(v_searcher_557_, v___x_563_);
lean_dec(v___x_563_);
v_slice_565_ = l_String_Slice_subslice_x21(v___x_545_, v_currPos_556_, v_searcher_557_);
lean_inc(v___x_564_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v___x_564_);
lean_ctor_set(v___x_559_, 0, v___x_564_);
v_nextIt_567_ = v___x_559_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_564_);
v_nextIt_567_ = v_reuseFailAlloc_570_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v_startInclusive_568_; lean_object* v_endExclusive_569_; 
v_startInclusive_568_ = lean_ctor_get(v_slice_565_, 0);
lean_inc(v_startInclusive_568_);
v_endExclusive_569_ = lean_ctor_get(v_slice_565_, 1);
lean_inc(v_endExclusive_569_);
lean_dec_ref(v_slice_565_);
v_it_550_ = v_nextIt_567_;
v_startInclusive_551_ = v_startInclusive_568_;
v_endExclusive_552_ = v_endExclusive_569_;
goto v___jp_549_;
}
}
}
}
else
{
lean_dec(v___x_546_);
lean_dec_ref(v_dt_544_);
return v_b_548_;
}
v___jp_549_:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_inc_ref(v_dt_544_);
v___x_553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_553_, 0, v_dt_544_);
lean_ctor_set(v___x_553_, 1, v_startInclusive_551_);
lean_ctor_set(v___x_553_, 2, v_endExclusive_552_);
v___x_554_ = lean_array_push(v_b_548_, v___x_553_);
v_a_547_ = v_it_550_;
v_b_548_ = v___x_554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg___boxed(lean_object* v_dt_584_, lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v_a_587_, lean_object* v_b_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_584_, v___x_585_, v___x_586_, v_a_587_, v_b_588_);
lean_dec_ref(v___x_585_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(lean_object* v_head_590_, lean_object* v_a_591_, lean_object* v_b_592_){
_start:
{
if (lean_obj_tag(v_a_591_) == 0)
{
lean_object* v_currPos_593_; lean_object* v_searcher_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_633_; 
v_currPos_593_ = lean_ctor_get(v_a_591_, 0);
v_searcher_594_ = lean_ctor_get(v_a_591_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_591_);
if (v_isSharedCheck_633_ == 0)
{
v___x_596_ = v_a_591_;
v_isShared_597_ = v_isSharedCheck_633_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_searcher_594_);
lean_inc(v_currPos_593_);
lean_dec(v_a_591_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_633_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v_str_598_; lean_object* v_startInclusive_599_; lean_object* v_endExclusive_600_; lean_object* v_it_602_; lean_object* v_startInclusive_603_; lean_object* v_endExclusive_604_; lean_object* v___x_611_; uint8_t v_decide_612_; 
v_str_598_ = lean_ctor_get(v_head_590_, 0);
v_startInclusive_599_ = lean_ctor_get(v_head_590_, 1);
v_endExclusive_600_ = lean_ctor_get(v_head_590_, 2);
v___x_611_ = lean_nat_sub(v_endExclusive_600_, v_startInclusive_599_);
v_decide_612_ = lean_nat_dec_eq(v_searcher_594_, v___x_611_);
if (v_decide_612_ == 0)
{
uint32_t v___x_613_; lean_object* v___x_614_; uint32_t v___x_615_; uint8_t v___x_616_; 
lean_dec(v___x_611_);
v___x_613_ = 45;
v___x_614_ = lean_nat_add(v_startInclusive_599_, v_searcher_594_);
v___x_615_ = lean_string_utf8_get_fast(v_str_598_, v___x_614_);
v___x_616_ = lean_uint32_dec_eq(v___x_615_, v___x_613_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
lean_dec(v_searcher_594_);
v___x_617_ = lean_string_utf8_next_fast(v_str_598_, v___x_614_);
lean_dec(v___x_614_);
v___x_618_ = lean_nat_sub(v___x_617_, v_startInclusive_599_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v___x_618_);
v___x_620_ = v___x_596_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_currPos_593_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___x_618_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
v_a_591_ = v___x_620_;
goto _start;
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v_slice_626_; lean_object* v_nextIt_628_; 
v___x_623_ = lean_string_utf8_next_fast(v_str_598_, v___x_614_);
v___x_624_ = lean_nat_sub(v___x_623_, v___x_614_);
lean_dec(v___x_614_);
v___x_625_ = lean_nat_add(v_searcher_594_, v___x_624_);
lean_dec(v___x_624_);
v_slice_626_ = l_String_Slice_subslice_x21(v_head_590_, v_currPos_593_, v_searcher_594_);
lean_inc(v___x_625_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v___x_625_);
lean_ctor_set(v___x_596_, 0, v___x_625_);
v_nextIt_628_ = v___x_596_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_625_);
v_nextIt_628_ = v_reuseFailAlloc_631_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v_startInclusive_629_; lean_object* v_endExclusive_630_; 
v_startInclusive_629_ = lean_ctor_get(v_slice_626_, 0);
lean_inc(v_startInclusive_629_);
v_endExclusive_630_ = lean_ctor_get(v_slice_626_, 1);
lean_inc(v_endExclusive_630_);
lean_dec_ref(v_slice_626_);
v_it_602_ = v_nextIt_628_;
v_startInclusive_603_ = v_startInclusive_629_;
v_endExclusive_604_ = v_endExclusive_630_;
goto v___jp_601_;
}
}
}
else
{
lean_object* v___x_632_; 
lean_del_object(v___x_596_);
lean_dec(v_searcher_594_);
v___x_632_ = lean_box(1);
v_it_602_ = v___x_632_;
v_startInclusive_603_ = v_currPos_593_;
v_endExclusive_604_ = v___x_611_;
goto v___jp_601_;
}
v___jp_601_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_605_ = lean_nat_add(v_startInclusive_599_, v_startInclusive_603_);
lean_dec(v_startInclusive_603_);
v___x_606_ = lean_nat_add(v_startInclusive_599_, v_endExclusive_604_);
lean_dec(v_endExclusive_604_);
lean_inc_ref(v_str_598_);
v___x_607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_607_, 0, v_str_598_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
lean_ctor_set(v___x_607_, 2, v___x_606_);
v___x_608_ = l_String_Slice_toString(v___x_607_);
lean_dec_ref_known(v___x_607_, 3);
v___x_609_ = lean_array_push(v_b_592_, v___x_608_);
v_a_591_ = v_it_602_;
v_b_592_ = v___x_609_;
goto _start;
}
}
}
else
{
return v_b_592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg___boxed(lean_object* v_head_634_, lean_object* v_a_635_, lean_object* v_b_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_634_, v_a_635_, v_b_636_);
lean_dec_ref(v_head_634_);
return v_res_637_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(lean_object* v_s_638_, lean_object* v_a_639_, uint8_t v_b_640_){
_start:
{
lean_object* v_str_641_; lean_object* v_startInclusive_642_; lean_object* v_endExclusive_643_; lean_object* v___x_644_; uint8_t v_decide_645_; 
v_str_641_ = lean_ctor_get(v_s_638_, 0);
v_startInclusive_642_ = lean_ctor_get(v_s_638_, 1);
v_endExclusive_643_ = lean_ctor_get(v_s_638_, 2);
v___x_644_ = lean_nat_sub(v_endExclusive_643_, v_startInclusive_642_);
v_decide_645_ = lean_nat_dec_eq(v_a_639_, v___x_644_);
lean_dec(v___x_644_);
if (v_decide_645_ == 0)
{
lean_object* v___x_646_; uint32_t v___x_647_; uint32_t v___x_648_; uint8_t v___x_649_; 
v___x_646_ = lean_nat_add(v_startInclusive_642_, v_a_639_);
lean_dec(v_a_639_);
v___x_647_ = lean_string_utf8_get_fast(v_str_641_, v___x_646_);
v___x_648_ = 58;
v___x_649_ = lean_uint32_dec_eq(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_string_utf8_next_fast(v_str_641_, v___x_646_);
lean_dec(v___x_646_);
v___x_651_ = lean_nat_sub(v___x_650_, v_startInclusive_642_);
v_a_639_ = v___x_651_;
v_b_640_ = v___x_649_;
goto _start;
}
else
{
lean_dec(v___x_646_);
return v___x_649_;
}
}
else
{
lean_dec(v_a_639_);
return v_b_640_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_s_653_, lean_object* v_a_654_, lean_object* v_b_655_){
_start:
{
uint8_t v_b_boxed_656_; uint8_t v_res_657_; lean_object* v_r_658_; 
v_b_boxed_656_ = lean_unbox(v_b_655_);
v_res_657_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_653_, v_a_654_, v_b_boxed_656_);
lean_dec_ref(v_s_653_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(lean_object* v_s_659_){
_start:
{
lean_object* v_searcher_660_; uint8_t v___x_661_; uint8_t v___x_662_; 
v_searcher_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = 0;
v___x_662_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_659_, v_searcher_660_, v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2___boxed(lean_object* v_s_663_){
_start:
{
uint8_t v_res_664_; lean_object* v_r_665_; 
v_res_664_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_s_663_);
lean_dec_ref(v_s_663_);
v_r_665_ = lean_box(v_res_664_);
return v_r_665_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ofString_x3f(lean_object* v_dt_666_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_667_ = lean_unsigned_to_nat(0u);
v___x_668_ = lean_string_utf8_byte_size(v_dt_666_);
lean_inc_ref(v_dt_666_);
v___x_669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_669_, 0, v_dt_666_);
lean_ctor_set(v___x_669_, 1, v___x_667_);
lean_ctor_set(v___x_669_, 2, v___x_668_);
v___x_670_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0);
v___x_671_ = ((lean_object*)(l_Lake_Toml_Time_ofString_x3f___closed__0));
v___x_672_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_666_, v___x_669_, v___x_668_, v___x_670_, v___x_671_);
lean_dec_ref_known(v___x_669_, 3);
v___x_673_ = lean_array_to_list(v___x_672_);
if (lean_obj_tag(v___x_673_) == 1)
{
lean_object* v_tail_674_; 
v_tail_674_ = lean_ctor_get(v___x_673_, 1);
lean_inc(v_tail_674_);
if (lean_obj_tag(v_tail_674_) == 0)
{
lean_object* v_head_675_; uint8_t v___x_676_; 
v_head_675_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_head_675_);
lean_dec_ref_known(v___x_673_, 2);
v___x_676_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_head_675_);
if (v___x_676_ == 0)
{
lean_object* v_str_677_; lean_object* v_startInclusive_678_; lean_object* v_endExclusive_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v_str_677_ = lean_ctor_get(v_head_675_, 0);
lean_inc_ref(v_str_677_);
v_startInclusive_678_ = lean_ctor_get(v_head_675_, 1);
lean_inc(v_startInclusive_678_);
v_endExclusive_679_ = lean_ctor_get(v_head_675_, 2);
lean_inc(v_endExclusive_679_);
lean_dec(v_head_675_);
v___x_680_ = lean_string_utf8_extract_fast(v_str_677_, v_startInclusive_678_, v_endExclusive_679_);
lean_dec(v_endExclusive_679_);
lean_dec(v_startInclusive_678_);
lean_dec_ref(v_str_677_);
v___x_681_ = l_Lake_Date_ofString_x3f(v___x_680_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v___x_682_; 
v___x_682_ = lean_box(0);
return v___x_682_;
}
else
{
lean_object* v_val_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_691_; 
v_val_683_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_691_ == 0)
{
v___x_685_ = v___x_681_;
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_val_683_);
lean_dec(v___x_681_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_691_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_687_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_687_, 0, v_val_683_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_687_);
v___x_689_ = v___x_685_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v_str_692_; lean_object* v_startInclusive_693_; lean_object* v_endExclusive_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v_str_692_ = lean_ctor_get(v_head_675_, 0);
lean_inc_ref(v_str_692_);
v_startInclusive_693_ = lean_ctor_get(v_head_675_, 1);
lean_inc(v_startInclusive_693_);
v_endExclusive_694_ = lean_ctor_get(v_head_675_, 2);
lean_inc(v_endExclusive_694_);
lean_dec(v_head_675_);
v___x_695_ = lean_string_utf8_extract_fast(v_str_692_, v_startInclusive_693_, v_endExclusive_694_);
lean_dec(v_endExclusive_694_);
lean_dec(v_startInclusive_693_);
lean_dec_ref(v_str_692_);
v___x_696_ = l_Lake_Toml_Time_ofString_x3f(v___x_695_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_697_; 
v___x_697_ = lean_box(0);
return v___x_697_;
}
else
{
lean_object* v_val_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_706_; 
v_val_698_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_706_ == 0)
{
v___x_700_ = v___x_696_;
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_val_698_);
lean_dec(v___x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_706_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_704_; 
v___x_702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_702_, 0, v_val_698_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v___x_702_);
v___x_704_ = v___x_700_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
else
{
lean_object* v_tail_707_; 
v_tail_707_ = lean_ctor_get(v_tail_674_, 1);
if (lean_obj_tag(v_tail_707_) == 0)
{
lean_object* v_head_708_; lean_object* v_head_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_884_; 
v_head_708_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_head_708_);
lean_dec_ref_known(v___x_673_, 2);
v_head_709_ = lean_ctor_get(v_tail_674_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v_tail_674_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v_tail_674_, 1);
lean_dec(v_unused_885_);
v___x_711_ = v_tail_674_;
v_isShared_712_ = v_isSharedCheck_884_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_head_709_);
lean_dec(v_tail_674_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_884_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_str_713_; lean_object* v_startInclusive_714_; lean_object* v_endExclusive_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_str_713_ = lean_ctor_get(v_head_708_, 0);
lean_inc_ref(v_str_713_);
v_startInclusive_714_ = lean_ctor_get(v_head_708_, 1);
lean_inc(v_startInclusive_714_);
v_endExclusive_715_ = lean_ctor_get(v_head_708_, 2);
lean_inc(v_endExclusive_715_);
lean_dec(v_head_708_);
v___x_716_ = lean_string_utf8_extract_fast(v_str_713_, v_startInclusive_714_, v_endExclusive_715_);
lean_dec(v_endExclusive_715_);
lean_dec(v_startInclusive_714_);
lean_dec_ref(v_str_713_);
v___x_717_ = l_Lake_Date_ofString_x3f(v___x_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v___x_718_; 
lean_del_object(v___x_711_);
lean_dec(v_head_709_);
v___x_718_ = lean_box(0);
return v___x_718_;
}
else
{
lean_object* v_val_719_; lean_object* v_str_720_; lean_object* v_startInclusive_721_; lean_object* v_endExclusive_722_; uint8_t v___y_739_; uint32_t v___y_814_; uint32_t v___y_867_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_val_719_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v___x_717_, 1);
v_str_720_ = lean_ctor_get(v_head_709_, 0);
v_startInclusive_721_ = lean_ctor_get(v_head_709_, 1);
v_endExclusive_722_ = lean_ctor_get(v_head_709_, 2);
v___x_878_ = lean_nat_sub(v_endExclusive_722_, v_startInclusive_721_);
v___x_879_ = l_String_Slice_Pos_prev_x3f(v_head_709_, v___x_878_);
lean_dec(v___x_878_);
if (lean_obj_tag(v___x_879_) == 0)
{
goto v___jp_876_;
}
else
{
lean_object* v_val_880_; lean_object* v___x_881_; 
v_val_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_val_880_);
lean_dec_ref_known(v___x_879_, 1);
v___x_881_ = l_String_Slice_Pos_get_x3f(v_head_709_, v_val_880_);
lean_dec(v_val_880_);
if (lean_obj_tag(v___x_881_) == 0)
{
goto v___jp_876_;
}
else
{
lean_object* v_val_882_; uint32_t v___x_883_; 
v_val_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = lean_unbox_uint32(v_val_882_);
lean_dec(v_val_882_);
v___y_867_ = v___x_883_;
goto v___jp_866_;
}
}
v___jp_723_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_string_utf8_extract_fast(v_str_720_, v_startInclusive_721_, v_endExclusive_722_);
lean_dec(v_endExclusive_722_);
lean_dec(v_startInclusive_721_);
lean_dec_ref(v_str_720_);
v___x_725_ = l_Lake_Toml_Time_ofString_x3f(v___x_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_726_; 
lean_dec(v_val_719_);
lean_del_object(v___x_711_);
v___x_726_ = lean_box(0);
return v___x_726_;
}
else
{
lean_object* v_val_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_737_; 
v_val_727_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_737_ == 0)
{
v___x_729_ = v___x_725_;
v_isShared_730_ = v_isSharedCheck_737_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_val_727_);
lean_dec(v___x_725_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_737_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 1, v_val_727_);
lean_ctor_set(v___x_711_, 0, v_val_719_);
v___x_732_ = v___x_711_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_val_719_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v_val_727_);
v___x_732_ = v_reuseFailAlloc_736_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_734_; 
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 0, v___x_732_);
v___x_734_ = v___x_729_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
v___jp_738_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_782_; 
v___x_740_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0);
v___x_741_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_709_, v___x_740_, v___x_671_);
v_isSharedCheck_782_ = !lean_is_exclusive(v_head_709_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; lean_object* v_unused_784_; lean_object* v_unused_785_; 
v_unused_783_ = lean_ctor_get(v_head_709_, 2);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_head_709_, 1);
lean_dec(v_unused_784_);
v_unused_785_ = lean_ctor_get(v_head_709_, 0);
lean_dec(v_unused_785_);
v___x_743_ = v_head_709_;
v_isShared_744_ = v_isSharedCheck_782_;
goto v_resetjp_742_;
}
else
{
lean_dec(v_head_709_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_782_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; 
v___x_745_ = lean_array_to_list(v___x_741_);
if (lean_obj_tag(v___x_745_) == 1)
{
lean_object* v_tail_746_; 
v_tail_746_ = lean_ctor_get(v___x_745_, 1);
lean_inc(v_tail_746_);
if (lean_obj_tag(v_tail_746_) == 1)
{
lean_object* v_tail_747_; 
v_tail_747_ = lean_ctor_get(v_tail_746_, 1);
if (lean_obj_tag(v_tail_747_) == 0)
{
lean_object* v_head_748_; lean_object* v_head_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_endExclusive_722_);
lean_dec(v_startInclusive_721_);
lean_dec_ref(v_str_720_);
lean_del_object(v___x_711_);
v_head_748_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_head_748_);
lean_dec_ref_known(v___x_745_, 2);
v_head_749_ = lean_ctor_get(v_tail_746_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v_tail_746_);
if (v_isSharedCheck_780_ == 0)
{
lean_object* v_unused_781_; 
v_unused_781_ = lean_ctor_get(v_tail_746_, 1);
lean_dec(v_unused_781_);
v___x_751_ = v_tail_746_;
v_isShared_752_ = v_isSharedCheck_780_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_head_749_);
lean_dec(v_tail_746_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_780_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lake_Toml_Time_ofString_x3f(v_head_748_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v___x_754_; 
lean_del_object(v___x_751_);
lean_dec(v_head_749_);
lean_del_object(v___x_743_);
lean_dec(v_val_719_);
v___x_754_ = lean_box(0);
return v___x_754_;
}
else
{
lean_object* v_val_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_779_; 
v_val_755_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_779_ == 0)
{
v___x_757_ = v___x_753_;
v_isShared_758_ = v_isSharedCheck_779_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_val_755_);
lean_dec(v___x_753_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_779_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lake_Toml_Time_ofString_x3f(v_head_749_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v___x_760_; 
lean_del_object(v___x_757_);
lean_dec(v_val_755_);
lean_del_object(v___x_751_);
lean_del_object(v___x_743_);
lean_dec(v_val_719_);
v___x_760_ = lean_box(0);
return v___x_760_;
}
else
{
lean_object* v_val_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_778_; 
v_val_761_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_778_ == 0)
{
v___x_763_ = v___x_759_;
v_isShared_764_ = v_isSharedCheck_778_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_val_761_);
lean_dec(v___x_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_778_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_box(v___y_739_);
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 0);
lean_ctor_set(v___x_751_, 1, v_val_761_);
lean_ctor_set(v___x_751_, 0, v___x_765_);
v___x_767_ = v___x_751_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_val_761_);
v___x_767_ = v_reuseFailAlloc_777_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_767_);
v___x_769_ = v___x_763_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_767_);
v___x_769_ = v_reuseFailAlloc_776_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_771_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 2, v___x_769_);
lean_ctor_set(v___x_743_, 1, v_val_755_);
lean_ctor_set(v___x_743_, 0, v_val_719_);
v___x_771_ = v___x_743_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_val_719_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_val_755_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v___x_769_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_773_; 
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_771_);
v___x_773_ = v___x_757_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
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
lean_dec_ref_known(v_tail_746_, 2);
lean_dec_ref_known(v___x_745_, 2);
lean_del_object(v___x_743_);
goto v___jp_723_;
}
}
else
{
lean_dec_ref_known(v___x_745_, 2);
lean_dec(v_tail_746_);
lean_del_object(v___x_743_);
goto v___jp_723_;
}
}
else
{
lean_dec(v___x_745_);
lean_del_object(v___x_743_);
goto v___jp_723_;
}
}
}
v___jp_786_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_809_; 
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = lean_nat_sub(v_endExclusive_722_, v_startInclusive_721_);
v___x_789_ = l_String_Slice_Pos_prevn(v_head_709_, v___x_788_, v___x_787_);
v_isSharedCheck_809_ = !lean_is_exclusive(v_head_709_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; lean_object* v_unused_811_; lean_object* v_unused_812_; 
v_unused_810_ = lean_ctor_get(v_head_709_, 2);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_head_709_, 1);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_head_709_, 0);
lean_dec(v_unused_812_);
v___x_791_ = v_head_709_;
v_isShared_792_ = v_isSharedCheck_809_;
goto v_resetjp_790_;
}
else
{
lean_dec(v_head_709_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_809_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_793_ = lean_nat_add(v_startInclusive_721_, v___x_789_);
lean_dec(v___x_789_);
v___x_794_ = lean_string_utf8_extract_fast(v_str_720_, v_startInclusive_721_, v___x_793_);
lean_dec(v___x_793_);
lean_dec(v_startInclusive_721_);
lean_dec_ref(v_str_720_);
v___x_795_ = l_Lake_Toml_Time_ofString_x3f(v___x_794_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v___x_796_; 
lean_del_object(v___x_791_);
lean_dec(v_val_719_);
v___x_796_ = lean_box(0);
return v___x_796_;
}
else
{
lean_object* v_val_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_808_; 
v_val_797_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_808_ == 0)
{
v___x_799_ = v___x_795_;
v_isShared_800_ = v_isSharedCheck_808_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_val_797_);
lean_dec(v___x_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_808_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_801_ = lean_box(0);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 2, v___x_801_);
lean_ctor_set(v___x_791_, 1, v_val_797_);
lean_ctor_set(v___x_791_, 0, v_val_719_);
v___x_803_ = v___x_791_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_val_719_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_val_797_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v___x_801_);
v___x_803_ = v_reuseFailAlloc_807_;
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
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
v___jp_813_:
{
uint32_t v___x_815_; uint8_t v___x_816_; 
v___x_815_ = 122;
v___x_816_ = lean_uint32_dec_eq(v___y_814_, v___x_815_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_817_ = 1;
v___x_818_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0);
v___x_819_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_709_, v___x_818_, v___x_671_);
v___x_820_ = lean_array_to_list(v___x_819_);
if (lean_obj_tag(v___x_820_) == 1)
{
lean_object* v_tail_821_; 
v_tail_821_ = lean_ctor_get(v___x_820_, 1);
lean_inc(v_tail_821_);
if (lean_obj_tag(v_tail_821_) == 1)
{
lean_object* v_tail_822_; 
v_tail_822_ = lean_ctor_get(v_tail_821_, 1);
if (lean_obj_tag(v_tail_822_) == 0)
{
lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_860_; 
lean_del_object(v___x_711_);
v_isSharedCheck_860_ = !lean_is_exclusive(v_head_709_);
if (v_isSharedCheck_860_ == 0)
{
lean_object* v_unused_861_; lean_object* v_unused_862_; lean_object* v_unused_863_; 
v_unused_861_ = lean_ctor_get(v_head_709_, 2);
lean_dec(v_unused_861_);
v_unused_862_ = lean_ctor_get(v_head_709_, 1);
lean_dec(v_unused_862_);
v_unused_863_ = lean_ctor_get(v_head_709_, 0);
lean_dec(v_unused_863_);
v___x_824_ = v_head_709_;
v_isShared_825_ = v_isSharedCheck_860_;
goto v_resetjp_823_;
}
else
{
lean_dec(v_head_709_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_860_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_head_826_; lean_object* v_head_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_858_; 
v_head_826_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_head_826_);
lean_dec_ref_known(v___x_820_, 2);
v_head_827_ = lean_ctor_get(v_tail_821_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_tail_821_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_tail_821_, 1);
lean_dec(v_unused_859_);
v___x_829_ = v_tail_821_;
v_isShared_830_ = v_isSharedCheck_858_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_head_827_);
lean_dec(v_tail_821_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_858_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lake_Toml_Time_ofString_x3f(v_head_826_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v___x_832_; 
lean_del_object(v___x_829_);
lean_dec(v_head_827_);
lean_del_object(v___x_824_);
lean_dec(v_val_719_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
lean_object* v_val_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_857_; 
v_val_833_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_857_ == 0)
{
v___x_835_ = v___x_831_;
v_isShared_836_ = v_isSharedCheck_857_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_val_833_);
lean_dec(v___x_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_857_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lake_Toml_Time_ofString_x3f(v_head_827_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v___x_838_; 
lean_del_object(v___x_835_);
lean_dec(v_val_833_);
lean_del_object(v___x_829_);
lean_del_object(v___x_824_);
lean_dec(v_val_719_);
v___x_838_ = lean_box(0);
return v___x_838_;
}
else
{
lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_856_; 
v_val_839_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_856_ == 0)
{
v___x_841_ = v___x_837_;
v_isShared_842_ = v_isSharedCheck_856_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_dec(v___x_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_856_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_box(v___x_816_);
if (v_isShared_830_ == 0)
{
lean_ctor_set_tag(v___x_829_, 0);
lean_ctor_set(v___x_829_, 1, v_val_839_);
lean_ctor_set(v___x_829_, 0, v___x_843_);
v___x_845_ = v___x_829_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_val_839_);
v___x_845_ = v_reuseFailAlloc_855_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
lean_object* v___x_847_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_845_);
v___x_847_ = v___x_841_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_854_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 2, v___x_847_);
lean_ctor_set(v___x_824_, 1, v_val_833_);
lean_ctor_set(v___x_824_, 0, v_val_719_);
v___x_849_ = v___x_824_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_val_719_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_val_833_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v___x_847_);
v___x_849_ = v_reuseFailAlloc_853_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_851_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_849_);
v___x_851_ = v___x_835_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
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
lean_inc(v_endExclusive_722_);
lean_inc(v_startInclusive_721_);
lean_inc_ref(v_str_720_);
lean_dec_ref_known(v_tail_821_, 2);
lean_dec_ref_known(v___x_820_, 2);
v___y_739_ = v___x_817_;
goto v___jp_738_;
}
}
else
{
lean_inc(v_endExclusive_722_);
lean_inc(v_startInclusive_721_);
lean_inc_ref(v_str_720_);
lean_dec(v_tail_821_);
lean_dec_ref_known(v___x_820_, 2);
v___y_739_ = v___x_817_;
goto v___jp_738_;
}
}
else
{
lean_inc(v_endExclusive_722_);
lean_inc(v_startInclusive_721_);
lean_inc_ref(v_str_720_);
lean_dec(v___x_820_);
v___y_739_ = v___x_817_;
goto v___jp_738_;
}
}
else
{
lean_inc(v_startInclusive_721_);
lean_inc_ref(v_str_720_);
lean_del_object(v___x_711_);
goto v___jp_786_;
}
}
v___jp_864_:
{
uint32_t v___x_865_; 
v___x_865_ = 65;
v___y_814_ = v___x_865_;
goto v___jp_813_;
}
v___jp_866_:
{
uint32_t v___x_868_; uint8_t v___x_869_; 
v___x_868_ = 90;
v___x_869_ = lean_uint32_dec_eq(v___y_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_nat_sub(v_endExclusive_722_, v_startInclusive_721_);
v___x_871_ = l_String_Slice_Pos_prev_x3f(v_head_709_, v___x_870_);
lean_dec(v___x_870_);
if (lean_obj_tag(v___x_871_) == 0)
{
goto v___jp_864_;
}
else
{
lean_object* v_val_872_; lean_object* v___x_873_; 
v_val_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = l_String_Slice_Pos_get_x3f(v_head_709_, v_val_872_);
lean_dec(v_val_872_);
if (lean_obj_tag(v___x_873_) == 0)
{
goto v___jp_864_;
}
else
{
lean_object* v_val_874_; uint32_t v___x_875_; 
v_val_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_val_874_);
lean_dec_ref_known(v___x_873_, 1);
v___x_875_ = lean_unbox_uint32(v_val_874_);
lean_dec(v_val_874_);
v___y_814_ = v___x_875_;
goto v___jp_813_;
}
}
}
else
{
lean_inc(v_startInclusive_721_);
lean_inc_ref(v_str_720_);
lean_del_object(v___x_711_);
goto v___jp_786_;
}
}
v___jp_876_:
{
uint32_t v___x_877_; 
v___x_877_ = 65;
v___y_867_ = v___x_877_;
goto v___jp_866_;
}
}
}
}
else
{
lean_object* v___x_886_; 
lean_dec_ref_known(v_tail_674_, 2);
lean_dec_ref_known(v___x_673_, 2);
v___x_886_ = lean_box(0);
return v___x_886_;
}
}
}
else
{
lean_object* v___x_887_; 
lean_dec(v___x_673_);
v___x_887_ = lean_box(0);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(lean_object* v_dt_888_, lean_object* v___x_889_, lean_object* v___x_890_, lean_object* v_inst_891_, lean_object* v_R_892_, lean_object* v_a_893_, lean_object* v_b_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_888_, v___x_889_, v___x_890_, v_a_893_, v_b_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___boxed(lean_object* v_dt_896_, lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_inst_899_, lean_object* v_R_900_, lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(v_dt_896_, v___x_897_, v___x_898_, v_inst_899_, v_R_900_, v_a_901_, v_b_902_);
lean_dec_ref(v___x_897_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(lean_object* v_head_904_, lean_object* v_inst_905_, lean_object* v_R_906_, lean_object* v_a_907_, lean_object* v_b_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_904_, v_a_907_, v_b_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___boxed(lean_object* v_head_910_, lean_object* v_inst_911_, lean_object* v_R_912_, lean_object* v_a_913_, lean_object* v_b_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(v_head_910_, v_inst_911_, v_R_912_, v_a_913_, v_b_914_);
lean_dec_ref(v_head_910_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(lean_object* v_head_916_, lean_object* v_inst_917_, lean_object* v_R_918_, lean_object* v_a_919_, lean_object* v_b_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_916_, v_a_919_, v_b_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___boxed(lean_object* v_head_922_, lean_object* v_inst_923_, lean_object* v_R_924_, lean_object* v_a_925_, lean_object* v_b_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(v_head_922_, v_inst_923_, v_R_924_, v_a_925_, v_b_926_);
lean_dec_ref(v_head_922_);
return v_res_927_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(lean_object* v_s_928_, lean_object* v_inst_929_, lean_object* v_R_930_, lean_object* v_a_931_, uint8_t v_b_932_, lean_object* v_c_933_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_928_, v_a_931_, v_b_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___boxed(lean_object* v_s_935_, lean_object* v_inst_936_, lean_object* v_R_937_, lean_object* v_a_938_, lean_object* v_b_939_, lean_object* v_c_940_){
_start:
{
uint8_t v_b_boxed_941_; uint8_t v_res_942_; lean_object* v_r_943_; 
v_b_boxed_941_ = lean_unbox(v_b_939_);
v_res_942_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(v_s_935_, v_inst_936_, v_R_937_, v_a_938_, v_b_boxed_941_, v_c_940_);
lean_dec_ref(v_s_935_);
v_r_943_ = lean_box(v_res_942_);
return v_r_943_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_toString(lean_object* v_dt_948_){
_start:
{
switch(lean_obj_tag(v_dt_948_))
{
case 0:
{
lean_object* v_offset_x3f_949_; 
v_offset_x3f_949_ = lean_ctor_get(v_dt_948_, 2);
if (lean_obj_tag(v_offset_x3f_949_) == 1)
{
lean_object* v_val_950_; lean_object* v_fst_951_; uint8_t v___x_952_; 
v_val_950_ = lean_ctor_get(v_offset_x3f_949_, 0);
v_fst_951_ = lean_ctor_get(v_val_950_, 0);
v___x_952_ = lean_unbox(v_fst_951_);
if (v___x_952_ == 0)
{
lean_object* v_snd_953_; lean_object* v_date_954_; lean_object* v_time_955_; lean_object* v_hour_956_; lean_object* v_minute_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_snd_953_ = lean_ctor_get(v_val_950_, 1);
lean_inc(v_snd_953_);
v_date_954_ = lean_ctor_get(v_dt_948_, 0);
lean_inc_ref(v_date_954_);
v_time_955_ = lean_ctor_get(v_dt_948_, 1);
lean_inc_ref(v_time_955_);
lean_dec_ref_known(v_dt_948_, 3);
v_hour_956_ = lean_ctor_get(v_snd_953_, 0);
lean_inc(v_hour_956_);
v_minute_957_ = lean_ctor_get(v_snd_953_, 1);
lean_inc(v_minute_957_);
lean_dec(v_snd_953_);
v___x_958_ = l_Lake_Date_toString(v_date_954_);
v___x_959_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_960_ = lean_string_append(v___x_958_, v___x_959_);
v___x_961_ = l_Lake_Toml_Time_toString(v_time_955_);
v___x_962_ = lean_string_append(v___x_960_, v___x_961_);
lean_dec_ref(v___x_961_);
v___x_963_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__1));
v___x_964_ = lean_string_append(v___x_962_, v___x_963_);
v___x_965_ = lean_unsigned_to_nat(2u);
v___x_966_ = l_Lake_zpad(v_hour_956_, v___x_965_);
v___x_967_ = lean_string_append(v___x_964_, v___x_966_);
lean_dec_ref(v___x_966_);
v___x_968_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_969_ = lean_string_append(v___x_967_, v___x_968_);
v___x_970_ = l_Lake_zpad(v_minute_957_, v___x_965_);
v___x_971_ = lean_string_append(v___x_969_, v___x_970_);
lean_dec_ref(v___x_970_);
return v___x_971_;
}
else
{
lean_object* v_snd_972_; lean_object* v_date_973_; lean_object* v_time_974_; lean_object* v_hour_975_; lean_object* v_minute_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_snd_972_ = lean_ctor_get(v_val_950_, 1);
lean_inc(v_snd_972_);
v_date_973_ = lean_ctor_get(v_dt_948_, 0);
lean_inc_ref(v_date_973_);
v_time_974_ = lean_ctor_get(v_dt_948_, 1);
lean_inc_ref(v_time_974_);
lean_dec_ref_known(v_dt_948_, 3);
v_hour_975_ = lean_ctor_get(v_snd_972_, 0);
lean_inc(v_hour_975_);
v_minute_976_ = lean_ctor_get(v_snd_972_, 1);
lean_inc(v_minute_976_);
lean_dec(v_snd_972_);
v___x_977_ = l_Lake_Date_toString(v_date_973_);
v___x_978_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
v___x_980_ = l_Lake_Toml_Time_toString(v_time_974_);
v___x_981_ = lean_string_append(v___x_979_, v___x_980_);
lean_dec_ref(v___x_980_);
v___x_982_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__2));
v___x_983_ = lean_string_append(v___x_981_, v___x_982_);
v___x_984_ = lean_unsigned_to_nat(2u);
v___x_985_ = l_Lake_zpad(v_hour_975_, v___x_984_);
v___x_986_ = lean_string_append(v___x_983_, v___x_985_);
lean_dec_ref(v___x_985_);
v___x_987_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_988_ = lean_string_append(v___x_986_, v___x_987_);
v___x_989_ = l_Lake_zpad(v_minute_976_, v___x_984_);
v___x_990_ = lean_string_append(v___x_988_, v___x_989_);
lean_dec_ref(v___x_989_);
return v___x_990_;
}
}
else
{
lean_object* v_date_991_; lean_object* v_time_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_date_991_ = lean_ctor_get(v_dt_948_, 0);
lean_inc_ref(v_date_991_);
v_time_992_ = lean_ctor_get(v_dt_948_, 1);
lean_inc_ref(v_time_992_);
lean_dec_ref_known(v_dt_948_, 3);
v___x_993_ = l_Lake_Date_toString(v_date_991_);
v___x_994_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_995_ = lean_string_append(v___x_993_, v___x_994_);
v___x_996_ = l_Lake_Toml_Time_toString(v_time_992_);
v___x_997_ = lean_string_append(v___x_995_, v___x_996_);
lean_dec_ref(v___x_996_);
v___x_998_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__3));
v___x_999_ = lean_string_append(v___x_997_, v___x_998_);
return v___x_999_;
}
}
case 1:
{
lean_object* v_date_1000_; lean_object* v_time_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_date_1000_ = lean_ctor_get(v_dt_948_, 0);
lean_inc_ref(v_date_1000_);
v_time_1001_ = lean_ctor_get(v_dt_948_, 1);
lean_inc_ref(v_time_1001_);
lean_dec_ref_known(v_dt_948_, 2);
v___x_1002_ = l_Lake_Date_toString(v_date_1000_);
v___x_1003_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_1004_ = lean_string_append(v___x_1002_, v___x_1003_);
v___x_1005_ = l_Lake_Toml_Time_toString(v_time_1001_);
v___x_1006_ = lean_string_append(v___x_1004_, v___x_1005_);
lean_dec_ref(v___x_1005_);
return v___x_1006_;
}
case 2:
{
lean_object* v_date_1007_; lean_object* v___x_1008_; 
v_date_1007_ = lean_ctor_get(v_dt_948_, 0);
lean_inc_ref(v_date_1007_);
lean_dec_ref_known(v_dt_948_, 1);
v___x_1008_ = l_Lake_Date_toString(v_date_1007_);
return v___x_1008_;
}
default: 
{
lean_object* v_time_1009_; lean_object* v___x_1010_; 
v_time_1009_ = lean_ctor_get(v_dt_948_, 0);
lean_inc_ref(v_time_1009_);
lean_dec_ref_known(v_dt_948_, 1);
v___x_1010_ = l_Lake_Toml_Time_toString(v_time_1009_);
return v___x_1010_;
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

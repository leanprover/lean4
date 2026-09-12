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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg();
return v_res_57_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg();
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(lean_object* v_s_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___boxed(lean_object* v_s_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(v_s_61_);
lean_dec_ref(v_s_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg(){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg___boxed(lean_object* v___dummy_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg();
return v_res_66_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___redArg();
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(lean_object* v_s_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___boxed(lean_object* v_s_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(v_s_70_);
lean_dec_ref(v_s_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(lean_object* v_head_72_, lean_object* v_a_73_, lean_object* v_b_74_){
_start:
{
if (lean_obj_tag(v_a_73_) == 0)
{
lean_object* v_currPos_75_; lean_object* v_searcher_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_114_; 
v_currPos_75_ = lean_ctor_get(v_a_73_, 0);
v_searcher_76_ = lean_ctor_get(v_a_73_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_a_73_);
if (v_isSharedCheck_114_ == 0)
{
v___x_78_ = v_a_73_;
v_isShared_79_ = v_isSharedCheck_114_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_searcher_76_);
lean_inc(v_currPos_75_);
lean_dec(v_a_73_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_114_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v_str_80_; lean_object* v_startInclusive_81_; lean_object* v_endExclusive_82_; lean_object* v_it_84_; lean_object* v_startInclusive_85_; lean_object* v_endExclusive_86_; lean_object* v___x_92_; uint8_t v_decide_93_; 
v_str_80_ = lean_ctor_get(v_head_72_, 0);
v_startInclusive_81_ = lean_ctor_get(v_head_72_, 1);
v_endExclusive_82_ = lean_ctor_get(v_head_72_, 2);
v___x_92_ = lean_nat_sub(v_endExclusive_82_, v_startInclusive_81_);
v_decide_93_ = lean_nat_dec_eq(v_searcher_76_, v___x_92_);
if (v_decide_93_ == 0)
{
uint32_t v___x_94_; lean_object* v___x_95_; uint32_t v___x_96_; uint8_t v___x_97_; 
lean_dec(v___x_92_);
v___x_94_ = 46;
v___x_95_ = lean_nat_add(v_startInclusive_81_, v_searcher_76_);
v___x_96_ = lean_string_utf8_get_fast(v_str_80_, v___x_95_);
v___x_97_ = lean_uint32_dec_eq(v___x_96_, v___x_94_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_101_; 
lean_dec(v_searcher_76_);
v___x_98_ = lean_string_utf8_next_fast(v_str_80_, v___x_95_);
lean_dec(v___x_95_);
v___x_99_ = lean_nat_sub(v___x_98_, v_startInclusive_81_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_99_);
v___x_101_ = v___x_78_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_currPos_75_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_99_);
v___x_101_ = v_reuseFailAlloc_103_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
v_a_73_ = v___x_101_;
goto _start;
}
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_slice_107_; lean_object* v_nextIt_109_; 
v___x_104_ = lean_string_utf8_next_fast(v_str_80_, v___x_95_);
v___x_105_ = lean_nat_sub(v___x_104_, v___x_95_);
lean_dec(v___x_95_);
v___x_106_ = lean_nat_add(v_searcher_76_, v___x_105_);
lean_dec(v___x_105_);
v_slice_107_ = l_String_Slice_subslice_x21(v_head_72_, v_currPos_75_, v_searcher_76_);
lean_inc(v___x_106_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_106_);
lean_ctor_set(v___x_78_, 0, v___x_106_);
v_nextIt_109_ = v___x_78_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_106_);
v_nextIt_109_ = v_reuseFailAlloc_112_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v_startInclusive_110_; lean_object* v_endExclusive_111_; 
v_startInclusive_110_ = lean_ctor_get(v_slice_107_, 0);
lean_inc(v_startInclusive_110_);
v_endExclusive_111_ = lean_ctor_get(v_slice_107_, 1);
lean_inc(v_endExclusive_111_);
lean_dec_ref(v_slice_107_);
v_it_84_ = v_nextIt_109_;
v_startInclusive_85_ = v_startInclusive_110_;
v_endExclusive_86_ = v_endExclusive_111_;
goto v___jp_83_;
}
}
}
else
{
lean_object* v___x_113_; 
lean_del_object(v___x_78_);
lean_dec(v_searcher_76_);
v___x_113_ = lean_box(1);
v_it_84_ = v___x_113_;
v_startInclusive_85_ = v_currPos_75_;
v_endExclusive_86_ = v___x_92_;
goto v___jp_83_;
}
v___jp_83_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = lean_nat_add(v_startInclusive_81_, v_startInclusive_85_);
lean_dec(v_startInclusive_85_);
v___x_88_ = lean_nat_add(v_startInclusive_81_, v_endExclusive_86_);
lean_dec(v_endExclusive_86_);
lean_inc_ref(v_str_80_);
v___x_89_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_89_, 0, v_str_80_);
lean_ctor_set(v___x_89_, 1, v___x_87_);
lean_ctor_set(v___x_89_, 2, v___x_88_);
v___x_90_ = lean_array_push(v_b_74_, v___x_89_);
v_a_73_ = v_it_84_;
v_b_74_ = v___x_90_;
goto _start;
}
}
}
else
{
return v_b_74_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg___boxed(lean_object* v_head_115_, lean_object* v_a_116_, lean_object* v_b_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_115_, v_a_116_, v_b_117_);
lean_dec_ref(v_head_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(lean_object* v_t_119_, lean_object* v___x_120_, lean_object* v___x_121_, lean_object* v_a_122_, lean_object* v_b_123_){
_start:
{
lean_object* v_it_125_; lean_object* v_startInclusive_126_; lean_object* v_endExclusive_127_; 
if (lean_obj_tag(v_a_122_) == 0)
{
lean_object* v_currPos_131_; lean_object* v_searcher_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_155_; 
v_currPos_131_ = lean_ctor_get(v_a_122_, 0);
v_searcher_132_ = lean_ctor_get(v_a_122_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_a_122_);
if (v_isSharedCheck_155_ == 0)
{
v___x_134_ = v_a_122_;
v_isShared_135_ = v_isSharedCheck_155_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_searcher_132_);
lean_inc(v_currPos_131_);
lean_dec(v_a_122_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_155_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
uint8_t v_decide_136_; 
v_decide_136_ = lean_nat_dec_eq(v_searcher_132_, v___x_121_);
if (v_decide_136_ == 0)
{
uint32_t v___x_137_; uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_137_ = 58;
v___x_138_ = lean_string_utf8_get_fast(v_t_119_, v_searcher_132_);
v___x_139_ = lean_uint32_dec_eq(v___x_138_, v___x_137_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = lean_string_utf8_next_fast(v_t_119_, v_searcher_132_);
lean_dec(v_searcher_132_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_140_);
v___x_142_ = v___x_134_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_currPos_131_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_144_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
v_a_122_ = v___x_142_;
goto _start;
}
}
else
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_slice_148_; lean_object* v_nextIt_150_; 
v___x_145_ = lean_string_utf8_next_fast(v_t_119_, v_searcher_132_);
v___x_146_ = lean_nat_sub(v___x_145_, v_searcher_132_);
v___x_147_ = lean_nat_add(v_searcher_132_, v___x_146_);
lean_dec(v___x_146_);
v_slice_148_ = l_String_Slice_subslice_x21(v___x_120_, v_currPos_131_, v_searcher_132_);
lean_inc(v___x_147_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 1, v___x_147_);
lean_ctor_set(v___x_134_, 0, v___x_147_);
v_nextIt_150_ = v___x_134_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v___x_147_);
v_nextIt_150_ = v_reuseFailAlloc_153_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_object* v_startInclusive_151_; lean_object* v_endExclusive_152_; 
v_startInclusive_151_ = lean_ctor_get(v_slice_148_, 0);
lean_inc(v_startInclusive_151_);
v_endExclusive_152_ = lean_ctor_get(v_slice_148_, 1);
lean_inc(v_endExclusive_152_);
lean_dec_ref(v_slice_148_);
v_it_125_ = v_nextIt_150_;
v_startInclusive_126_ = v_startInclusive_151_;
v_endExclusive_127_ = v_endExclusive_152_;
goto v___jp_124_;
}
}
}
else
{
lean_object* v___x_154_; 
lean_del_object(v___x_134_);
lean_dec(v_searcher_132_);
v___x_154_ = lean_box(1);
lean_inc(v___x_121_);
v_it_125_ = v___x_154_;
v_startInclusive_126_ = v_currPos_131_;
v_endExclusive_127_ = v___x_121_;
goto v___jp_124_;
}
}
}
else
{
lean_dec(v___x_121_);
lean_dec_ref(v_t_119_);
return v_b_123_;
}
v___jp_124_:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_inc_ref(v_t_119_);
v___x_128_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_128_, 0, v_t_119_);
lean_ctor_set(v___x_128_, 1, v_startInclusive_126_);
lean_ctor_set(v___x_128_, 2, v_endExclusive_127_);
v___x_129_ = lean_array_push(v_b_123_, v___x_128_);
v_a_122_ = v_it_125_;
v_b_123_ = v___x_129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg___boxed(lean_object* v_t_156_, lean_object* v___x_157_, lean_object* v___x_158_, lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_156_, v___x_157_, v___x_158_, v_a_159_, v_b_160_);
lean_dec_ref(v___x_157_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(lean_object* v_head_162_, lean_object* v_a_163_, lean_object* v_b_164_){
_start:
{
lean_object* v_str_165_; lean_object* v_startInclusive_166_; lean_object* v_endExclusive_167_; lean_object* v___x_168_; uint8_t v_decide_169_; 
v_str_165_ = lean_ctor_get(v_head_162_, 0);
v_startInclusive_166_ = lean_ctor_get(v_head_162_, 1);
v_endExclusive_167_ = lean_ctor_get(v_head_162_, 2);
v___x_168_ = lean_nat_sub(v_endExclusive_167_, v_startInclusive_166_);
v_decide_169_ = lean_nat_dec_eq(v_a_163_, v___x_168_);
lean_dec(v___x_168_);
if (v_decide_169_ == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_170_ = lean_nat_add(v_startInclusive_166_, v_a_163_);
lean_dec(v_a_163_);
v___x_171_ = lean_string_utf8_next_fast(v_str_165_, v___x_170_);
lean_dec(v___x_170_);
v___x_172_ = lean_nat_sub(v___x_171_, v_startInclusive_166_);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_b_164_, v___x_173_);
lean_dec(v_b_164_);
v_a_163_ = v___x_172_;
v_b_164_ = v___x_174_;
goto _start;
}
else
{
lean_dec(v_a_163_);
return v_b_164_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg___boxed(lean_object* v_head_176_, lean_object* v_a_177_, lean_object* v_b_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_176_, v_a_177_, v_b_178_);
lean_dec_ref(v_head_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_ofString_x3f(lean_object* v_t_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_string_utf8_byte_size(v_t_182_);
lean_inc_ref(v_t_182_);
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v_t_182_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_184_);
v___x_186_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0);
v___x_187_ = ((lean_object*)(l_Lake_Toml_Time_ofString_x3f___closed__0));
v___x_188_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_182_, v___x_185_, v___x_184_, v___x_186_, v___x_187_);
lean_dec_ref_known(v___x_185_, 3);
v___x_189_ = lean_array_to_list(v___x_188_);
if (lean_obj_tag(v___x_189_) == 1)
{
lean_object* v_tail_190_; 
v_tail_190_ = lean_ctor_get(v___x_189_, 1);
lean_inc(v_tail_190_);
if (lean_obj_tag(v_tail_190_) == 1)
{
lean_object* v_tail_191_; 
v_tail_191_ = lean_ctor_get(v_tail_190_, 1);
if (lean_obj_tag(v_tail_191_) == 0)
{
lean_object* v_head_192_; lean_object* v_head_193_; lean_object* v___x_194_; 
v_head_192_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_head_192_);
lean_dec_ref_known(v___x_189_, 2);
v_head_193_ = lean_ctor_get(v_tail_190_, 0);
lean_inc(v_head_193_);
lean_dec_ref_known(v_tail_190_, 2);
v___x_194_ = l_String_Slice_toNat_x3f(v_head_192_);
lean_dec(v_head_192_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v___x_195_; 
lean_dec(v_head_193_);
v___x_195_ = lean_box(0);
return v___x_195_;
}
else
{
lean_object* v_val_196_; lean_object* v___x_197_; 
v_val_196_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v___x_194_, 1);
v___x_197_ = l_String_Slice_toNat_x3f(v_head_193_);
lean_dec(v_head_193_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v___x_198_; 
lean_dec(v_val_196_);
v___x_198_ = lean_box(0);
return v___x_198_;
}
else
{
lean_object* v_val_199_; lean_object* v___x_200_; 
v_val_199_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_val_199_);
lean_dec_ref_known(v___x_197_, 1);
v___x_200_ = l_Lake_Toml_Time_ofValid_x3f(v_val_196_, v_val_199_, v___x_183_);
return v___x_200_;
}
}
}
else
{
lean_object* v_tail_201_; 
lean_inc_ref(v_tail_191_);
v_tail_201_ = lean_ctor_get(v_tail_191_, 1);
if (lean_obj_tag(v_tail_201_) == 0)
{
lean_object* v_head_202_; lean_object* v_head_203_; lean_object* v_head_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_head_202_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_head_202_);
lean_dec_ref_known(v___x_189_, 2);
v_head_203_ = lean_ctor_get(v_tail_190_, 0);
lean_inc(v_head_203_);
lean_dec_ref_known(v_tail_190_, 2);
v_head_204_ = lean_ctor_get(v_tail_191_, 0);
lean_inc(v_head_204_);
lean_dec_ref_known(v_tail_191_, 2);
v___x_205_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___closed__0);
v___x_206_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_204_, v___x_205_, v___x_187_);
lean_dec(v_head_204_);
v___x_207_ = lean_array_to_list(v___x_206_);
if (lean_obj_tag(v___x_207_) == 1)
{
lean_object* v_tail_208_; 
v_tail_208_ = lean_ctor_get(v___x_207_, 1);
lean_inc(v_tail_208_);
if (lean_obj_tag(v_tail_208_) == 0)
{
lean_object* v_head_209_; lean_object* v___x_210_; 
v_head_209_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_head_209_);
lean_dec_ref_known(v___x_207_, 2);
v___x_210_ = l_String_Slice_toNat_x3f(v_head_202_);
lean_dec(v_head_202_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; 
lean_dec(v_head_209_);
lean_dec(v_head_203_);
v___x_211_ = lean_box(0);
return v___x_211_;
}
else
{
lean_object* v_val_212_; lean_object* v___x_213_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_210_, 1);
v___x_213_ = l_String_Slice_toNat_x3f(v_head_203_);
lean_dec(v_head_203_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v___x_214_; 
lean_dec(v_val_212_);
lean_dec(v_head_209_);
v___x_214_ = lean_box(0);
return v___x_214_;
}
else
{
lean_object* v_val_215_; lean_object* v___x_216_; 
v_val_215_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_val_215_);
lean_dec_ref_known(v___x_213_, 1);
v___x_216_ = l_String_Slice_toNat_x3f(v_head_209_);
lean_dec(v_head_209_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v___x_217_; 
lean_dec(v_val_215_);
lean_dec(v_val_212_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v_val_218_; lean_object* v___x_219_; 
v_val_218_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v___x_216_, 1);
v___x_219_ = l_Lake_Toml_Time_ofValid_x3f(v_val_212_, v_val_215_, v_val_218_);
return v___x_219_;
}
}
}
}
else
{
lean_object* v_tail_220_; 
v_tail_220_ = lean_ctor_get(v_tail_208_, 1);
if (lean_obj_tag(v_tail_220_) == 0)
{
lean_object* v_head_221_; lean_object* v_head_222_; lean_object* v___x_223_; 
v_head_221_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_head_221_);
lean_dec_ref_known(v___x_207_, 2);
v_head_222_ = lean_ctor_get(v_tail_208_, 0);
lean_inc(v_head_222_);
lean_dec_ref_known(v_tail_208_, 2);
v___x_223_ = l_String_Slice_toNat_x3f(v_head_202_);
lean_dec(v_head_202_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v___x_224_; 
lean_dec(v_head_222_);
lean_dec(v_head_221_);
lean_dec(v_head_203_);
v___x_224_ = lean_box(0);
return v___x_224_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; 
v_val_225_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_223_, 1);
v___x_226_ = l_String_Slice_toNat_x3f(v_head_203_);
lean_dec(v_head_203_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v___x_227_; 
lean_dec(v_val_225_);
lean_dec(v_head_222_);
lean_dec(v_head_221_);
v___x_227_ = lean_box(0);
return v___x_227_;
}
else
{
lean_object* v_val_228_; lean_object* v___x_229_; 
v_val_228_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_228_);
lean_dec_ref_known(v___x_226_, 1);
v___x_229_ = l_String_Slice_toNat_x3f(v_head_221_);
lean_dec(v_head_221_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v___x_230_; 
lean_dec(v_val_228_);
lean_dec(v_val_225_);
lean_dec(v_head_222_);
v___x_230_ = lean_box(0);
return v___x_230_;
}
else
{
lean_object* v_val_231_; lean_object* v___x_232_; 
v_val_231_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_val_231_);
lean_dec_ref_known(v___x_229_, 1);
v___x_232_ = l_Lake_Toml_Time_ofValid_x3f(v_val_225_, v_val_228_, v_val_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_dec(v_head_222_);
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_234_; 
v_val_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v___x_232_, 1);
v___x_234_ = l_String_Slice_toNat_x3f(v_head_222_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_235_; 
lean_dec(v_val_233_);
lean_dec(v_head_222_);
v___x_235_ = lean_box(0);
return v___x_235_;
}
else
{
lean_object* v_val_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_258_; 
v_val_236_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_258_ == 0)
{
v___x_238_ = v___x_234_;
v_isShared_239_ = v_isSharedCheck_258_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_val_236_);
lean_dec(v___x_234_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_258_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_hour_240_; lean_object* v_minute_241_; lean_object* v_second_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_255_; 
v_hour_240_ = lean_ctor_get(v_val_233_, 0);
v_minute_241_ = lean_ctor_get(v_val_233_, 1);
v_second_242_ = lean_ctor_get(v_val_233_, 2);
v_isSharedCheck_255_ = !lean_is_exclusive(v_val_233_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; lean_object* v_unused_257_; 
v_unused_256_ = lean_ctor_get(v_val_233_, 4);
lean_dec(v_unused_256_);
v_unused_257_ = lean_ctor_get(v_val_233_, 3);
lean_dec(v_unused_257_);
v___x_244_ = v_val_233_;
v_isShared_245_ = v_isSharedCheck_255_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_second_242_);
lean_inc(v_minute_241_);
lean_inc(v_hour_240_);
lean_dec(v_val_233_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_255_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_250_; 
v___x_246_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_222_, v___x_183_, v___x_183_);
lean_dec(v_head_222_);
v___x_247_ = lean_unsigned_to_nat(1u);
v___x_248_ = lean_nat_sub(v___x_246_, v___x_247_);
lean_dec(v___x_246_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 4, v_val_236_);
lean_ctor_set(v___x_244_, 3, v___x_248_);
v___x_250_ = v___x_244_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_hour_240_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_minute_241_);
lean_ctor_set(v_reuseFailAlloc_254_, 2, v_second_242_);
lean_ctor_set(v_reuseFailAlloc_254_, 3, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_254_, 4, v_val_236_);
v___x_250_ = v_reuseFailAlloc_254_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_250_);
v___x_252_ = v___x_238_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
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
lean_object* v___x_259_; 
lean_dec_ref_known(v_tail_208_, 2);
lean_dec_ref_known(v___x_207_, 2);
lean_dec(v_head_203_);
lean_dec(v_head_202_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
}
}
else
{
lean_object* v___x_260_; 
lean_dec(v___x_207_);
lean_dec(v_head_203_);
lean_dec(v_head_202_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
}
else
{
lean_object* v___x_261_; 
lean_dec_ref_known(v_tail_191_, 2);
lean_dec_ref_known(v_tail_190_, 2);
lean_dec_ref_known(v___x_189_, 2);
v___x_261_ = lean_box(0);
return v___x_261_;
}
}
}
else
{
lean_object* v___x_262_; 
lean_dec(v_tail_190_);
lean_dec_ref_known(v___x_189_, 2);
v___x_262_ = lean_box(0);
return v___x_262_;
}
}
else
{
lean_object* v___x_263_; 
lean_dec(v___x_189_);
v___x_263_ = lean_box(0);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(lean_object* v_t_264_, lean_object* v___x_265_, lean_object* v___x_266_, lean_object* v_inst_267_, lean_object* v_R_268_, lean_object* v_a_269_, lean_object* v_b_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_264_, v___x_265_, v___x_266_, v_a_269_, v_b_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___boxed(lean_object* v_t_272_, lean_object* v___x_273_, lean_object* v___x_274_, lean_object* v_inst_275_, lean_object* v_R_276_, lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(v_t_272_, v___x_273_, v___x_274_, v_inst_275_, v_R_276_, v_a_277_, v_b_278_);
lean_dec_ref(v___x_273_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(lean_object* v_head_280_, lean_object* v_inst_281_, lean_object* v_R_282_, lean_object* v_a_283_, lean_object* v_b_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_280_, v_a_283_, v_b_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___boxed(lean_object* v_head_286_, lean_object* v_inst_287_, lean_object* v_R_288_, lean_object* v_a_289_, lean_object* v_b_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(v_head_286_, v_inst_287_, v_R_288_, v_a_289_, v_b_290_);
lean_dec_ref(v_head_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(lean_object* v_head_292_, lean_object* v_inst_293_, lean_object* v_R_294_, lean_object* v_a_295_, lean_object* v_b_296_, lean_object* v_c_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_292_, v_a_295_, v_b_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___boxed(lean_object* v_head_299_, lean_object* v_inst_300_, lean_object* v_R_301_, lean_object* v_a_302_, lean_object* v_b_303_, lean_object* v_c_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(v_head_299_, v_inst_300_, v_R_301_, v_a_302_, v_b_303_, v_c_304_);
lean_dec_ref(v_head_299_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Time_toString(lean_object* v_t_308_){
_start:
{
lean_object* v_hour_309_; lean_object* v_minute_310_; lean_object* v_second_311_; lean_object* v_fracExponent_312_; lean_object* v_fracMantissa_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_s_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_hour_309_ = lean_ctor_get(v_t_308_, 0);
lean_inc(v_hour_309_);
v_minute_310_ = lean_ctor_get(v_t_308_, 1);
lean_inc(v_minute_310_);
v_second_311_ = lean_ctor_get(v_t_308_, 2);
lean_inc(v_second_311_);
v_fracExponent_312_ = lean_ctor_get(v_t_308_, 3);
lean_inc(v_fracExponent_312_);
v_fracMantissa_313_ = lean_ctor_get(v_t_308_, 4);
lean_inc(v_fracMantissa_313_);
lean_dec_ref(v_t_308_);
v___x_314_ = lean_unsigned_to_nat(2u);
v___x_315_ = l_Lake_zpad(v_hour_309_, v___x_314_);
v___x_316_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_317_ = lean_string_append(v___x_315_, v___x_316_);
v___x_318_ = l_Lake_zpad(v_minute_310_, v___x_314_);
v___x_319_ = lean_string_append(v___x_317_, v___x_318_);
lean_dec_ref(v___x_318_);
v___x_320_ = lean_string_append(v___x_319_, v___x_316_);
v___x_321_ = l_Lake_zpad(v_second_311_, v___x_314_);
v_s_322_ = lean_string_append(v___x_320_, v___x_321_);
lean_dec_ref(v___x_321_);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_nat_dec_eq(v_fracMantissa_313_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint32_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_325_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__1));
v___x_326_ = lean_string_append(v_s_322_, v___x_325_);
v___x_327_ = l_Lake_zpad(v_fracMantissa_313_, v_fracExponent_312_);
lean_dec(v_fracExponent_312_);
v___x_328_ = 48;
v___x_329_ = lean_unsigned_to_nat(3u);
v___x_330_ = l_Lake_rpadAscii(v___x_327_, v___x_328_, v___x_329_);
v___x_331_ = lean_string_append(v___x_326_, v___x_330_);
lean_dec_ref(v___x_330_);
return v___x_331_;
}
else
{
lean_dec(v_fracMantissa_313_);
lean_dec(v_fracExponent_312_);
return v_s_322_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx(lean_object* v_x_334_){
_start:
{
switch(lean_obj_tag(v_x_334_))
{
case 0:
{
lean_object* v___x_335_; 
v___x_335_ = lean_unsigned_to_nat(0u);
return v___x_335_;
}
case 1:
{
lean_object* v___x_336_; 
v___x_336_ = lean_unsigned_to_nat(1u);
return v___x_336_;
}
case 2:
{
lean_object* v___x_337_; 
v___x_337_ = lean_unsigned_to_nat(2u);
return v___x_337_;
}
default: 
{
lean_object* v___x_338_; 
v___x_338_ = lean_unsigned_to_nat(3u);
return v___x_338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorIdx___boxed(lean_object* v_x_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lake_Toml_DateTime_ctorIdx(v_x_339_);
lean_dec_ref(v_x_339_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___redArg(lean_object* v_t_341_, lean_object* v_k_342_){
_start:
{
switch(lean_obj_tag(v_t_341_))
{
case 0:
{
lean_object* v_date_343_; lean_object* v_time_344_; lean_object* v_offset_x3f_345_; lean_object* v___x_346_; 
v_date_343_ = lean_ctor_get(v_t_341_, 0);
lean_inc_ref(v_date_343_);
v_time_344_ = lean_ctor_get(v_t_341_, 1);
lean_inc_ref(v_time_344_);
v_offset_x3f_345_ = lean_ctor_get(v_t_341_, 2);
lean_inc(v_offset_x3f_345_);
lean_dec_ref_known(v_t_341_, 3);
v___x_346_ = lean_apply_3(v_k_342_, v_date_343_, v_time_344_, v_offset_x3f_345_);
return v___x_346_;
}
case 1:
{
lean_object* v_date_347_; lean_object* v_time_348_; lean_object* v___x_349_; 
v_date_347_ = lean_ctor_get(v_t_341_, 0);
lean_inc_ref(v_date_347_);
v_time_348_ = lean_ctor_get(v_t_341_, 1);
lean_inc_ref(v_time_348_);
lean_dec_ref_known(v_t_341_, 2);
v___x_349_ = lean_apply_2(v_k_342_, v_date_347_, v_time_348_);
return v___x_349_;
}
default: 
{
lean_object* v_date_350_; lean_object* v___x_351_; 
v_date_350_ = lean_ctor_get(v_t_341_, 0);
lean_inc_ref(v_date_350_);
lean_dec_ref(v_t_341_);
v___x_351_ = lean_apply_1(v_k_342_, v_date_350_);
return v___x_351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim(lean_object* v_motive_352_, lean_object* v_ctorIdx_353_, lean_object* v_t_354_, lean_object* v_h_355_, lean_object* v_k_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_354_, v_k_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ctorElim___boxed(lean_object* v_motive_358_, lean_object* v_ctorIdx_359_, lean_object* v_t_360_, lean_object* v_h_361_, lean_object* v_k_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lake_Toml_DateTime_ctorElim(v_motive_358_, v_ctorIdx_359_, v_t_360_, v_h_361_, v_k_362_);
lean_dec(v_ctorIdx_359_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim___redArg(lean_object* v_t_364_, lean_object* v_offsetDateTime_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_364_, v_offsetDateTime_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_offsetDateTime_elim(lean_object* v_motive_367_, lean_object* v_t_368_, lean_object* v_h_369_, lean_object* v_offsetDateTime_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_368_, v_offsetDateTime_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim___redArg(lean_object* v_t_372_, lean_object* v_localDateTime_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_372_, v_localDateTime_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDateTime_elim(lean_object* v_motive_375_, lean_object* v_t_376_, lean_object* v_h_377_, lean_object* v_localDateTime_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_376_, v_localDateTime_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim___redArg(lean_object* v_t_380_, lean_object* v_localDate_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_380_, v_localDate_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localDate_elim(lean_object* v_motive_383_, lean_object* v_t_384_, lean_object* v_h_385_, lean_object* v_localDate_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_384_, v_localDate_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim___redArg(lean_object* v_t_388_, lean_object* v_localTime_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_388_, v_localTime_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_localTime_elim(lean_object* v_motive_391_, lean_object* v_t_392_, lean_object* v_h_393_, lean_object* v_localTime_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_392_, v_localTime_394_);
return v___x_395_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_396_ = lean_box(0);
v___x_397_ = ((lean_object*)(l_Lake_Toml_instInhabitedTime_default));
v___x_398_ = l_Lake_instInhabitedDate_default;
v___x_399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v___x_397_);
lean_ctor_set(v___x_399_, 2, v___x_396_);
return v___x_399_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime_default(void){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_obj_once(&l_Lake_Toml_instInhabitedDateTime_default___closed__0, &l_Lake_Toml_instInhabitedDateTime_default___closed__0_once, _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0);
return v___x_400_;
}
}
static lean_object* _init_l_Lake_Toml_instInhabitedDateTime(void){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lake_Toml_instInhabitedDateTime_default;
return v___x_401_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(uint8_t v___x_402_, uint8_t v___y_403_, uint8_t v___y_404_){
_start:
{
if (v___y_404_ == 0)
{
if (v___y_403_ == 0)
{
return v___x_402_;
}
else
{
return v___y_404_;
}
}
else
{
return v___y_403_;
}
}
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
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(lean_object* v___f_413_, lean_object* v_a_414_, lean_object* v_b_415_){
_start:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqTime___boxed), 2, 0);
v___x_417_ = l_instDecidableEqProd___redArg(v___f_413_, v___x_416_, v_a_414_, v_b_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed(lean_object* v___f_418_, lean_object* v_a_419_, lean_object* v_b_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(v___f_418_, v_a_419_, v_b_420_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime_decEq(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
switch(lean_obj_tag(v_x_423_))
{
case 0:
{
if (lean_obj_tag(v_x_424_) == 0)
{
lean_object* v_date_425_; lean_object* v_time_426_; lean_object* v_offset_x3f_427_; lean_object* v_date_428_; lean_object* v_time_429_; lean_object* v_offset_x3f_430_; uint8_t v___x_431_; 
v_date_425_ = lean_ctor_get(v_x_423_, 0);
lean_inc_ref(v_date_425_);
v_time_426_ = lean_ctor_get(v_x_423_, 1);
lean_inc_ref(v_time_426_);
v_offset_x3f_427_ = lean_ctor_get(v_x_423_, 2);
lean_inc(v_offset_x3f_427_);
lean_dec_ref_known(v_x_423_, 3);
v_date_428_ = lean_ctor_get(v_x_424_, 0);
lean_inc_ref(v_date_428_);
v_time_429_ = lean_ctor_get(v_x_424_, 1);
lean_inc_ref(v_time_429_);
v_offset_x3f_430_ = lean_ctor_get(v_x_424_, 2);
lean_inc(v_offset_x3f_430_);
lean_dec_ref_known(v_x_424_, 3);
v___x_431_ = l_Lake_instDecidableEqDate_decEq(v_date_425_, v_date_428_);
lean_dec_ref(v_date_428_);
lean_dec_ref(v_date_425_);
if (v___x_431_ == 0)
{
lean_dec(v_offset_x3f_430_);
lean_dec_ref(v_time_429_);
lean_dec(v_offset_x3f_427_);
lean_dec_ref(v_time_426_);
return v___x_431_;
}
else
{
uint8_t v___x_432_; 
v___x_432_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_426_, v_time_429_);
lean_dec_ref(v_time_429_);
lean_dec_ref(v_time_426_);
if (v___x_432_ == 0)
{
lean_dec(v_offset_x3f_430_);
lean_dec(v_offset_x3f_427_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; lean_object* v___f_434_; lean_object* v___f_435_; uint8_t v___x_436_; 
v___x_433_ = lean_box(v___x_432_);
v___f_434_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed), 3, 1);
lean_closure_set(v___f_434_, 0, v___x_433_);
v___f_435_ = lean_alloc_closure((void*)(l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed), 3, 1);
lean_closure_set(v___f_435_, 0, v___f_434_);
v___x_436_ = l_Option_instDecidableEq___redArg(v___f_435_, v_offset_x3f_427_, v_offset_x3f_430_);
return v___x_436_;
}
}
}
else
{
uint8_t v___x_437_; 
lean_dec_ref_known(v_x_423_, 3);
lean_dec_ref(v_x_424_);
v___x_437_ = 0;
return v___x_437_;
}
}
case 1:
{
if (lean_obj_tag(v_x_424_) == 1)
{
lean_object* v_date_438_; lean_object* v_time_439_; lean_object* v_date_440_; lean_object* v_time_441_; uint8_t v___x_442_; 
v_date_438_ = lean_ctor_get(v_x_423_, 0);
lean_inc_ref(v_date_438_);
v_time_439_ = lean_ctor_get(v_x_423_, 1);
lean_inc_ref(v_time_439_);
lean_dec_ref_known(v_x_423_, 2);
v_date_440_ = lean_ctor_get(v_x_424_, 0);
lean_inc_ref(v_date_440_);
v_time_441_ = lean_ctor_get(v_x_424_, 1);
lean_inc_ref(v_time_441_);
lean_dec_ref_known(v_x_424_, 2);
v___x_442_ = l_Lake_instDecidableEqDate_decEq(v_date_438_, v_date_440_);
lean_dec_ref(v_date_440_);
lean_dec_ref(v_date_438_);
if (v___x_442_ == 0)
{
lean_dec_ref(v_time_441_);
lean_dec_ref(v_time_439_);
return v___x_442_;
}
else
{
uint8_t v___x_443_; 
v___x_443_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_439_, v_time_441_);
lean_dec_ref(v_time_441_);
lean_dec_ref(v_time_439_);
return v___x_443_;
}
}
else
{
uint8_t v___x_444_; 
lean_dec_ref_known(v_x_423_, 2);
lean_dec_ref(v_x_424_);
v___x_444_ = 0;
return v___x_444_;
}
}
case 2:
{
if (lean_obj_tag(v_x_424_) == 2)
{
lean_object* v_date_445_; lean_object* v_date_446_; uint8_t v___x_447_; 
v_date_445_ = lean_ctor_get(v_x_423_, 0);
lean_inc_ref(v_date_445_);
lean_dec_ref_known(v_x_423_, 1);
v_date_446_ = lean_ctor_get(v_x_424_, 0);
lean_inc_ref(v_date_446_);
lean_dec_ref_known(v_x_424_, 1);
v___x_447_ = l_Lake_instDecidableEqDate_decEq(v_date_445_, v_date_446_);
lean_dec_ref(v_date_446_);
lean_dec_ref(v_date_445_);
return v___x_447_;
}
else
{
uint8_t v___x_448_; 
lean_dec_ref_known(v_x_423_, 1);
lean_dec_ref(v_x_424_);
v___x_448_ = 0;
return v___x_448_;
}
}
default: 
{
if (lean_obj_tag(v_x_424_) == 3)
{
lean_object* v_time_449_; lean_object* v_time_450_; uint8_t v___x_451_; 
v_time_449_ = lean_ctor_get(v_x_423_, 0);
lean_inc_ref(v_time_449_);
lean_dec_ref_known(v_x_423_, 1);
v_time_450_ = lean_ctor_get(v_x_424_, 0);
lean_inc_ref(v_time_450_);
lean_dec_ref_known(v_x_424_, 1);
v___x_451_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_449_, v_time_450_);
lean_dec_ref(v_time_450_);
lean_dec_ref(v_time_449_);
return v___x_451_;
}
else
{
uint8_t v___x_452_; 
lean_dec_ref_known(v_x_423_, 1);
lean_dec_ref(v_x_424_);
v___x_452_ = 0;
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime_decEq___boxed(lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_453_, v_x_454_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_instDecidableEqDateTime(lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_457_, v_x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instDecidableEqDateTime___boxed(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Lake_Toml_instDecidableEqDateTime(v_x_460_, v_x_461_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeDateDateTime___lam__0(lean_object* v_date_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_465_, 0, v_date_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_instCoeTimeDateTime___lam__0(lean_object* v_time_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_469_, 0, v_time_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg___closed__0));
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg___boxed(lean_object* v___dummy_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg();
return v_res_477_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___redArg();
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(lean_object* v_s_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___boxed(lean_object* v_s_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(v_s_481_);
lean_dec_ref(v_s_481_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg(){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg___boxed(lean_object* v___dummy_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg();
return v_res_486_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0(void){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___redArg();
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(lean_object* v_s_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___boxed(lean_object* v_s_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(v_s_490_);
lean_dec_ref(v_s_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg(){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___redArg___closed__0));
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg___boxed(lean_object* v___dummy_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg();
return v_res_495_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___redArg();
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(lean_object* v_s_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___boxed(lean_object* v_s_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(v_s_499_);
lean_dec_ref(v_s_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(lean_object* v_head_501_, lean_object* v_a_502_, lean_object* v_b_503_){
_start:
{
if (lean_obj_tag(v_a_502_) == 0)
{
lean_object* v_currPos_504_; lean_object* v_searcher_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_544_; 
v_currPos_504_ = lean_ctor_get(v_a_502_, 0);
v_searcher_505_ = lean_ctor_get(v_a_502_, 1);
v_isSharedCheck_544_ = !lean_is_exclusive(v_a_502_);
if (v_isSharedCheck_544_ == 0)
{
v___x_507_ = v_a_502_;
v_isShared_508_ = v_isSharedCheck_544_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_searcher_505_);
lean_inc(v_currPos_504_);
lean_dec(v_a_502_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_544_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_str_509_; lean_object* v_startInclusive_510_; lean_object* v_endExclusive_511_; lean_object* v_it_513_; lean_object* v_startInclusive_514_; lean_object* v_endExclusive_515_; lean_object* v___x_522_; uint8_t v_decide_523_; 
v_str_509_ = lean_ctor_get(v_head_501_, 0);
v_startInclusive_510_ = lean_ctor_get(v_head_501_, 1);
v_endExclusive_511_ = lean_ctor_get(v_head_501_, 2);
v___x_522_ = lean_nat_sub(v_endExclusive_511_, v_startInclusive_510_);
v_decide_523_ = lean_nat_dec_eq(v_searcher_505_, v___x_522_);
if (v_decide_523_ == 0)
{
uint32_t v___x_524_; lean_object* v___x_525_; uint32_t v___x_526_; uint8_t v___x_527_; 
lean_dec(v___x_522_);
v___x_524_ = 43;
v___x_525_ = lean_nat_add(v_startInclusive_510_, v_searcher_505_);
v___x_526_ = lean_string_utf8_get_fast(v_str_509_, v___x_525_);
v___x_527_ = lean_uint32_dec_eq(v___x_526_, v___x_524_);
if (v___x_527_ == 0)
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
lean_dec(v_searcher_505_);
v___x_528_ = lean_string_utf8_next_fast(v_str_509_, v___x_525_);
lean_dec(v___x_525_);
v___x_529_ = lean_nat_sub(v___x_528_, v_startInclusive_510_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_529_);
v___x_531_ = v___x_507_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_currPos_504_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_533_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
v_a_502_ = v___x_531_;
goto _start;
}
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_slice_537_; lean_object* v_nextIt_539_; 
v___x_534_ = lean_string_utf8_next_fast(v_str_509_, v___x_525_);
v___x_535_ = lean_nat_sub(v___x_534_, v___x_525_);
lean_dec(v___x_525_);
v___x_536_ = lean_nat_add(v_searcher_505_, v___x_535_);
lean_dec(v___x_535_);
v_slice_537_ = l_String_Slice_subslice_x21(v_head_501_, v_currPos_504_, v_searcher_505_);
lean_inc(v___x_536_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v___x_536_);
lean_ctor_set(v___x_507_, 0, v___x_536_);
v_nextIt_539_ = v___x_507_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_536_);
v_nextIt_539_ = v_reuseFailAlloc_542_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v_startInclusive_540_; lean_object* v_endExclusive_541_; 
v_startInclusive_540_ = lean_ctor_get(v_slice_537_, 0);
lean_inc(v_startInclusive_540_);
v_endExclusive_541_ = lean_ctor_get(v_slice_537_, 1);
lean_inc(v_endExclusive_541_);
lean_dec_ref(v_slice_537_);
v_it_513_ = v_nextIt_539_;
v_startInclusive_514_ = v_startInclusive_540_;
v_endExclusive_515_ = v_endExclusive_541_;
goto v___jp_512_;
}
}
}
else
{
lean_object* v___x_543_; 
lean_del_object(v___x_507_);
lean_dec(v_searcher_505_);
v___x_543_ = lean_box(1);
v_it_513_ = v___x_543_;
v_startInclusive_514_ = v_currPos_504_;
v_endExclusive_515_ = v___x_522_;
goto v___jp_512_;
}
v___jp_512_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_516_ = lean_nat_add(v_startInclusive_510_, v_startInclusive_514_);
lean_dec(v_startInclusive_514_);
v___x_517_ = lean_nat_add(v_startInclusive_510_, v_endExclusive_515_);
lean_dec(v_endExclusive_515_);
lean_inc_ref(v_str_509_);
v___x_518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_518_, 0, v_str_509_);
lean_ctor_set(v___x_518_, 1, v___x_516_);
lean_ctor_set(v___x_518_, 2, v___x_517_);
v___x_519_ = l_String_Slice_toString(v___x_518_);
lean_dec_ref_known(v___x_518_, 3);
v___x_520_ = lean_array_push(v_b_503_, v___x_519_);
v_a_502_ = v_it_513_;
v_b_503_ = v___x_520_;
goto _start;
}
}
}
else
{
return v_b_503_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg___boxed(lean_object* v_head_545_, lean_object* v_a_546_, lean_object* v_b_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_545_, v_a_546_, v_b_547_);
lean_dec_ref(v_head_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(lean_object* v_dt_549_, lean_object* v___x_550_, lean_object* v___x_551_, lean_object* v_a_552_, lean_object* v_b_553_){
_start:
{
lean_object* v_it_555_; lean_object* v_startInclusive_556_; lean_object* v_endExclusive_557_; 
if (lean_obj_tag(v_a_552_) == 0)
{
lean_object* v_currPos_561_; lean_object* v_searcher_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_591_; 
v_currPos_561_ = lean_ctor_get(v_a_552_, 0);
v_searcher_562_ = lean_ctor_get(v_a_552_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_a_552_);
if (v_isSharedCheck_591_ == 0)
{
v___x_564_ = v_a_552_;
v_isShared_565_ = v_isSharedCheck_591_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_searcher_562_);
lean_inc(v_currPos_561_);
lean_dec(v_a_552_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_591_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
uint8_t v___y_567_; uint8_t v_decide_582_; 
v_decide_582_ = lean_nat_dec_eq(v_searcher_562_, v___x_551_);
if (v_decide_582_ == 0)
{
uint32_t v___x_583_; uint32_t v___x_584_; uint8_t v___x_585_; 
v___x_583_ = lean_string_utf8_get_fast(v_dt_549_, v_searcher_562_);
v___x_584_ = 84;
v___x_585_ = lean_uint32_dec_eq(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
uint32_t v___x_586_; uint8_t v___x_587_; 
v___x_586_ = 116;
v___x_587_ = lean_uint32_dec_eq(v___x_583_, v___x_586_);
if (v___x_587_ == 0)
{
uint32_t v___x_588_; uint8_t v___x_589_; 
v___x_588_ = 32;
v___x_589_ = lean_uint32_dec_eq(v___x_583_, v___x_588_);
v___y_567_ = v___x_589_;
goto v___jp_566_;
}
else
{
v___y_567_ = v___x_587_;
goto v___jp_566_;
}
}
else
{
v___y_567_ = v___x_585_;
goto v___jp_566_;
}
}
else
{
lean_object* v___x_590_; 
lean_del_object(v___x_564_);
lean_dec(v_searcher_562_);
v___x_590_ = lean_box(1);
lean_inc(v___x_551_);
v_it_555_ = v___x_590_;
v_startInclusive_556_ = v_currPos_561_;
v_endExclusive_557_ = v___x_551_;
goto v___jp_554_;
}
v___jp_566_:
{
if (v___y_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_568_ = lean_string_utf8_next_fast(v_dt_549_, v_searcher_562_);
lean_dec(v_searcher_562_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v___x_568_);
v___x_570_ = v___x_564_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_currPos_561_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_568_);
v___x_570_ = v_reuseFailAlloc_572_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
v_a_552_ = v___x_570_;
goto _start;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_slice_576_; lean_object* v_nextIt_578_; 
v___x_573_ = lean_string_utf8_next_fast(v_dt_549_, v_searcher_562_);
v___x_574_ = lean_nat_sub(v___x_573_, v_searcher_562_);
v___x_575_ = lean_nat_add(v_searcher_562_, v___x_574_);
lean_dec(v___x_574_);
v_slice_576_ = l_String_Slice_subslice_x21(v___x_550_, v_currPos_561_, v_searcher_562_);
lean_inc(v___x_575_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v___x_575_);
lean_ctor_set(v___x_564_, 0, v___x_575_);
v_nextIt_578_ = v___x_564_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_575_);
v_nextIt_578_ = v_reuseFailAlloc_581_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v_startInclusive_579_; lean_object* v_endExclusive_580_; 
v_startInclusive_579_ = lean_ctor_get(v_slice_576_, 0);
lean_inc(v_startInclusive_579_);
v_endExclusive_580_ = lean_ctor_get(v_slice_576_, 1);
lean_inc(v_endExclusive_580_);
lean_dec_ref(v_slice_576_);
v_it_555_ = v_nextIt_578_;
v_startInclusive_556_ = v_startInclusive_579_;
v_endExclusive_557_ = v_endExclusive_580_;
goto v___jp_554_;
}
}
}
}
}
else
{
lean_dec(v___x_551_);
lean_dec_ref(v_dt_549_);
return v_b_553_;
}
v___jp_554_:
{
lean_object* v___x_558_; lean_object* v___x_559_; 
lean_inc_ref(v_dt_549_);
v___x_558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_558_, 0, v_dt_549_);
lean_ctor_set(v___x_558_, 1, v_startInclusive_556_);
lean_ctor_set(v___x_558_, 2, v_endExclusive_557_);
v___x_559_ = lean_array_push(v_b_553_, v___x_558_);
v_a_552_ = v_it_555_;
v_b_553_ = v___x_559_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg___boxed(lean_object* v_dt_592_, lean_object* v___x_593_, lean_object* v___x_594_, lean_object* v_a_595_, lean_object* v_b_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_592_, v___x_593_, v___x_594_, v_a_595_, v_b_596_);
lean_dec_ref(v___x_593_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(lean_object* v_head_598_, lean_object* v_a_599_, lean_object* v_b_600_){
_start:
{
if (lean_obj_tag(v_a_599_) == 0)
{
lean_object* v_currPos_601_; lean_object* v_searcher_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_641_; 
v_currPos_601_ = lean_ctor_get(v_a_599_, 0);
v_searcher_602_ = lean_ctor_get(v_a_599_, 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_a_599_);
if (v_isSharedCheck_641_ == 0)
{
v___x_604_ = v_a_599_;
v_isShared_605_ = v_isSharedCheck_641_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_searcher_602_);
lean_inc(v_currPos_601_);
lean_dec(v_a_599_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_641_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_str_606_; lean_object* v_startInclusive_607_; lean_object* v_endExclusive_608_; lean_object* v_it_610_; lean_object* v_startInclusive_611_; lean_object* v_endExclusive_612_; lean_object* v___x_619_; uint8_t v_decide_620_; 
v_str_606_ = lean_ctor_get(v_head_598_, 0);
v_startInclusive_607_ = lean_ctor_get(v_head_598_, 1);
v_endExclusive_608_ = lean_ctor_get(v_head_598_, 2);
v___x_619_ = lean_nat_sub(v_endExclusive_608_, v_startInclusive_607_);
v_decide_620_ = lean_nat_dec_eq(v_searcher_602_, v___x_619_);
if (v_decide_620_ == 0)
{
uint32_t v___x_621_; lean_object* v___x_622_; uint32_t v___x_623_; uint8_t v___x_624_; 
lean_dec(v___x_619_);
v___x_621_ = 45;
v___x_622_ = lean_nat_add(v_startInclusive_607_, v_searcher_602_);
v___x_623_ = lean_string_utf8_get_fast(v_str_606_, v___x_622_);
v___x_624_ = lean_uint32_dec_eq(v___x_623_, v___x_621_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
lean_dec(v_searcher_602_);
v___x_625_ = lean_string_utf8_next_fast(v_str_606_, v___x_622_);
lean_dec(v___x_622_);
v___x_626_ = lean_nat_sub(v___x_625_, v_startInclusive_607_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___x_626_);
v___x_628_ = v___x_604_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_currPos_601_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_626_);
v___x_628_ = v_reuseFailAlloc_630_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v_a_599_ = v___x_628_;
goto _start;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_slice_634_; lean_object* v_nextIt_636_; 
v___x_631_ = lean_string_utf8_next_fast(v_str_606_, v___x_622_);
v___x_632_ = lean_nat_sub(v___x_631_, v___x_622_);
lean_dec(v___x_622_);
v___x_633_ = lean_nat_add(v_searcher_602_, v___x_632_);
lean_dec(v___x_632_);
v_slice_634_ = l_String_Slice_subslice_x21(v_head_598_, v_currPos_601_, v_searcher_602_);
lean_inc(v___x_633_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___x_633_);
lean_ctor_set(v___x_604_, 0, v___x_633_);
v_nextIt_636_ = v___x_604_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_633_);
v_nextIt_636_ = v_reuseFailAlloc_639_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v_startInclusive_637_; lean_object* v_endExclusive_638_; 
v_startInclusive_637_ = lean_ctor_get(v_slice_634_, 0);
lean_inc(v_startInclusive_637_);
v_endExclusive_638_ = lean_ctor_get(v_slice_634_, 1);
lean_inc(v_endExclusive_638_);
lean_dec_ref(v_slice_634_);
v_it_610_ = v_nextIt_636_;
v_startInclusive_611_ = v_startInclusive_637_;
v_endExclusive_612_ = v_endExclusive_638_;
goto v___jp_609_;
}
}
}
else
{
lean_object* v___x_640_; 
lean_del_object(v___x_604_);
lean_dec(v_searcher_602_);
v___x_640_ = lean_box(1);
v_it_610_ = v___x_640_;
v_startInclusive_611_ = v_currPos_601_;
v_endExclusive_612_ = v___x_619_;
goto v___jp_609_;
}
v___jp_609_:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_613_ = lean_nat_add(v_startInclusive_607_, v_startInclusive_611_);
lean_dec(v_startInclusive_611_);
v___x_614_ = lean_nat_add(v_startInclusive_607_, v_endExclusive_612_);
lean_dec(v_endExclusive_612_);
lean_inc_ref(v_str_606_);
v___x_615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_615_, 0, v_str_606_);
lean_ctor_set(v___x_615_, 1, v___x_613_);
lean_ctor_set(v___x_615_, 2, v___x_614_);
v___x_616_ = l_String_Slice_toString(v___x_615_);
lean_dec_ref_known(v___x_615_, 3);
v___x_617_ = lean_array_push(v_b_600_, v___x_616_);
v_a_599_ = v_it_610_;
v_b_600_ = v___x_617_;
goto _start;
}
}
}
else
{
return v_b_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg___boxed(lean_object* v_head_642_, lean_object* v_a_643_, lean_object* v_b_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_642_, v_a_643_, v_b_644_);
lean_dec_ref(v_head_642_);
return v_res_645_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(lean_object* v_s_646_, lean_object* v_a_647_, uint8_t v_b_648_){
_start:
{
lean_object* v_str_649_; lean_object* v_startInclusive_650_; lean_object* v_endExclusive_651_; lean_object* v___x_652_; uint8_t v_decide_653_; 
v_str_649_ = lean_ctor_get(v_s_646_, 0);
v_startInclusive_650_ = lean_ctor_get(v_s_646_, 1);
v_endExclusive_651_ = lean_ctor_get(v_s_646_, 2);
v___x_652_ = lean_nat_sub(v_endExclusive_651_, v_startInclusive_650_);
v_decide_653_ = lean_nat_dec_eq(v_a_647_, v___x_652_);
lean_dec(v___x_652_);
if (v_decide_653_ == 0)
{
lean_object* v___x_654_; uint32_t v___x_655_; uint32_t v___x_656_; uint8_t v___x_657_; 
v___x_654_ = lean_nat_add(v_startInclusive_650_, v_a_647_);
lean_dec(v_a_647_);
v___x_655_ = lean_string_utf8_get_fast(v_str_649_, v___x_654_);
v___x_656_ = 58;
v___x_657_ = lean_uint32_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_string_utf8_next_fast(v_str_649_, v___x_654_);
lean_dec(v___x_654_);
v___x_659_ = lean_nat_sub(v___x_658_, v_startInclusive_650_);
v_a_647_ = v___x_659_;
v_b_648_ = v___x_657_;
goto _start;
}
else
{
lean_dec(v___x_654_);
return v___x_657_;
}
}
else
{
lean_dec(v_a_647_);
return v_b_648_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg___boxed(lean_object* v_s_661_, lean_object* v_a_662_, lean_object* v_b_663_){
_start:
{
uint8_t v_b_boxed_664_; uint8_t v_res_665_; lean_object* v_r_666_; 
v_b_boxed_664_ = lean_unbox(v_b_663_);
v_res_665_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_661_, v_a_662_, v_b_boxed_664_);
lean_dec_ref(v_s_661_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(lean_object* v_s_667_){
_start:
{
lean_object* v_searcher_668_; uint8_t v___x_669_; uint8_t v___x_670_; 
v_searcher_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = 0;
v___x_670_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_667_, v_searcher_668_, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2___boxed(lean_object* v_s_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_s_671_);
lean_dec_ref(v_s_671_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_ofString_x3f(lean_object* v_dt_674_){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_string_utf8_byte_size(v_dt_674_);
lean_inc_ref(v_dt_674_);
v___x_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_677_, 0, v_dt_674_);
lean_ctor_set(v___x_677_, 1, v___x_675_);
lean_ctor_set(v___x_677_, 2, v___x_676_);
v___x_678_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0);
v___x_679_ = ((lean_object*)(l_Lake_Toml_Time_ofString_x3f___closed__0));
v___x_680_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_674_, v___x_677_, v___x_676_, v___x_678_, v___x_679_);
lean_dec_ref_known(v___x_677_, 3);
v___x_681_ = lean_array_to_list(v___x_680_);
if (lean_obj_tag(v___x_681_) == 1)
{
lean_object* v_tail_682_; 
v_tail_682_ = lean_ctor_get(v___x_681_, 1);
lean_inc(v_tail_682_);
if (lean_obj_tag(v_tail_682_) == 0)
{
lean_object* v_head_683_; uint8_t v___x_684_; 
v_head_683_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_head_683_);
lean_dec_ref_known(v___x_681_, 2);
v___x_684_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_head_683_);
if (v___x_684_ == 0)
{
lean_object* v_str_685_; lean_object* v_startInclusive_686_; lean_object* v_endExclusive_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_str_685_ = lean_ctor_get(v_head_683_, 0);
lean_inc_ref(v_str_685_);
v_startInclusive_686_ = lean_ctor_get(v_head_683_, 1);
lean_inc(v_startInclusive_686_);
v_endExclusive_687_ = lean_ctor_get(v_head_683_, 2);
lean_inc(v_endExclusive_687_);
lean_dec(v_head_683_);
v___x_688_ = lean_string_utf8_extract_fast(v_str_685_, v_startInclusive_686_, v_endExclusive_687_);
lean_dec(v_endExclusive_687_);
lean_dec(v_startInclusive_686_);
lean_dec_ref(v_str_685_);
v___x_689_ = l_Lake_Date_ofString_x3f(v___x_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v___x_690_; 
v___x_690_ = lean_box(0);
return v___x_690_;
}
else
{
lean_object* v_val_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_699_; 
v_val_691_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_699_ == 0)
{
v___x_693_ = v___x_689_;
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_val_691_);
lean_dec(v___x_689_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_695_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_695_, 0, v_val_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v_str_700_; lean_object* v_startInclusive_701_; lean_object* v_endExclusive_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_str_700_ = lean_ctor_get(v_head_683_, 0);
lean_inc_ref(v_str_700_);
v_startInclusive_701_ = lean_ctor_get(v_head_683_, 1);
lean_inc(v_startInclusive_701_);
v_endExclusive_702_ = lean_ctor_get(v_head_683_, 2);
lean_inc(v_endExclusive_702_);
lean_dec(v_head_683_);
v___x_703_ = lean_string_utf8_extract_fast(v_str_700_, v_startInclusive_701_, v_endExclusive_702_);
lean_dec(v_endExclusive_702_);
lean_dec(v_startInclusive_701_);
lean_dec_ref(v_str_700_);
v___x_704_ = l_Lake_Toml_Time_ofString_x3f(v___x_703_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v___x_705_; 
v___x_705_ = lean_box(0);
return v___x_705_;
}
else
{
lean_object* v_val_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_714_; 
v_val_706_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_714_ == 0)
{
v___x_708_ = v___x_704_;
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_val_706_);
lean_dec(v___x_704_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_714_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_712_; 
v___x_710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_710_, 0, v_val_706_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_710_);
v___x_712_ = v___x_708_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
else
{
lean_object* v_tail_715_; 
v_tail_715_ = lean_ctor_get(v_tail_682_, 1);
if (lean_obj_tag(v_tail_715_) == 0)
{
lean_object* v_head_716_; lean_object* v_head_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_892_; 
v_head_716_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_head_716_);
lean_dec_ref_known(v___x_681_, 2);
v_head_717_ = lean_ctor_get(v_tail_682_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v_tail_682_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_tail_682_, 1);
lean_dec(v_unused_893_);
v___x_719_ = v_tail_682_;
v_isShared_720_ = v_isSharedCheck_892_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_head_717_);
lean_dec(v_tail_682_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_892_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_str_721_; lean_object* v_startInclusive_722_; lean_object* v_endExclusive_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_str_721_ = lean_ctor_get(v_head_716_, 0);
lean_inc_ref(v_str_721_);
v_startInclusive_722_ = lean_ctor_get(v_head_716_, 1);
lean_inc(v_startInclusive_722_);
v_endExclusive_723_ = lean_ctor_get(v_head_716_, 2);
lean_inc(v_endExclusive_723_);
lean_dec(v_head_716_);
v___x_724_ = lean_string_utf8_extract_fast(v_str_721_, v_startInclusive_722_, v_endExclusive_723_);
lean_dec(v_endExclusive_723_);
lean_dec(v_startInclusive_722_);
lean_dec_ref(v_str_721_);
v___x_725_ = l_Lake_Date_ofString_x3f(v___x_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_726_; 
lean_del_object(v___x_719_);
lean_dec(v_head_717_);
v___x_726_ = lean_box(0);
return v___x_726_;
}
else
{
lean_object* v_val_727_; lean_object* v_str_728_; lean_object* v_startInclusive_729_; lean_object* v_endExclusive_730_; uint8_t v___y_747_; uint32_t v___y_822_; uint32_t v___y_873_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_val_727_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_727_);
lean_dec_ref_known(v___x_725_, 1);
v_str_728_ = lean_ctor_get(v_head_717_, 0);
v_startInclusive_729_ = lean_ctor_get(v_head_717_, 1);
v_endExclusive_730_ = lean_ctor_get(v_head_717_, 2);
v___x_884_ = lean_nat_sub(v_endExclusive_730_, v_startInclusive_729_);
v___x_885_ = l_String_Slice_Pos_prev_x3f(v_head_717_, v___x_884_);
lean_dec(v___x_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
uint32_t v___x_886_; 
v___x_886_ = 65;
v___y_873_ = v___x_886_;
goto v___jp_872_;
}
else
{
lean_object* v_val_887_; lean_object* v___x_888_; 
v_val_887_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_val_887_);
lean_dec_ref_known(v___x_885_, 1);
v___x_888_ = l_String_Slice_Pos_get_x3f(v_head_717_, v_val_887_);
lean_dec(v_val_887_);
if (lean_obj_tag(v___x_888_) == 0)
{
uint32_t v___x_889_; 
v___x_889_ = 65;
v___y_873_ = v___x_889_;
goto v___jp_872_;
}
else
{
lean_object* v_val_890_; uint32_t v___x_891_; 
v_val_890_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_val_890_);
lean_dec_ref_known(v___x_888_, 1);
v___x_891_ = lean_unbox_uint32(v_val_890_);
lean_dec(v_val_890_);
v___y_873_ = v___x_891_;
goto v___jp_872_;
}
}
v___jp_731_:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_string_utf8_extract_fast(v_str_728_, v_startInclusive_729_, v_endExclusive_730_);
lean_dec(v_endExclusive_730_);
lean_dec(v_startInclusive_729_);
lean_dec_ref(v_str_728_);
v___x_733_ = l_Lake_Toml_Time_ofString_x3f(v___x_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; 
lean_dec(v_val_727_);
lean_del_object(v___x_719_);
v___x_734_ = lean_box(0);
return v___x_734_;
}
else
{
lean_object* v_val_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_745_; 
v_val_735_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_745_ == 0)
{
v___x_737_ = v___x_733_;
v_isShared_738_ = v_isSharedCheck_745_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_val_735_);
lean_dec(v___x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_745_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v_val_735_);
lean_ctor_set(v___x_719_, 0, v_val_727_);
v___x_740_ = v___x_719_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_val_727_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_val_735_);
v___x_740_ = v_reuseFailAlloc_744_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_742_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_740_);
v___x_742_ = v___x_737_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_790_; 
v___x_748_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___closed__0);
v___x_749_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_717_, v___x_748_, v___x_679_);
v_isSharedCheck_790_ = !lean_is_exclusive(v_head_717_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; lean_object* v_unused_792_; lean_object* v_unused_793_; 
v_unused_791_ = lean_ctor_get(v_head_717_, 2);
lean_dec(v_unused_791_);
v_unused_792_ = lean_ctor_get(v_head_717_, 1);
lean_dec(v_unused_792_);
v_unused_793_ = lean_ctor_get(v_head_717_, 0);
lean_dec(v_unused_793_);
v___x_751_ = v_head_717_;
v_isShared_752_ = v_isSharedCheck_790_;
goto v_resetjp_750_;
}
else
{
lean_dec(v_head_717_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_790_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_array_to_list(v___x_749_);
if (lean_obj_tag(v___x_753_) == 1)
{
lean_object* v_tail_754_; 
v_tail_754_ = lean_ctor_get(v___x_753_, 1);
lean_inc(v_tail_754_);
if (lean_obj_tag(v_tail_754_) == 1)
{
lean_object* v_tail_755_; 
v_tail_755_ = lean_ctor_get(v_tail_754_, 1);
if (lean_obj_tag(v_tail_755_) == 0)
{
lean_object* v_head_756_; lean_object* v_head_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_788_; 
lean_dec(v_endExclusive_730_);
lean_dec(v_startInclusive_729_);
lean_dec_ref(v_str_728_);
lean_del_object(v___x_719_);
v_head_756_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_head_756_);
lean_dec_ref_known(v___x_753_, 2);
v_head_757_ = lean_ctor_get(v_tail_754_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_tail_754_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v_tail_754_, 1);
lean_dec(v_unused_789_);
v___x_759_ = v_tail_754_;
v_isShared_760_ = v_isSharedCheck_788_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_head_757_);
lean_dec(v_tail_754_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_788_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lake_Toml_Time_ofString_x3f(v_head_756_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v___x_762_; 
lean_del_object(v___x_759_);
lean_dec(v_head_757_);
lean_del_object(v___x_751_);
lean_dec(v_val_727_);
v___x_762_ = lean_box(0);
return v___x_762_;
}
else
{
lean_object* v_val_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_787_; 
v_val_763_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_787_ == 0)
{
v___x_765_ = v___x_761_;
v_isShared_766_ = v_isSharedCheck_787_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_val_763_);
lean_dec(v___x_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_787_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lake_Toml_Time_ofString_x3f(v_head_757_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v___x_768_; 
lean_del_object(v___x_765_);
lean_dec(v_val_763_);
lean_del_object(v___x_759_);
lean_del_object(v___x_751_);
lean_dec(v_val_727_);
v___x_768_ = lean_box(0);
return v___x_768_;
}
else
{
lean_object* v_val_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_786_; 
v_val_769_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_786_ == 0)
{
v___x_771_ = v___x_767_;
v_isShared_772_ = v_isSharedCheck_786_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_val_769_);
lean_dec(v___x_767_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_786_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_773_ = lean_box(v___y_747_);
if (v_isShared_760_ == 0)
{
lean_ctor_set_tag(v___x_759_, 0);
lean_ctor_set(v___x_759_, 1, v_val_769_);
lean_ctor_set(v___x_759_, 0, v___x_773_);
v___x_775_ = v___x_759_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_773_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_val_769_);
v___x_775_ = v_reuseFailAlloc_785_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_777_; 
if (v_isShared_772_ == 0)
{
lean_ctor_set(v___x_771_, 0, v___x_775_);
v___x_777_ = v___x_771_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_784_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 2, v___x_777_);
lean_ctor_set(v___x_751_, 1, v_val_763_);
lean_ctor_set(v___x_751_, 0, v_val_727_);
v___x_779_ = v___x_751_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_val_727_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_val_763_);
lean_ctor_set(v_reuseFailAlloc_783_, 2, v___x_777_);
v___x_779_ = v_reuseFailAlloc_783_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_781_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_779_);
v___x_781_ = v___x_765_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
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
lean_dec_ref_known(v_tail_754_, 2);
lean_dec_ref_known(v___x_753_, 2);
lean_del_object(v___x_751_);
goto v___jp_731_;
}
}
else
{
lean_dec(v_tail_754_);
lean_dec_ref_known(v___x_753_, 2);
lean_del_object(v___x_751_);
goto v___jp_731_;
}
}
else
{
lean_dec(v___x_753_);
lean_del_object(v___x_751_);
goto v___jp_731_;
}
}
}
v___jp_794_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_817_; 
v___x_795_ = lean_unsigned_to_nat(1u);
v___x_796_ = lean_nat_sub(v_endExclusive_730_, v_startInclusive_729_);
v___x_797_ = l_String_Slice_Pos_prevn(v_head_717_, v___x_796_, v___x_795_);
v_isSharedCheck_817_ = !lean_is_exclusive(v_head_717_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; lean_object* v_unused_819_; lean_object* v_unused_820_; 
v_unused_818_ = lean_ctor_get(v_head_717_, 2);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_head_717_, 1);
lean_dec(v_unused_819_);
v_unused_820_ = lean_ctor_get(v_head_717_, 0);
lean_dec(v_unused_820_);
v___x_799_ = v_head_717_;
v_isShared_800_ = v_isSharedCheck_817_;
goto v_resetjp_798_;
}
else
{
lean_dec(v_head_717_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_817_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_nat_add(v_startInclusive_729_, v___x_797_);
lean_dec(v___x_797_);
v___x_802_ = lean_string_utf8_extract_fast(v_str_728_, v_startInclusive_729_, v___x_801_);
lean_dec(v___x_801_);
lean_dec(v_startInclusive_729_);
lean_dec_ref(v_str_728_);
v___x_803_ = l_Lake_Toml_Time_ofString_x3f(v___x_802_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v___x_804_; 
lean_del_object(v___x_799_);
lean_dec(v_val_727_);
v___x_804_ = lean_box(0);
return v___x_804_;
}
else
{
lean_object* v_val_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_816_; 
v_val_805_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_816_ == 0)
{
v___x_807_ = v___x_803_;
v_isShared_808_ = v_isSharedCheck_816_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_val_805_);
lean_dec(v___x_803_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_816_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_box(0);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 2, v___x_809_);
lean_ctor_set(v___x_799_, 1, v_val_805_);
lean_ctor_set(v___x_799_, 0, v_val_727_);
v___x_811_ = v___x_799_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_val_727_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_val_805_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v___x_809_);
v___x_811_ = v_reuseFailAlloc_815_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_811_);
v___x_813_ = v___x_807_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
v___jp_821_:
{
uint32_t v___x_823_; uint8_t v___x_824_; 
v___x_823_ = 122;
v___x_824_ = lean_uint32_dec_eq(v___y_822_, v___x_823_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_825_ = 1;
v___x_826_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0, &l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___closed__0);
v___x_827_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_717_, v___x_826_, v___x_679_);
v___x_828_ = lean_array_to_list(v___x_827_);
if (lean_obj_tag(v___x_828_) == 1)
{
lean_object* v_tail_829_; 
v_tail_829_ = lean_ctor_get(v___x_828_, 1);
lean_inc(v_tail_829_);
if (lean_obj_tag(v_tail_829_) == 1)
{
lean_object* v_tail_830_; 
v_tail_830_ = lean_ctor_get(v_tail_829_, 1);
if (lean_obj_tag(v_tail_830_) == 0)
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_868_; 
lean_del_object(v___x_719_);
v_isSharedCheck_868_ = !lean_is_exclusive(v_head_717_);
if (v_isSharedCheck_868_ == 0)
{
lean_object* v_unused_869_; lean_object* v_unused_870_; lean_object* v_unused_871_; 
v_unused_869_ = lean_ctor_get(v_head_717_, 2);
lean_dec(v_unused_869_);
v_unused_870_ = lean_ctor_get(v_head_717_, 1);
lean_dec(v_unused_870_);
v_unused_871_ = lean_ctor_get(v_head_717_, 0);
lean_dec(v_unused_871_);
v___x_832_ = v_head_717_;
v_isShared_833_ = v_isSharedCheck_868_;
goto v_resetjp_831_;
}
else
{
lean_dec(v_head_717_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_868_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_head_834_; lean_object* v_head_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_866_; 
v_head_834_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_head_834_);
lean_dec_ref_known(v___x_828_, 2);
v_head_835_ = lean_ctor_get(v_tail_829_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_tail_829_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v_tail_829_, 1);
lean_dec(v_unused_867_);
v___x_837_ = v_tail_829_;
v_isShared_838_ = v_isSharedCheck_866_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_head_835_);
lean_dec(v_tail_829_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_866_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lake_Toml_Time_ofString_x3f(v_head_834_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_840_; 
lean_del_object(v___x_837_);
lean_dec(v_head_835_);
lean_del_object(v___x_832_);
lean_dec(v_val_727_);
v___x_840_ = lean_box(0);
return v___x_840_;
}
else
{
lean_object* v_val_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_865_; 
v_val_841_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_865_ == 0)
{
v___x_843_ = v___x_839_;
v_isShared_844_ = v_isSharedCheck_865_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_val_841_);
lean_dec(v___x_839_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_865_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lake_Toml_Time_ofString_x3f(v_head_835_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_846_; 
lean_del_object(v___x_843_);
lean_dec(v_val_841_);
lean_del_object(v___x_837_);
lean_del_object(v___x_832_);
lean_dec(v_val_727_);
v___x_846_ = lean_box(0);
return v___x_846_;
}
else
{
lean_object* v_val_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_864_; 
v_val_847_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_864_ == 0)
{
v___x_849_ = v___x_845_;
v_isShared_850_ = v_isSharedCheck_864_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_val_847_);
lean_dec(v___x_845_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_864_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_box(v___x_824_);
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 0);
lean_ctor_set(v___x_837_, 1, v_val_847_);
lean_ctor_set(v___x_837_, 0, v___x_851_);
v___x_853_ = v___x_837_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_863_, 1, v_val_847_);
v___x_853_ = v_reuseFailAlloc_863_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_855_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_853_);
v___x_855_ = v___x_849_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_862_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 2, v___x_855_);
lean_ctor_set(v___x_832_, 1, v_val_841_);
lean_ctor_set(v___x_832_, 0, v_val_727_);
v___x_857_ = v___x_832_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_val_727_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_val_841_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v___x_855_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_857_);
v___x_859_ = v___x_843_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
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
lean_inc(v_endExclusive_730_);
lean_inc(v_startInclusive_729_);
lean_inc_ref(v_str_728_);
lean_dec_ref_known(v_tail_829_, 2);
lean_dec_ref_known(v___x_828_, 2);
v___y_747_ = v___x_825_;
goto v___jp_746_;
}
}
else
{
lean_inc(v_endExclusive_730_);
lean_inc(v_startInclusive_729_);
lean_inc_ref(v_str_728_);
lean_dec(v_tail_829_);
lean_dec_ref_known(v___x_828_, 2);
v___y_747_ = v___x_825_;
goto v___jp_746_;
}
}
else
{
lean_inc(v_endExclusive_730_);
lean_inc(v_startInclusive_729_);
lean_inc_ref(v_str_728_);
lean_dec(v___x_828_);
v___y_747_ = v___x_825_;
goto v___jp_746_;
}
}
else
{
lean_inc(v_startInclusive_729_);
lean_inc_ref(v_str_728_);
lean_del_object(v___x_719_);
goto v___jp_794_;
}
}
v___jp_872_:
{
uint32_t v___x_874_; uint8_t v___x_875_; 
v___x_874_ = 90;
v___x_875_ = lean_uint32_dec_eq(v___y_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_nat_sub(v_endExclusive_730_, v_startInclusive_729_);
v___x_877_ = l_String_Slice_Pos_prev_x3f(v_head_717_, v___x_876_);
lean_dec(v___x_876_);
if (lean_obj_tag(v___x_877_) == 0)
{
uint32_t v___x_878_; 
v___x_878_ = 65;
v___y_822_ = v___x_878_;
goto v___jp_821_;
}
else
{
lean_object* v_val_879_; lean_object* v___x_880_; 
v_val_879_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v___x_877_, 1);
v___x_880_ = l_String_Slice_Pos_get_x3f(v_head_717_, v_val_879_);
lean_dec(v_val_879_);
if (lean_obj_tag(v___x_880_) == 0)
{
uint32_t v___x_881_; 
v___x_881_ = 65;
v___y_822_ = v___x_881_;
goto v___jp_821_;
}
else
{
lean_object* v_val_882_; uint32_t v___x_883_; 
v_val_882_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_val_882_);
lean_dec_ref_known(v___x_880_, 1);
v___x_883_ = lean_unbox_uint32(v_val_882_);
lean_dec(v_val_882_);
v___y_822_ = v___x_883_;
goto v___jp_821_;
}
}
}
else
{
lean_inc(v_startInclusive_729_);
lean_inc_ref(v_str_728_);
lean_del_object(v___x_719_);
goto v___jp_794_;
}
}
}
}
}
else
{
lean_object* v___x_894_; 
lean_dec_ref_known(v_tail_682_, 2);
lean_dec_ref_known(v___x_681_, 2);
v___x_894_ = lean_box(0);
return v___x_894_;
}
}
}
else
{
lean_object* v___x_895_; 
lean_dec(v___x_681_);
v___x_895_ = lean_box(0);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(lean_object* v_dt_896_, lean_object* v___x_897_, lean_object* v___x_898_, lean_object* v_inst_899_, lean_object* v_R_900_, lean_object* v_a_901_, lean_object* v_b_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_896_, v___x_897_, v___x_898_, v_a_901_, v_b_902_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___boxed(lean_object* v_dt_904_, lean_object* v___x_905_, lean_object* v___x_906_, lean_object* v_inst_907_, lean_object* v_R_908_, lean_object* v_a_909_, lean_object* v_b_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(v_dt_904_, v___x_905_, v___x_906_, v_inst_907_, v_R_908_, v_a_909_, v_b_910_);
lean_dec_ref(v___x_905_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(lean_object* v_head_912_, lean_object* v_inst_913_, lean_object* v_R_914_, lean_object* v_a_915_, lean_object* v_b_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_912_, v_a_915_, v_b_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___boxed(lean_object* v_head_918_, lean_object* v_inst_919_, lean_object* v_R_920_, lean_object* v_a_921_, lean_object* v_b_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(v_head_918_, v_inst_919_, v_R_920_, v_a_921_, v_b_922_);
lean_dec_ref(v_head_918_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(lean_object* v_head_924_, lean_object* v_inst_925_, lean_object* v_R_926_, lean_object* v_a_927_, lean_object* v_b_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_924_, v_a_927_, v_b_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___boxed(lean_object* v_head_930_, lean_object* v_inst_931_, lean_object* v_R_932_, lean_object* v_a_933_, lean_object* v_b_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(v_head_930_, v_inst_931_, v_R_932_, v_a_933_, v_b_934_);
lean_dec_ref(v_head_930_);
return v_res_935_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(lean_object* v_s_936_, lean_object* v_inst_937_, lean_object* v_R_938_, lean_object* v_a_939_, uint8_t v_b_940_, lean_object* v_c_941_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_936_, v_a_939_, v_b_940_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___boxed(lean_object* v_s_943_, lean_object* v_inst_944_, lean_object* v_R_945_, lean_object* v_a_946_, lean_object* v_b_947_, lean_object* v_c_948_){
_start:
{
uint8_t v_b_boxed_949_; uint8_t v_res_950_; lean_object* v_r_951_; 
v_b_boxed_949_ = lean_unbox(v_b_947_);
v_res_950_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(v_s_943_, v_inst_944_, v_R_945_, v_a_946_, v_b_boxed_949_, v_c_948_);
lean_dec_ref(v_s_943_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_DateTime_toString(lean_object* v_dt_956_){
_start:
{
switch(lean_obj_tag(v_dt_956_))
{
case 0:
{
lean_object* v_offset_x3f_957_; 
v_offset_x3f_957_ = lean_ctor_get(v_dt_956_, 2);
if (lean_obj_tag(v_offset_x3f_957_) == 1)
{
lean_object* v_val_958_; lean_object* v_fst_959_; uint8_t v___x_960_; 
v_val_958_ = lean_ctor_get(v_offset_x3f_957_, 0);
v_fst_959_ = lean_ctor_get(v_val_958_, 0);
v___x_960_ = lean_unbox(v_fst_959_);
if (v___x_960_ == 0)
{
lean_object* v_snd_961_; lean_object* v_date_962_; lean_object* v_time_963_; lean_object* v_hour_964_; lean_object* v_minute_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v_snd_961_ = lean_ctor_get(v_val_958_, 1);
lean_inc(v_snd_961_);
v_date_962_ = lean_ctor_get(v_dt_956_, 0);
lean_inc_ref(v_date_962_);
v_time_963_ = lean_ctor_get(v_dt_956_, 1);
lean_inc_ref(v_time_963_);
lean_dec_ref_known(v_dt_956_, 3);
v_hour_964_ = lean_ctor_get(v_snd_961_, 0);
lean_inc(v_hour_964_);
v_minute_965_ = lean_ctor_get(v_snd_961_, 1);
lean_inc(v_minute_965_);
lean_dec(v_snd_961_);
v___x_966_ = l_Lake_Date_toString(v_date_962_);
v___x_967_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_968_ = lean_string_append(v___x_966_, v___x_967_);
v___x_969_ = l_Lake_Toml_Time_toString(v_time_963_);
v___x_970_ = lean_string_append(v___x_968_, v___x_969_);
lean_dec_ref(v___x_969_);
v___x_971_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__1));
v___x_972_ = lean_string_append(v___x_970_, v___x_971_);
v___x_973_ = lean_unsigned_to_nat(2u);
v___x_974_ = l_Lake_zpad(v_hour_964_, v___x_973_);
v___x_975_ = lean_string_append(v___x_972_, v___x_974_);
lean_dec_ref(v___x_974_);
v___x_976_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_977_ = lean_string_append(v___x_975_, v___x_976_);
v___x_978_ = l_Lake_zpad(v_minute_965_, v___x_973_);
v___x_979_ = lean_string_append(v___x_977_, v___x_978_);
lean_dec_ref(v___x_978_);
return v___x_979_;
}
else
{
lean_object* v_snd_980_; lean_object* v_date_981_; lean_object* v_time_982_; lean_object* v_hour_983_; lean_object* v_minute_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_snd_980_ = lean_ctor_get(v_val_958_, 1);
lean_inc(v_snd_980_);
v_date_981_ = lean_ctor_get(v_dt_956_, 0);
lean_inc_ref(v_date_981_);
v_time_982_ = lean_ctor_get(v_dt_956_, 1);
lean_inc_ref(v_time_982_);
lean_dec_ref_known(v_dt_956_, 3);
v_hour_983_ = lean_ctor_get(v_snd_980_, 0);
lean_inc(v_hour_983_);
v_minute_984_ = lean_ctor_get(v_snd_980_, 1);
lean_inc(v_minute_984_);
lean_dec(v_snd_980_);
v___x_985_ = l_Lake_Date_toString(v_date_981_);
v___x_986_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_987_ = lean_string_append(v___x_985_, v___x_986_);
v___x_988_ = l_Lake_Toml_Time_toString(v_time_982_);
v___x_989_ = lean_string_append(v___x_987_, v___x_988_);
lean_dec_ref(v___x_988_);
v___x_990_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__2));
v___x_991_ = lean_string_append(v___x_989_, v___x_990_);
v___x_992_ = lean_unsigned_to_nat(2u);
v___x_993_ = l_Lake_zpad(v_hour_983_, v___x_992_);
v___x_994_ = lean_string_append(v___x_991_, v___x_993_);
lean_dec_ref(v___x_993_);
v___x_995_ = ((lean_object*)(l_Lake_Toml_Time_toString___closed__0));
v___x_996_ = lean_string_append(v___x_994_, v___x_995_);
v___x_997_ = l_Lake_zpad(v_minute_984_, v___x_992_);
v___x_998_ = lean_string_append(v___x_996_, v___x_997_);
lean_dec_ref(v___x_997_);
return v___x_998_;
}
}
else
{
lean_object* v_date_999_; lean_object* v_time_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_date_999_ = lean_ctor_get(v_dt_956_, 0);
lean_inc_ref(v_date_999_);
v_time_1000_ = lean_ctor_get(v_dt_956_, 1);
lean_inc_ref(v_time_1000_);
lean_dec_ref_known(v_dt_956_, 3);
v___x_1001_ = l_Lake_Date_toString(v_date_999_);
v___x_1002_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_1003_ = lean_string_append(v___x_1001_, v___x_1002_);
v___x_1004_ = l_Lake_Toml_Time_toString(v_time_1000_);
v___x_1005_ = lean_string_append(v___x_1003_, v___x_1004_);
lean_dec_ref(v___x_1004_);
v___x_1006_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__3));
v___x_1007_ = lean_string_append(v___x_1005_, v___x_1006_);
return v___x_1007_;
}
}
case 1:
{
lean_object* v_date_1008_; lean_object* v_time_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_date_1008_ = lean_ctor_get(v_dt_956_, 0);
lean_inc_ref(v_date_1008_);
v_time_1009_ = lean_ctor_get(v_dt_956_, 1);
lean_inc_ref(v_time_1009_);
lean_dec_ref_known(v_dt_956_, 2);
v___x_1010_ = l_Lake_Date_toString(v_date_1008_);
v___x_1011_ = ((lean_object*)(l_Lake_Toml_DateTime_toString___closed__0));
v___x_1012_ = lean_string_append(v___x_1010_, v___x_1011_);
v___x_1013_ = l_Lake_Toml_Time_toString(v_time_1009_);
v___x_1014_ = lean_string_append(v___x_1012_, v___x_1013_);
lean_dec_ref(v___x_1013_);
return v___x_1014_;
}
case 2:
{
lean_object* v_date_1015_; lean_object* v___x_1016_; 
v_date_1015_ = lean_ctor_get(v_dt_956_, 0);
lean_inc_ref(v_date_1015_);
lean_dec_ref_known(v_dt_956_, 1);
v___x_1016_ = l_Lake_Date_toString(v_date_1015_);
return v___x_1016_;
}
default: 
{
lean_object* v_time_1017_; lean_object* v___x_1018_; 
v_time_1017_ = lean_ctor_get(v_dt_956_, 0);
lean_inc_ref(v_time_1017_);
lean_dec_ref_known(v_dt_956_, 1);
v___x_1018_ = l_Lake_Toml_Time_toString(v_time_1017_);
return v___x_1018_;
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

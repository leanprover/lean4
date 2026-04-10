// Lean compiler output
// Module: Std.Internal.Http.Data.Headers.Basic
// Imports: public import Std.Internal.Http.Data.Headers.Name public import Std.Internal.Http.Data.Headers.Value public import Std.Internal.Parsec.Basic import Init.Data.String.Search
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_Http_Internal_isToken(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* l_String_intercalate(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
extern lean_object* l_Std_Http_Header_Name_contentLength;
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0_value;
static const lean_string_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2_value;
static const lean_string_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3_value;
static lean_once_cell_t l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4;
static const lean_string_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__5 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader(lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0 = (const lean_object*)&l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqContentLength_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqContentLength_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instBEqContentLength___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instBEqContentLength_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instBEqContentLength___closed__0 = (const lean_object*)&l_Std_Http_Header_instBEqContentLength___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instBEqContentLength = (const lean_object*)&l_Std_Http_Header_instBEqContentLength___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprContentLength_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Http_Header_instReprContentLength_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "length"};
static const lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_instReprContentLength_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Header_instReprContentLength_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__2_value)}};
static const lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Header_instReprContentLength_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__3_value),((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6_value;
static lean_once_cell_t l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7;
static const lean_string_object l_Std_Http_Header_instReprContentLength_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__8_value;
static lean_once_cell_t l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9;
static lean_once_cell_t l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10;
static const lean_ctor_object l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11_value;
static const lean_ctor_object l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__8_value)}};
static const lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12 = (const lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instReprContentLength___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instReprContentLength_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instReprContentLength___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprContentLength___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instReprContentLength = (const lean_object*)&l_Std_Http_Header_instReprContentLength___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_parse(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_serialize(lean_object*);
static const lean_closure_object l_Std_Http_Header_ContentLength_inst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_ContentLength_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_ContentLength_inst___closed__0 = (const lean_object*)&l_Std_Http_Header_ContentLength_inst___closed__0_value;
static const lean_closure_object l_Std_Http_Header_ContentLength_inst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_ContentLength_serialize, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_ContentLength_inst___closed__1 = (const lean_object*)&l_Std_Http_Header_ContentLength_inst___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_ContentLength_inst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Header_ContentLength_inst___closed__0_value),((lean_object*)&l_Std_Http_Header_ContentLength_inst___closed__1_value)}};
static const lean_object* l_Std_Http_Header_ContentLength_inst___closed__2 = (const lean_object*)&l_Std_Http_Header_ContentLength_inst___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_ContentLength_inst = (const lean_object*)&l_Std_Http_Header_ContentLength_inst___closed__2_value;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "chunked"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Header_TransferEncoding_Validate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0_value)}};
static const lean_object* l_Std_Http_Header_TransferEncoding_Validate___closed__0 = (const lean_object*)&l_Std_Http_Header_TransferEncoding_Validate___closed__0_value;
static const lean_array_object l_Std_Http_Header_TransferEncoding_Validate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Http_Header_TransferEncoding_Validate___closed__1 = (const lean_object*)&l_Std_Http_Header_TransferEncoding_Validate___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_Validate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0 = (const lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0_value;
static const lean_string_object l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1 = (const lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2 = (const lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3 = (const lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3_value;
static const lean_string_object l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4 = (const lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5;
static lean_once_cell_t l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6;
static const lean_ctor_object l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7 = (const lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8 = (const lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8_value;
static const lean_string_object l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__9 = (const lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10 = (const lean_object*)&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(lean_object*);
static const lean_string_object l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "codings"};
static const lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__2_value),((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4;
static const lean_string_object l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isValid"};
static const lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__5_value;
static const lean_ctor_object l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6_value;
static const lean_string_object l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__7 = (const lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__7_value)}};
static const lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instReprTransferEncoding___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instReprTransferEncoding_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instReprTransferEncoding___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprTransferEncoding___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instReprTransferEncoding = (const lean_object*)&l_Std_Http_Header_instReprTransferEncoding___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_isChunked___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_serialize(lean_object*);
static const lean_closure_object l_Std_Http_Header_TransferEncoding_inst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_TransferEncoding_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_TransferEncoding_inst___closed__0 = (const lean_object*)&l_Std_Http_Header_TransferEncoding_inst___closed__0_value;
static const lean_closure_object l_Std_Http_Header_TransferEncoding_inst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_TransferEncoding_serialize, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_TransferEncoding_inst___closed__1 = (const lean_object*)&l_Std_Http_Header_TransferEncoding_inst___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_TransferEncoding_inst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Header_TransferEncoding_inst___closed__0_value),((lean_object*)&l_Std_Http_Header_TransferEncoding_inst___closed__1_value)}};
static const lean_object* l_Std_Http_Header_TransferEncoding_inst___closed__2 = (const lean_object*)&l_Std_Http_Header_TransferEncoding_inst___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_TransferEncoding_inst = (const lean_object*)&l_Std_Http_Header_TransferEncoding_inst___closed__2_value;
static const lean_string_object l_Std_Http_Header_instReprConnection_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tokens"};
static const lean_object* l_Std_Http_Header_instReprConnection_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprConnection_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Header_instReprConnection_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprConnection_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Header_instReprConnection_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Header_instReprConnection_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_instReprConnection_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_instReprConnection_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Header_instReprConnection_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Header_instReprConnection_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Header_instReprConnection_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprConnection_repr___redArg___closed__2_value),((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Header_instReprConnection_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Header_instReprConnection_repr___redArg___closed__3_value;
static const lean_string_object l_Std_Http_Header_instReprConnection_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "valid"};
static const lean_object* l_Std_Http_Header_instReprConnection_repr___redArg___closed__4 = (const lean_object*)&l_Std_Http_Header_instReprConnection_repr___redArg___closed__4_value;
static const lean_ctor_object l_Std_Http_Header_instReprConnection_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprConnection_repr___redArg___closed__4_value)}};
static const lean_object* l_Std_Http_Header_instReprConnection_repr___redArg___closed__5 = (const lean_object*)&l_Std_Http_Header_instReprConnection_repr___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instReprConnection___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instReprConnection_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instReprConnection___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprConnection___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instReprConnection = (const lean_object*)&l_Std_Http_Header_instReprConnection___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_containsToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_containsToken___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Header_Connection_shouldClose___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "close"};
static const lean_object* l_Std_Http_Header_Connection_shouldClose___closed__0 = (const lean_object*)&l_Std_Http_Header_Connection_shouldClose___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_shouldClose(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_shouldClose___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_parse(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_serialize(lean_object*);
static const lean_closure_object l_Std_Http_Header_Connection_inst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Connection_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Connection_inst___closed__0 = (const lean_object*)&l_Std_Http_Header_Connection_inst___closed__0_value;
static const lean_closure_object l_Std_Http_Header_Connection_inst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Connection_serialize, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Connection_inst___closed__1 = (const lean_object*)&l_Std_Http_Header_Connection_inst___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_Connection_inst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Header_Connection_inst___closed__0_value),((lean_object*)&l_Std_Http_Header_Connection_inst___closed__1_value)}};
static const lean_object* l_Std_Http_Header_Connection_inst___closed__2 = (const lean_object*)&l_Std_Http_Header_Connection_inst___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Connection_inst = (const lean_object*)&l_Std_Http_Header_Connection_inst___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v_fst_4_, lean_object* v___x_5_, uint32_t v___x_6_, lean_object* v___x_7_, lean_object* v_it_8_, lean_object* v_acc_9_, lean_object* v_hP_10_, lean_object* v_recur_11_){
_start:
{
lean_object* v_it_13_; lean_object* v_out_14_; lean_object* v_it_30_; lean_object* v_startInclusive_31_; lean_object* v_endExclusive_32_; 
if (lean_obj_tag(v_it_8_) == 0)
{
lean_object* v_currPos_44_; lean_object* v_searcher_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_67_; 
v_currPos_44_ = lean_ctor_get(v_it_8_, 0);
v_searcher_45_ = lean_ctor_get(v_it_8_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_it_8_);
if (v_isSharedCheck_67_ == 0)
{
v___x_47_ = v_it_8_;
v_isShared_48_ = v_isSharedCheck_67_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_searcher_45_);
lean_inc(v_currPos_44_);
lean_dec(v_it_8_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_67_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
uint8_t v___x_49_; 
v___x_49_ = lean_nat_dec_eq(v_searcher_45_, v___x_5_);
if (v___x_49_ == 0)
{
uint32_t v___x_50_; uint8_t v___x_51_; 
lean_dec(v___x_5_);
v___x_50_ = lean_string_utf8_get_fast(v_fst_4_, v_searcher_45_);
v___x_51_ = lean_uint32_dec_eq(v___x_50_, v___x_6_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_52_ = lean_string_utf8_next_fast(v_fst_4_, v_searcher_45_);
lean_dec(v_searcher_45_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v___x_52_);
v___x_54_ = v___x_47_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_currPos_44_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v___x_52_);
v___x_54_ = v_reuseFailAlloc_56_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
lean_object* v___x_55_; 
v___x_55_ = lean_apply_4(v_recur_11_, v___x_54_, v_acc_9_, lean_box(0), lean_box(0));
return v___x_55_;
}
}
else
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v_slice_60_; lean_object* v_nextIt_62_; 
v___x_57_ = lean_string_utf8_next_fast(v_fst_4_, v_searcher_45_);
v___x_58_ = lean_nat_sub(v___x_57_, v_searcher_45_);
v___x_59_ = lean_nat_add(v_searcher_45_, v___x_58_);
lean_dec(v___x_58_);
v_slice_60_ = l_String_Slice_subslice_x21(v___x_7_, v_currPos_44_, v_searcher_45_);
lean_inc(v___x_59_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v___x_59_);
lean_ctor_set(v___x_47_, 0, v___x_59_);
v_nextIt_62_ = v___x_47_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_59_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_59_);
v_nextIt_62_ = v_reuseFailAlloc_65_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v_startInclusive_63_; lean_object* v_endExclusive_64_; 
v_startInclusive_63_ = lean_ctor_get(v_slice_60_, 0);
lean_inc(v_startInclusive_63_);
v_endExclusive_64_ = lean_ctor_get(v_slice_60_, 1);
lean_inc(v_endExclusive_64_);
lean_dec_ref(v_slice_60_);
v_it_30_ = v_nextIt_62_;
v_startInclusive_31_ = v_startInclusive_63_;
v_endExclusive_32_ = v_endExclusive_64_;
goto v___jp_29_;
}
}
}
else
{
lean_object* v___x_66_; 
lean_del_object(v___x_47_);
lean_dec(v_searcher_45_);
v___x_66_ = lean_box(1);
v_it_30_ = v___x_66_;
v_startInclusive_31_ = v_currPos_44_;
v_endExclusive_32_ = v___x_5_;
goto v___jp_29_;
}
}
}
else
{
lean_dec_ref(v_recur_11_);
lean_dec(v___x_5_);
return v_acc_9_;
}
v___jp_12_:
{
if (lean_obj_tag(v_acc_9_) == 0)
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v_out_14_);
v___x_16_ = lean_apply_4(v_recur_11_, v_it_13_, v___x_15_, lean_box(0), lean_box(0));
return v___x_16_;
}
else
{
lean_object* v_val_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_28_; 
v_val_17_ = lean_ctor_get(v_acc_9_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v_acc_9_);
if (v_isSharedCheck_28_ == 0)
{
v___x_19_ = v_acc_9_;
v_isShared_20_ = v_isSharedCheck_28_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_val_17_);
lean_dec(v_acc_9_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_28_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_21_ = lean_string_utf8_extract(v___x_1_, v___x_2_, v___x_3_);
v___x_22_ = lean_string_append(v_val_17_, v___x_21_);
lean_dec_ref(v___x_21_);
v___x_23_ = lean_string_append(v___x_22_, v_out_14_);
lean_dec_ref(v_out_14_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_23_);
v___x_25_ = v___x_19_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_23_);
v___x_25_ = v_reuseFailAlloc_27_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; 
v___x_26_ = lean_apply_4(v_recur_11_, v_it_13_, v___x_25_, lean_box(0), lean_box(0));
return v___x_26_;
}
}
}
}
v___jp_29_:
{
lean_object* v___x_33_; uint32_t v___x_34_; uint32_t v___x_35_; uint8_t v___x_36_; 
v___x_33_ = lean_string_utf8_extract(v_fst_4_, v_startInclusive_31_, v_endExclusive_32_);
lean_dec(v_endExclusive_32_);
lean_dec(v_startInclusive_31_);
v___x_34_ = lean_string_utf8_get(v___x_33_, v___x_2_);
v___x_35_ = 97;
v___x_36_ = lean_uint32_dec_le(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; 
v___x_37_ = lean_string_utf8_set(v___x_33_, v___x_2_, v___x_34_);
v_it_13_ = v_it_30_;
v_out_14_ = v___x_37_;
goto v___jp_12_;
}
else
{
uint32_t v___x_38_; uint8_t v___x_39_; 
v___x_38_ = 122;
v___x_39_ = lean_uint32_dec_le(v___x_34_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; 
v___x_40_ = lean_string_utf8_set(v___x_33_, v___x_2_, v___x_34_);
v_it_13_ = v_it_30_;
v_out_14_ = v___x_40_;
goto v___jp_12_;
}
else
{
uint32_t v___x_41_; uint32_t v___x_42_; lean_object* v___x_43_; 
v___x_41_ = 4294967264;
v___x_42_ = lean_uint32_add(v___x_34_, v___x_41_);
v___x_43_ = lean_string_utf8_set(v___x_33_, v___x_2_, v___x_42_);
v_it_13_ = v_it_30_;
v_out_14_ = v___x_43_;
goto v___jp_12_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed(lean_object* v___x_68_, lean_object* v___x_69_, lean_object* v___x_70_, lean_object* v_fst_71_, lean_object* v___x_72_, lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v_it_75_, lean_object* v_acc_76_, lean_object* v_hP_77_, lean_object* v_recur_78_){
_start:
{
uint32_t v___x_1336__boxed_79_; lean_object* v_res_80_; 
v___x_1336__boxed_79_ = lean_unbox_uint32(v___x_73_);
lean_dec(v___x_73_);
v_res_80_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(v___x_68_, v___x_69_, v___x_70_, v_fst_71_, v___x_72_, v___x_1336__boxed_79_, v___x_74_, v_it_75_, v_acc_76_, v_hP_77_, v_recur_78_);
lean_dec_ref(v___x_74_);
lean_dec_ref(v_fst_71_);
lean_dec(v___x_70_);
lean_dec(v___x_69_);
lean_dec_ref(v___x_68_);
return v_res_80_;
}
}
static lean_object* _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3));
v___x_86_ = lean_string_utf8_byte_size(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_88_; lean_object* v___x_89_; 
v___x_88_ = 45;
v___x_89_ = lean_box_uint32(v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1(lean_object* v_h_90_, lean_object* v_buffer_91_, lean_object* v_a_92_){
_start:
{
lean_object* v_serialize_93_; lean_object* v___x_94_; lean_object* v_fst_95_; lean_object* v_snd_96_; lean_object* v___y_98_; lean_object* v___f_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v_it_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_serialize_93_ = lean_ctor_get(v_h_90_, 1);
lean_inc_ref(v_serialize_93_);
lean_dec_ref(v_h_90_);
v___x_94_ = lean_apply_1(v_serialize_93_, v_a_92_);
v_fst_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc_n(v_fst_95_, 2);
v_snd_96_ = lean_ctor_get(v___x_94_, 1);
lean_inc(v_snd_96_);
lean_dec_ref(v___x_94_);
v___f_117_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2));
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_string_utf8_byte_size(v_fst_95_);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v_fst_95_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
lean_inc_ref(v___x_120_);
v_it_121_ = l_String_Slice_splitToSubslice___redArg(v___x_120_, v___f_117_);
v___x_122_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3));
v___x_123_ = lean_obj_once(&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4, &l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4_once, _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4);
v___x_124_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1;
v___f_125_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_125_, 0, v___x_122_);
lean_closure_set(v___f_125_, 1, v___x_118_);
lean_closure_set(v___f_125_, 2, v___x_123_);
lean_closure_set(v___f_125_, 3, v_fst_95_);
lean_closure_set(v___f_125_, 4, v___x_119_);
lean_closure_set(v___f_125_, 5, v___x_124_);
lean_closure_set(v___f_125_, 6, v___x_120_);
v___x_126_ = lean_box(0);
v___x_127_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_125_, v_it_121_, v___x_126_, lean_box(0));
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v___x_128_; 
v___x_128_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__5));
v___y_98_ = v___x_128_;
goto v___jp_97_;
}
else
{
lean_object* v_val_129_; 
v_val_129_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_val_129_);
lean_dec_ref(v___x_127_);
v___y_98_ = v_val_129_;
goto v___jp_97_;
}
v___jp_97_:
{
lean_object* v_data_99_; lean_object* v_size_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_116_; 
v_data_99_ = lean_ctor_get(v_buffer_91_, 0);
v_size_100_ = lean_ctor_get(v_buffer_91_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_buffer_91_);
if (v_isSharedCheck_116_ == 0)
{
v___x_102_ = v_buffer_91_;
v_isShared_103_ = v_isSharedCheck_116_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_size_100_);
lean_inc(v_data_99_);
lean_dec(v_buffer_91_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_116_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_104_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0));
v___x_105_ = lean_string_append(v___y_98_, v___x_104_);
v___x_106_ = lean_string_append(v___x_105_, v_snd_96_);
lean_dec(v_snd_96_);
v___x_107_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1));
v___x_108_ = lean_string_append(v___x_106_, v___x_107_);
v___x_109_ = lean_string_to_utf8(v___x_108_);
lean_dec_ref(v___x_108_);
lean_inc_ref(v___x_109_);
v___x_110_ = lean_array_push(v_data_99_, v___x_109_);
v___x_111_ = lean_byte_array_size(v___x_109_);
lean_dec_ref(v___x_109_);
v___x_112_ = lean_nat_add(v_size_100_, v___x_111_);
lean_dec(v_size_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_112_);
lean_ctor_set(v___x_102_, 0, v___x_110_);
v___x_114_ = v___x_102_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg(lean_object* v_h_130_){
_start:
{
lean_object* v___f_131_; 
v___f_131_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1), 3, 1);
lean_closure_set(v___f_131_, 0, v_h_130_);
return v___f_131_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader(lean_object* v_00_u03b1_132_, lean_object* v_h_133_){
_start:
{
lean_object* v___f_134_; 
v___f_134_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1), 3, 1);
lean_closure_set(v___f_134_, 0, v_h_133_);
return v___f_134_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(lean_object* v_s_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0));
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(lean_object* v_s_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v_s_139_);
lean_dec_ref(v_s_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(lean_object* v_s_141_, lean_object* v_p_142_){
_start:
{
uint32_t v___y_144_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = lean_string_utf8_byte_size(v_s_141_);
v___x_150_ = lean_nat_dec_eq(v_p_142_, v___x_149_);
if (v___x_150_ == 0)
{
uint32_t v___x_151_; uint32_t v___x_152_; uint8_t v___x_153_; 
v___x_151_ = lean_string_utf8_get_fast(v_s_141_, v_p_142_);
v___x_152_ = 65;
v___x_153_ = lean_uint32_dec_le(v___x_152_, v___x_151_);
if (v___x_153_ == 0)
{
v___y_144_ = v___x_151_;
goto v___jp_143_;
}
else
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 90;
v___x_155_ = lean_uint32_dec_le(v___x_151_, v___x_154_);
if (v___x_155_ == 0)
{
v___y_144_ = v___x_151_;
goto v___jp_143_;
}
else
{
uint32_t v___x_156_; uint32_t v___x_157_; 
v___x_156_ = 32;
v___x_157_ = lean_uint32_add(v___x_151_, v___x_156_);
v___y_144_ = v___x_157_;
goto v___jp_143_;
}
}
}
else
{
lean_dec(v_p_142_);
return v_s_141_;
}
v___jp_143_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
lean_inc(v_p_142_);
v___x_145_ = lean_string_utf8_set(v_s_141_, v_p_142_, v___y_144_);
v___x_146_ = l_Char_utf8Size(v___y_144_);
v___x_147_ = lean_nat_add(v_p_142_, v___x_146_);
lean_dec(v___x_146_);
lean_dec(v_p_142_);
v_s_141_ = v___x_145_;
v_p_142_ = v___x_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t v_sz_158_, size_t v_i_159_, lean_object* v_bs_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = lean_usize_dec_lt(v_i_159_, v_sz_158_);
if (v___x_161_ == 0)
{
return v_bs_160_;
}
else
{
lean_object* v_v_162_; lean_object* v___x_163_; lean_object* v_bs_x27_164_; lean_object* v___x_165_; lean_object* v___x_166_; size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; 
v_v_162_ = lean_array_uget(v_bs_160_, v_i_159_);
v___x_163_ = lean_unsigned_to_nat(0u);
v_bs_x27_164_ = lean_array_uset(v_bs_160_, v_i_159_, v___x_163_);
v___x_165_ = l_String_Slice_toString(v_v_162_);
lean_dec(v_v_162_);
v___x_166_ = l_String_mapAux___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_165_, v___x_163_);
v___x_167_ = ((size_t)1ULL);
v___x_168_ = lean_usize_add(v_i_159_, v___x_167_);
v___x_169_ = lean_array_uset(v_bs_x27_164_, v_i_159_, v___x_166_);
v_i_159_ = v___x_168_;
v_bs_160_ = v___x_169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(lean_object* v_sz_171_, lean_object* v_i_172_, lean_object* v_bs_173_){
_start:
{
size_t v_sz_boxed_174_; size_t v_i_boxed_175_; lean_object* v_res_176_; 
v_sz_boxed_174_ = lean_unbox_usize(v_sz_171_);
lean_dec(v_sz_171_);
v_i_boxed_175_ = lean_unbox_usize(v_i_172_);
lean_dec(v_i_172_);
v_res_176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_boxed_174_, v_i_boxed_175_, v_bs_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v___x_179_, lean_object* v_a_180_, lean_object* v_b_181_){
_start:
{
lean_object* v_it_183_; lean_object* v_startInclusive_184_; lean_object* v_endExclusive_185_; 
if (lean_obj_tag(v_a_180_) == 0)
{
lean_object* v_currPos_190_; lean_object* v_searcher_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_220_; 
v_currPos_190_ = lean_ctor_get(v_a_180_, 0);
v_searcher_191_ = lean_ctor_get(v_a_180_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v_a_180_);
if (v_isSharedCheck_220_ == 0)
{
v___x_193_ = v_a_180_;
v_isShared_194_ = v_isSharedCheck_220_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_searcher_191_);
lean_inc(v_currPos_190_);
lean_dec(v_a_180_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_220_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v_str_195_; lean_object* v_startInclusive_196_; lean_object* v_endExclusive_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_str_195_ = lean_ctor_get(v___x_178_, 0);
v_startInclusive_196_ = lean_ctor_get(v___x_178_, 1);
v_endExclusive_197_ = lean_ctor_get(v___x_178_, 2);
v___x_198_ = lean_nat_sub(v_endExclusive_197_, v_startInclusive_196_);
v___x_199_ = lean_nat_dec_eq(v_searcher_191_, v___x_198_);
lean_dec(v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; uint32_t v___x_201_; uint32_t v___x_202_; uint8_t v___x_203_; 
v___x_200_ = lean_nat_add(v_startInclusive_196_, v_searcher_191_);
v___x_201_ = lean_string_utf8_get_fast(v_str_195_, v___x_200_);
v___x_202_ = 44;
v___x_203_ = lean_uint32_dec_eq(v___x_201_, v___x_202_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_207_; 
lean_dec(v_searcher_191_);
v___x_204_ = lean_string_utf8_next_fast(v_str_195_, v___x_200_);
lean_dec(v___x_200_);
v___x_205_ = lean_nat_sub(v___x_204_, v_startInclusive_196_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 1, v___x_205_);
v___x_207_ = v___x_193_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_currPos_190_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_209_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
v_a_180_ = v___x_207_;
goto _start;
}
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v_slice_213_; lean_object* v_nextIt_215_; 
v___x_210_ = lean_string_utf8_next_fast(v_str_195_, v___x_200_);
v___x_211_ = lean_nat_sub(v___x_210_, v___x_200_);
lean_dec(v___x_200_);
v___x_212_ = lean_nat_add(v_searcher_191_, v___x_211_);
lean_dec(v___x_211_);
v_slice_213_ = l_String_Slice_subslice_x21(v___x_178_, v_currPos_190_, v_searcher_191_);
lean_inc(v___x_212_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 1, v___x_212_);
lean_ctor_set(v___x_193_, 0, v___x_212_);
v_nextIt_215_ = v___x_193_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_212_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_212_);
v_nextIt_215_ = v_reuseFailAlloc_218_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v_startInclusive_216_; lean_object* v_endExclusive_217_; 
v_startInclusive_216_ = lean_ctor_get(v_slice_213_, 0);
lean_inc(v_startInclusive_216_);
v_endExclusive_217_ = lean_ctor_get(v_slice_213_, 1);
lean_inc(v_endExclusive_217_);
lean_dec_ref(v_slice_213_);
v_it_183_ = v_nextIt_215_;
v_startInclusive_184_ = v_startInclusive_216_;
v_endExclusive_185_ = v_endExclusive_217_;
goto v___jp_182_;
}
}
}
else
{
lean_object* v___x_219_; 
lean_del_object(v___x_193_);
lean_dec(v_searcher_191_);
v___x_219_ = lean_box(1);
lean_inc(v___x_179_);
v_it_183_ = v___x_219_;
v_startInclusive_184_ = v_currPos_190_;
v_endExclusive_185_ = v___x_179_;
goto v___jp_182_;
}
}
}
else
{
lean_dec(v___x_179_);
lean_dec_ref(v___x_177_);
return v_b_181_;
}
v___jp_182_:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc_ref(v___x_177_);
v___x_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_186_, 0, v___x_177_);
lean_ctor_set(v___x_186_, 1, v_startInclusive_184_);
lean_ctor_set(v___x_186_, 2, v_endExclusive_185_);
v___x_187_ = l_String_Slice_trimAscii(v___x_186_);
v___x_188_ = lean_array_push(v_b_181_, v___x_187_);
v_a_180_ = v_it_183_;
v_b_181_ = v___x_188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(lean_object* v___x_221_, lean_object* v___x_222_, lean_object* v___x_223_, lean_object* v_a_224_, lean_object* v_b_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_221_, v___x_222_, v___x_223_, v_a_224_, v_b_225_);
lean_dec_ref(v___x_222_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(lean_object* v___x_227_, lean_object* v___x_228_, lean_object* v___x_229_, lean_object* v_a_230_, lean_object* v_b_231_){
_start:
{
lean_object* v_it_233_; lean_object* v_startInclusive_234_; lean_object* v_endExclusive_235_; 
if (lean_obj_tag(v_a_230_) == 0)
{
lean_object* v_currPos_240_; lean_object* v_searcher_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_270_; 
v_currPos_240_ = lean_ctor_get(v_a_230_, 0);
v_searcher_241_ = lean_ctor_get(v_a_230_, 1);
v_isSharedCheck_270_ = !lean_is_exclusive(v_a_230_);
if (v_isSharedCheck_270_ == 0)
{
v___x_243_ = v_a_230_;
v_isShared_244_ = v_isSharedCheck_270_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_searcher_241_);
lean_inc(v_currPos_240_);
lean_dec(v_a_230_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_270_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v_str_245_; lean_object* v_startInclusive_246_; lean_object* v_endExclusive_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v_str_245_ = lean_ctor_get(v___x_228_, 0);
v_startInclusive_246_ = lean_ctor_get(v___x_228_, 1);
v_endExclusive_247_ = lean_ctor_get(v___x_228_, 2);
v___x_248_ = lean_nat_sub(v_endExclusive_247_, v_startInclusive_246_);
v___x_249_ = lean_nat_dec_eq(v_searcher_241_, v___x_248_);
lean_dec(v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint32_t v___x_251_; uint32_t v___x_252_; uint8_t v___x_253_; 
v___x_250_ = lean_nat_add(v_startInclusive_246_, v_searcher_241_);
v___x_251_ = lean_string_utf8_get_fast(v_str_245_, v___x_250_);
v___x_252_ = 44;
v___x_253_ = lean_uint32_dec_eq(v___x_251_, v___x_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
lean_dec(v_searcher_241_);
v___x_254_ = lean_string_utf8_next_fast(v_str_245_, v___x_250_);
lean_dec(v___x_250_);
v___x_255_ = lean_nat_sub(v___x_254_, v_startInclusive_246_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v___x_255_);
v___x_257_ = v___x_243_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_currPos_240_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_255_);
v___x_257_ = v_reuseFailAlloc_259_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; 
v___x_258_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_227_, v___x_228_, v___x_229_, v___x_257_, v_b_231_);
return v___x_258_;
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_slice_263_; lean_object* v_nextIt_265_; 
v___x_260_ = lean_string_utf8_next_fast(v_str_245_, v___x_250_);
v___x_261_ = lean_nat_sub(v___x_260_, v___x_250_);
lean_dec(v___x_250_);
v___x_262_ = lean_nat_add(v_searcher_241_, v___x_261_);
lean_dec(v___x_261_);
v_slice_263_ = l_String_Slice_subslice_x21(v___x_228_, v_currPos_240_, v_searcher_241_);
lean_inc(v___x_262_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v___x_262_);
lean_ctor_set(v___x_243_, 0, v___x_262_);
v_nextIt_265_ = v___x_243_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_262_);
v_nextIt_265_ = v_reuseFailAlloc_268_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v_startInclusive_266_; lean_object* v_endExclusive_267_; 
v_startInclusive_266_ = lean_ctor_get(v_slice_263_, 0);
lean_inc(v_startInclusive_266_);
v_endExclusive_267_ = lean_ctor_get(v_slice_263_, 1);
lean_inc(v_endExclusive_267_);
lean_dec_ref(v_slice_263_);
v_it_233_ = v_nextIt_265_;
v_startInclusive_234_ = v_startInclusive_266_;
v_endExclusive_235_ = v_endExclusive_267_;
goto v___jp_232_;
}
}
}
else
{
lean_object* v___x_269_; 
lean_del_object(v___x_243_);
lean_dec(v_searcher_241_);
v___x_269_ = lean_box(1);
lean_inc(v___x_229_);
v_it_233_ = v___x_269_;
v_startInclusive_234_ = v_currPos_240_;
v_endExclusive_235_ = v___x_229_;
goto v___jp_232_;
}
}
}
else
{
lean_dec(v___x_229_);
lean_dec_ref(v___x_227_);
return v_b_231_;
}
v___jp_232_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_inc_ref(v___x_227_);
v___x_236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_236_, 0, v___x_227_);
lean_ctor_set(v___x_236_, 1, v_startInclusive_234_);
lean_ctor_set(v___x_236_, 2, v_endExclusive_235_);
v___x_237_ = l_String_Slice_trimAscii(v___x_236_);
v___x_238_ = lean_array_push(v_b_231_, v___x_237_);
v___x_239_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_227_, v___x_228_, v___x_229_, v_it_233_, v___x_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(lean_object* v___x_271_, lean_object* v___x_272_, lean_object* v___x_273_, lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_271_, v___x_272_, v___x_273_, v_a_274_, v_b_275_);
lean_dec_ref(v___x_272_);
return v_res_276_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object* v___x_277_, lean_object* v___x_278_, lean_object* v___x_279_, lean_object* v_a_280_, uint8_t v_b_281_){
_start:
{
if (lean_obj_tag(v_a_280_) == 0)
{
lean_object* v_currPos_282_; lean_object* v_searcher_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_326_; 
v_currPos_282_ = lean_ctor_get(v_a_280_, 0);
v_searcher_283_ = lean_ctor_get(v_a_280_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_a_280_);
if (v_isSharedCheck_326_ == 0)
{
v___x_285_ = v_a_280_;
v_isShared_286_ = v_isSharedCheck_326_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_searcher_283_);
lean_inc(v_currPos_282_);
lean_dec(v_a_280_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_326_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_str_287_; lean_object* v_startInclusive_288_; lean_object* v_endExclusive_289_; uint8_t v___x_290_; lean_object* v_it_292_; lean_object* v_startInclusive_293_; lean_object* v_endExclusive_294_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_str_287_ = lean_ctor_get(v___x_278_, 0);
v_startInclusive_288_ = lean_ctor_get(v___x_278_, 1);
v_endExclusive_289_ = lean_ctor_get(v___x_278_, 2);
v___x_290_ = 1;
v___x_304_ = lean_nat_sub(v_endExclusive_289_, v_startInclusive_288_);
v___x_305_ = lean_nat_dec_eq(v_searcher_283_, v___x_304_);
lean_dec(v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; uint32_t v___x_307_; uint32_t v___x_308_; uint8_t v___x_309_; 
v___x_306_ = lean_nat_add(v_startInclusive_288_, v_searcher_283_);
v___x_307_ = lean_string_utf8_get_fast(v_str_287_, v___x_306_);
v___x_308_ = 44;
v___x_309_ = lean_uint32_dec_eq(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec(v_searcher_283_);
v___x_310_ = lean_string_utf8_next_fast(v_str_287_, v___x_306_);
lean_dec(v___x_306_);
v___x_311_ = lean_nat_sub(v___x_310_, v_startInclusive_288_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_311_);
v___x_313_ = v___x_285_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_currPos_282_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_315_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
v_a_280_ = v___x_313_;
goto _start;
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_slice_319_; lean_object* v_nextIt_321_; 
v___x_316_ = lean_string_utf8_next_fast(v_str_287_, v___x_306_);
v___x_317_ = lean_nat_sub(v___x_316_, v___x_306_);
lean_dec(v___x_306_);
v___x_318_ = lean_nat_add(v_searcher_283_, v___x_317_);
lean_dec(v___x_317_);
v_slice_319_ = l_String_Slice_subslice_x21(v___x_278_, v_currPos_282_, v_searcher_283_);
lean_inc(v___x_318_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 1, v___x_318_);
lean_ctor_set(v___x_285_, 0, v___x_318_);
v_nextIt_321_ = v___x_285_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_318_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_318_);
v_nextIt_321_ = v_reuseFailAlloc_324_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v_startInclusive_322_; lean_object* v_endExclusive_323_; 
v_startInclusive_322_ = lean_ctor_get(v_slice_319_, 0);
lean_inc(v_startInclusive_322_);
v_endExclusive_323_ = lean_ctor_get(v_slice_319_, 1);
lean_inc(v_endExclusive_323_);
lean_dec_ref(v_slice_319_);
v_it_292_ = v_nextIt_321_;
v_startInclusive_293_ = v_startInclusive_322_;
v_endExclusive_294_ = v_endExclusive_323_;
goto v___jp_291_;
}
}
}
else
{
lean_object* v___x_325_; 
lean_del_object(v___x_285_);
lean_dec(v_searcher_283_);
v___x_325_ = lean_box(1);
lean_inc(v___x_279_);
v_it_292_ = v___x_325_;
v_startInclusive_293_ = v_currPos_282_;
v_endExclusive_294_ = v___x_279_;
goto v___jp_291_;
}
v___jp_291_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v_startInclusive_297_; lean_object* v_endExclusive_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
lean_inc_ref(v___x_277_);
v___x_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_277_);
lean_ctor_set(v___x_295_, 1, v_startInclusive_293_);
lean_ctor_set(v___x_295_, 2, v_endExclusive_294_);
v___x_296_ = l_String_Slice_trimAscii(v___x_295_);
v_startInclusive_297_ = lean_ctor_get(v___x_296_, 1);
lean_inc(v_startInclusive_297_);
v_endExclusive_298_ = lean_ctor_get(v___x_296_, 2);
lean_inc(v_endExclusive_298_);
lean_dec_ref(v___x_296_);
v___x_299_ = lean_nat_sub(v_endExclusive_298_, v_startInclusive_297_);
lean_dec(v_startInclusive_297_);
lean_dec(v_endExclusive_298_);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_nat_dec_eq(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
if (v___x_301_ == 0)
{
v_a_280_ = v_it_292_;
v_b_281_ = v___x_290_;
goto _start;
}
else
{
uint8_t v___x_303_; 
lean_dec(v_it_292_);
lean_dec(v___x_279_);
lean_dec_ref(v___x_277_);
v___x_303_ = 0;
return v___x_303_;
}
}
}
}
else
{
lean_dec(v___x_279_);
lean_dec_ref(v___x_277_);
return v_b_281_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object* v___x_327_, lean_object* v___x_328_, lean_object* v___x_329_, lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
uint8_t v_b_boxed_332_; uint8_t v_res_333_; lean_object* v_r_334_; 
v_b_boxed_332_ = lean_unbox(v_b_331_);
v_res_333_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_327_, v___x_328_, v___x_329_, v_a_330_, v_b_boxed_332_);
lean_dec_ref(v___x_328_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object* v___x_335_, lean_object* v___x_336_, lean_object* v___x_337_, lean_object* v_a_338_, uint8_t v_b_339_){
_start:
{
if (lean_obj_tag(v_a_338_) == 0)
{
lean_object* v_currPos_340_; lean_object* v_searcher_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_384_; 
v_currPos_340_ = lean_ctor_get(v_a_338_, 0);
v_searcher_341_ = lean_ctor_get(v_a_338_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_a_338_);
if (v_isSharedCheck_384_ == 0)
{
v___x_343_ = v_a_338_;
v_isShared_344_ = v_isSharedCheck_384_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_searcher_341_);
lean_inc(v_currPos_340_);
lean_dec(v_a_338_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_384_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_str_345_; lean_object* v_startInclusive_346_; lean_object* v_endExclusive_347_; uint8_t v___x_348_; lean_object* v_it_350_; lean_object* v_startInclusive_351_; lean_object* v_endExclusive_352_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_str_345_ = lean_ctor_get(v___x_336_, 0);
v_startInclusive_346_ = lean_ctor_get(v___x_336_, 1);
v_endExclusive_347_ = lean_ctor_get(v___x_336_, 2);
v___x_348_ = 1;
v___x_362_ = lean_nat_sub(v_endExclusive_347_, v_startInclusive_346_);
v___x_363_ = lean_nat_dec_eq(v_searcher_341_, v___x_362_);
lean_dec(v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; uint32_t v___x_365_; uint32_t v___x_366_; uint8_t v___x_367_; 
v___x_364_ = lean_nat_add(v_startInclusive_346_, v_searcher_341_);
v___x_365_ = lean_string_utf8_get_fast(v_str_345_, v___x_364_);
v___x_366_ = 44;
v___x_367_ = lean_uint32_dec_eq(v___x_365_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec(v_searcher_341_);
v___x_368_ = lean_string_utf8_next_fast(v_str_345_, v___x_364_);
lean_dec(v___x_364_);
v___x_369_ = lean_nat_sub(v___x_368_, v_startInclusive_346_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v___x_369_);
v___x_371_ = v___x_343_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_currPos_340_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_369_);
v___x_371_ = v_reuseFailAlloc_373_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
uint8_t v___x_372_; 
v___x_372_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_335_, v___x_336_, v___x_337_, v___x_371_, v_b_339_);
return v___x_372_;
}
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_slice_377_; lean_object* v_nextIt_379_; 
v___x_374_ = lean_string_utf8_next_fast(v_str_345_, v___x_364_);
v___x_375_ = lean_nat_sub(v___x_374_, v___x_364_);
lean_dec(v___x_364_);
v___x_376_ = lean_nat_add(v_searcher_341_, v___x_375_);
lean_dec(v___x_375_);
v_slice_377_ = l_String_Slice_subslice_x21(v___x_336_, v_currPos_340_, v_searcher_341_);
lean_inc(v___x_376_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v___x_376_);
lean_ctor_set(v___x_343_, 0, v___x_376_);
v_nextIt_379_ = v___x_343_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_376_);
v_nextIt_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v_startInclusive_380_; lean_object* v_endExclusive_381_; 
v_startInclusive_380_ = lean_ctor_get(v_slice_377_, 0);
lean_inc(v_startInclusive_380_);
v_endExclusive_381_ = lean_ctor_get(v_slice_377_, 1);
lean_inc(v_endExclusive_381_);
lean_dec_ref(v_slice_377_);
v_it_350_ = v_nextIt_379_;
v_startInclusive_351_ = v_startInclusive_380_;
v_endExclusive_352_ = v_endExclusive_381_;
goto v___jp_349_;
}
}
}
else
{
lean_object* v___x_383_; 
lean_del_object(v___x_343_);
lean_dec(v_searcher_341_);
v___x_383_ = lean_box(1);
lean_inc(v___x_337_);
v_it_350_ = v___x_383_;
v_startInclusive_351_ = v_currPos_340_;
v_endExclusive_352_ = v___x_337_;
goto v___jp_349_;
}
v___jp_349_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_startInclusive_355_; lean_object* v_endExclusive_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
lean_inc_ref(v___x_335_);
v___x_353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_353_, 0, v___x_335_);
lean_ctor_set(v___x_353_, 1, v_startInclusive_351_);
lean_ctor_set(v___x_353_, 2, v_endExclusive_352_);
v___x_354_ = l_String_Slice_trimAscii(v___x_353_);
v_startInclusive_355_ = lean_ctor_get(v___x_354_, 1);
lean_inc(v_startInclusive_355_);
v_endExclusive_356_ = lean_ctor_get(v___x_354_, 2);
lean_inc(v_endExclusive_356_);
lean_dec_ref(v___x_354_);
v___x_357_ = lean_nat_sub(v_endExclusive_356_, v_startInclusive_355_);
lean_dec(v_startInclusive_355_);
lean_dec(v_endExclusive_356_);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_nat_dec_eq(v___x_357_, v___x_358_);
lean_dec(v___x_357_);
if (v___x_359_ == 0)
{
uint8_t v___x_360_; 
v___x_360_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_335_, v___x_336_, v___x_337_, v_it_350_, v___x_348_);
return v___x_360_;
}
else
{
uint8_t v___x_361_; 
lean_dec(v_it_350_);
lean_dec(v___x_337_);
lean_dec_ref(v___x_335_);
v___x_361_ = 0;
return v___x_361_;
}
}
}
}
else
{
lean_dec(v___x_337_);
lean_dec_ref(v___x_335_);
return v_b_339_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v___x_387_, lean_object* v_a_388_, lean_object* v_b_389_){
_start:
{
uint8_t v_b_boxed_390_; uint8_t v_res_391_; lean_object* v_r_392_; 
v_b_boxed_390_ = lean_unbox(v_b_389_);
v_res_391_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_385_, v___x_386_, v___x_387_, v_a_388_, v_b_boxed_390_);
lean_dec_ref(v___x_386_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object* v_v_395_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_parts_399_; uint8_t v___x_400_; uint8_t v___x_401_; 
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = lean_string_utf8_byte_size(v_v_395_);
lean_inc_ref_n(v_v_395_, 2);
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v_v_395_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set(v___x_398_, 2, v___x_397_);
v_parts_399_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v___x_398_);
v___x_400_ = 1;
lean_inc(v_parts_399_);
v___x_401_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_395_, v___x_398_, v___x_397_, v_parts_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
lean_dec(v_parts_399_);
lean_dec_ref(v___x_398_);
lean_dec_ref(v_v_395_);
v___x_402_ = lean_box(0);
return v___x_402_;
}
else
{
lean_object* v___x_403_; lean_object* v___x_404_; size_t v_sz_405_; size_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_403_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0));
v___x_404_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v_v_395_, v___x_398_, v___x_397_, v_parts_399_, v___x_403_);
lean_dec_ref(v___x_398_);
v_sz_405_ = lean_array_size(v___x_404_);
v___x_406_ = ((size_t)0ULL);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_405_, v___x_406_, v___x_404_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v_inst_412_, lean_object* v_R_413_, lean_object* v_a_414_, uint8_t v_b_415_, lean_object* v_c_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_409_, v___x_410_, v___x_411_, v_a_414_, v_b_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v_inst_421_, lean_object* v_R_422_, lean_object* v_a_423_, lean_object* v_b_424_, lean_object* v_c_425_){
_start:
{
uint8_t v_b_boxed_426_; uint8_t v_res_427_; lean_object* v_r_428_; 
v_b_boxed_426_ = lean_unbox(v_b_424_);
v_res_427_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_418_, v___x_419_, v___x_420_, v_inst_421_, v_R_422_, v_a_423_, v_b_boxed_426_, v_c_425_);
lean_dec_ref(v___x_419_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v___x_431_, lean_object* v_inst_432_, lean_object* v_R_433_, lean_object* v_a_434_, lean_object* v_b_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_429_, v___x_430_, v___x_431_, v_a_434_, v_b_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v_inst_440_, lean_object* v_R_441_, lean_object* v_a_442_, lean_object* v_b_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_437_, v___x_438_, v___x_439_, v_inst_440_, v_R_441_, v_a_442_, v_b_443_);
lean_dec_ref(v___x_438_);
return v_res_444_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object* v___x_445_, lean_object* v___x_446_, lean_object* v___x_447_, lean_object* v_inst_448_, lean_object* v_R_449_, lean_object* v_a_450_, uint8_t v_b_451_, lean_object* v_c_452_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_445_, v___x_446_, v___x_447_, v_a_450_, v_b_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object* v___x_454_, lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v_inst_457_, lean_object* v_R_458_, lean_object* v_a_459_, lean_object* v_b_460_, lean_object* v_c_461_){
_start:
{
uint8_t v_b_boxed_462_; uint8_t v_res_463_; lean_object* v_r_464_; 
v_b_boxed_462_ = lean_unbox(v_b_460_);
v_res_463_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_454_, v___x_455_, v___x_456_, v_inst_457_, v_R_458_, v_a_459_, v_b_boxed_462_, v_c_461_);
lean_dec_ref(v___x_455_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v___x_467_, lean_object* v_inst_468_, lean_object* v_R_469_, lean_object* v_a_470_, lean_object* v_b_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_465_, v___x_466_, v___x_467_, v_a_470_, v_b_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object* v___x_473_, lean_object* v___x_474_, lean_object* v___x_475_, lean_object* v_inst_476_, lean_object* v_R_477_, lean_object* v_a_478_, lean_object* v_b_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(v___x_473_, v___x_474_, v___x_475_, v_inst_476_, v_R_477_, v_a_478_, v_b_479_);
lean_dec_ref(v___x_474_);
return v_res_480_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqContentLength_beq(lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_nat_dec_eq(v_x_481_, v_x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqContentLength_beq___boxed(lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
uint8_t v_res_486_; lean_object* v_r_487_; 
v_res_486_ = l_Std_Http_Header_instBEqContentLength_beq(v_x_484_, v_x_485_);
lean_dec(v_x_485_);
lean_dec(v_x_484_);
v_r_487_ = lean_box(v_res_486_);
return v_r_487_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprContentLength_repr_spec__0(lean_object* v_a_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = lean_nat_to_int(v_a_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(10u);
v___x_506_ = lean_nat_to_int(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0));
v___x_509_ = lean_string_length(v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9);
v___x_511_ = lean_nat_to_int(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg(lean_object* v_x_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_517_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6));
v___x_518_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_519_ = l_Nat_reprFast(v_x_516_);
v___x_520_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
v___x_521_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_518_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = 0;
v___x_523_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*1, v___x_522_);
v___x_524_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_517_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_526_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_524_);
v___x_528_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_529_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_525_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set_uint8(v___x_531_, sizeof(void*)*1, v___x_522_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr(lean_object* v_x_532_, lean_object* v_prec_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_Http_Header_instReprContentLength_repr___redArg(v_x_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___boxed(lean_object* v_x_535_, lean_object* v_prec_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_Http_Header_instReprContentLength_repr(v_x_535_, v_prec_536_);
lean_dec(v_prec_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_parse(lean_object* v_v_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_string_utf8_byte_size(v_v_540_);
v___x_543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_543_, 0, v_v_540_);
lean_ctor_set(v___x_543_, 1, v___x_541_);
lean_ctor_set(v___x_543_, 2, v___x_542_);
v___x_544_ = l_String_Slice_toNat_x3f(v___x_543_);
lean_dec_ref(v___x_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_545_; 
v___x_545_ = lean_box(0);
return v___x_545_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_val_546_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_544_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_val_546_);
lean_dec(v___x_544_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_val_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_serialize(lean_object* v_h_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_555_ = l_Std_Http_Header_Name_contentLength;
v___x_556_ = l_Nat_reprFast(v_h_554_);
v___x_557_ = l_Std_Http_Header_Value_ofString_x21(v___x_556_);
v___x_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_555_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
if (lean_obj_tag(v_x_566_) == 0)
{
uint8_t v___x_567_; 
v___x_567_ = 1;
return v___x_567_;
}
else
{
uint8_t v___x_568_; 
v___x_568_ = 0;
return v___x_568_;
}
}
else
{
if (lean_obj_tag(v_x_566_) == 0)
{
uint8_t v___x_569_; 
v___x_569_ = 0;
return v___x_569_;
}
else
{
lean_object* v_val_570_; lean_object* v_val_571_; uint8_t v___x_572_; 
v_val_570_ = lean_ctor_get(v_x_565_, 0);
v_val_571_ = lean_ctor_get(v_x_566_, 0);
v___x_572_ = lean_string_dec_eq(v_val_570_, v_val_571_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
uint8_t v_res_575_; lean_object* v_r_576_; 
v_res_575_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_573_, v_x_574_);
lean_dec(v_x_574_);
lean_dec(v_x_573_);
v_r_576_ = lean_box(v_res_575_);
return v_r_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object* v_as_578_, size_t v_i_579_, size_t v_stop_580_, lean_object* v_b_581_){
_start:
{
lean_object* v___y_583_; uint8_t v___x_587_; 
v___x_587_ = lean_usize_dec_eq(v_i_579_, v_stop_580_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_array_uget_borrowed(v_as_578_, v_i_579_);
v___x_589_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_590_ = lean_string_dec_eq(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
v___y_583_ = v_b_581_;
goto v___jp_582_;
}
else
{
lean_object* v___x_591_; 
lean_inc(v___x_588_);
v___x_591_ = lean_array_push(v_b_581_, v___x_588_);
v___y_583_ = v___x_591_;
goto v___jp_582_;
}
}
else
{
return v_b_581_;
}
v___jp_582_:
{
size_t v___x_584_; size_t v___x_585_; 
v___x_584_ = ((size_t)1ULL);
v___x_585_ = lean_usize_add(v_i_579_, v___x_584_);
v_i_579_ = v___x_585_;
v_b_581_ = v___y_583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object* v_as_592_, lean_object* v_i_593_, lean_object* v_stop_594_, lean_object* v_b_595_){
_start:
{
size_t v_i_boxed_596_; size_t v_stop_boxed_597_; lean_object* v_res_598_; 
v_i_boxed_596_ = lean_unbox_usize(v_i_593_);
lean_dec(v_i_593_);
v_stop_boxed_597_ = lean_unbox_usize(v_stop_594_);
lean_dec(v_stop_594_);
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_592_, v_i_boxed_596_, v_stop_boxed_597_, v_b_595_);
lean_dec_ref(v_as_592_);
return v_res_598_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object* v___x_599_, lean_object* v_as_600_, size_t v_i_601_, size_t v_stop_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = lean_usize_dec_eq(v_i_601_, v_stop_602_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_604_ = 1;
v___x_605_ = lean_array_uget_borrowed(v_as_600_, v_i_601_);
lean_inc(v___x_605_);
v___x_606_ = l_Std_Http_Internal_isToken(v___x_605_);
if (v___x_606_ == 0)
{
return v___x_604_;
}
else
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_nat_dec_eq(v___x_599_, v___x_607_);
if (v___x_608_ == 0)
{
size_t v___x_609_; size_t v___x_610_; 
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_add(v_i_601_, v___x_609_);
v_i_601_ = v___x_610_;
goto _start;
}
else
{
return v___x_604_;
}
}
}
else
{
uint8_t v___x_612_; 
v___x_612_ = 0;
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object* v___x_613_, lean_object* v_as_614_, lean_object* v_i_615_, lean_object* v_stop_616_){
_start:
{
size_t v_i_boxed_617_; size_t v_stop_boxed_618_; uint8_t v_res_619_; lean_object* v_r_620_; 
v_i_boxed_617_ = lean_unbox_usize(v_i_615_);
lean_dec(v_i_615_);
v_stop_boxed_618_ = lean_unbox_usize(v_stop_616_);
lean_dec(v_stop_616_);
v_res_619_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_613_, v_as_614_, v_i_boxed_617_, v_stop_boxed_618_);
lean_dec_ref(v_as_614_);
lean_dec(v___x_613_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object* v_codings_625_){
_start:
{
uint8_t v___y_627_; uint8_t v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; uint8_t v___y_637_; uint8_t v___y_638_; lean_object* v___y_639_; uint8_t v___y_649_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_array_get_size(v_codings_625_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_nat_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
uint8_t v___x_666_; 
v___x_666_ = lean_nat_dec_lt(v___x_664_, v___x_663_);
if (v___x_666_ == 0)
{
v___y_649_ = v___x_665_;
goto v___jp_648_;
}
else
{
if (v___x_666_ == 0)
{
v___y_649_ = v___x_665_;
goto v___jp_648_;
}
else
{
size_t v___x_667_; size_t v___x_668_; uint8_t v___x_669_; 
v___x_667_ = ((size_t)0ULL);
v___x_668_ = lean_usize_of_nat(v___x_663_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_663_, v_codings_625_, v___x_667_, v___x_668_);
v___y_649_ = v___x_669_;
goto v___jp_648_;
}
}
}
else
{
v___y_649_ = v___x_665_;
goto v___jp_648_;
}
v___jp_626_:
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_dec_lt(v___x_631_, v___y_629_);
if (v___x_632_ == 0)
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_eq(v___y_629_, v___x_631_);
lean_dec(v___y_629_);
if (v___x_633_ == 0)
{
lean_dec(v___y_630_);
if (v___x_633_ == 0)
{
return v___y_628_;
}
else
{
return v___y_627_;
}
}
else
{
lean_object* v___x_634_; uint8_t v_lastIsChunked_635_; 
v___x_634_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v_lastIsChunked_635_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_630_, v___x_634_);
lean_dec(v___y_630_);
if (v_lastIsChunked_635_ == 0)
{
if (v___x_633_ == 0)
{
return v___y_628_;
}
else
{
return v___y_627_;
}
}
else
{
return v___y_628_;
}
}
}
else
{
lean_dec(v___y_630_);
lean_dec(v___y_629_);
return v___y_627_;
}
}
v___jp_636_:
{
lean_object* v_chunkedCount_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_chunkedCount_640_ = lean_array_get_size(v___y_639_);
lean_dec_ref(v___y_639_);
v___x_641_ = lean_array_get_size(v_codings_625_);
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = lean_nat_sub(v___x_641_, v___x_642_);
v___x_644_ = lean_nat_dec_lt(v___x_643_, v___x_641_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v___x_643_);
v___x_645_ = lean_box(0);
v___y_627_ = v___y_637_;
v___y_628_ = v___y_638_;
v___y_629_ = v_chunkedCount_640_;
v___y_630_ = v___x_645_;
goto v___jp_626_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_array_fget_borrowed(v_codings_625_, v___x_643_);
lean_dec(v___x_643_);
lean_inc(v___x_646_);
v___x_647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
v___y_627_ = v___y_637_;
v___y_628_ = v___y_638_;
v___y_629_ = v_chunkedCount_640_;
v___y_630_ = v___x_647_;
goto v___jp_626_;
}
}
v___jp_648_:
{
if (v___y_649_ == 0)
{
uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_650_ = 1;
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_array_get_size(v_codings_625_);
v___x_653_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__1));
v___x_654_ = lean_nat_dec_lt(v___x_651_, v___x_652_);
if (v___x_654_ == 0)
{
v___y_637_ = v___y_649_;
v___y_638_ = v___x_650_;
v___y_639_ = v___x_653_;
goto v___jp_636_;
}
else
{
uint8_t v___x_655_; 
v___x_655_ = lean_nat_dec_le(v___x_652_, v___x_652_);
if (v___x_655_ == 0)
{
if (v___x_654_ == 0)
{
v___y_637_ = v___y_649_;
v___y_638_ = v___x_650_;
v___y_639_ = v___x_653_;
goto v___jp_636_;
}
else
{
size_t v___x_656_; size_t v___x_657_; lean_object* v___x_658_; 
v___x_656_ = ((size_t)0ULL);
v___x_657_ = lean_usize_of_nat(v___x_652_);
v___x_658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_625_, v___x_656_, v___x_657_, v___x_653_);
v___y_637_ = v___y_649_;
v___y_638_ = v___x_650_;
v___y_639_ = v___x_658_;
goto v___jp_636_;
}
}
else
{
size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; 
v___x_659_ = ((size_t)0ULL);
v___x_660_ = lean_usize_of_nat(v___x_652_);
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_625_, v___x_659_, v___x_660_, v___x_653_);
v___y_637_ = v___y_649_;
v___y_638_ = v___x_650_;
v___y_639_ = v___x_661_;
goto v___jp_636_;
}
}
}
else
{
uint8_t v___x_662_; 
v___x_662_ = 0;
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_Validate___boxed(lean_object* v_codings_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_670_);
lean_dec_ref(v_codings_670_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(lean_object* v___y_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = l_String_quote(v___y_673_);
v___x_675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_678_) == 0)
{
lean_dec(v_x_676_);
return v_x_677_;
}
else
{
lean_object* v_head_679_; lean_object* v_tail_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_691_; 
v_head_679_ = lean_ctor_get(v_x_678_, 0);
v_tail_680_ = lean_ctor_get(v_x_678_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_x_678_);
if (v_isSharedCheck_691_ == 0)
{
v___x_682_ = v_x_678_;
v_isShared_683_ = v_isSharedCheck_691_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_tail_680_);
lean_inc(v_head_679_);
lean_dec(v_x_678_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_691_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
lean_inc(v_x_676_);
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 5);
lean_ctor_set(v___x_682_, 1, v_x_676_);
lean_ctor_set(v___x_682_, 0, v_x_677_);
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_x_677_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_x_676_);
v___x_685_ = v_reuseFailAlloc_690_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = l_String_quote(v_head_679_);
v___x_687_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___x_688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_685_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v_x_677_ = v___x_688_;
v_x_678_ = v_tail_680_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
if (lean_obj_tag(v_x_694_) == 0)
{
lean_dec(v_x_692_);
return v_x_693_;
}
else
{
lean_object* v_head_695_; lean_object* v_tail_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_707_; 
v_head_695_ = lean_ctor_get(v_x_694_, 0);
v_tail_696_ = lean_ctor_get(v_x_694_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_707_ == 0)
{
v___x_698_ = v_x_694_;
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_tail_696_);
lean_inc(v_head_695_);
lean_dec(v_x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
lean_inc(v_x_692_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 5);
lean_ctor_set(v___x_698_, 1, v_x_692_);
lean_ctor_set(v___x_698_, 0, v_x_693_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_x_693_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_x_692_);
v___x_701_ = v_reuseFailAlloc_706_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = l_String_quote(v_head_695_);
v___x_703_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_701_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(v_x_692_, v___x_704_, v_tail_696_);
return v___x_705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_708_) == 0)
{
lean_object* v___x_710_; 
lean_dec(v_x_709_);
v___x_710_ = lean_box(0);
return v___x_710_;
}
else
{
lean_object* v_tail_711_; 
v_tail_711_ = lean_ctor_get(v_x_708_, 1);
if (lean_obj_tag(v_tail_711_) == 0)
{
lean_object* v_head_712_; lean_object* v___x_713_; 
lean_dec(v_x_709_);
v_head_712_ = lean_ctor_get(v_x_708_, 0);
lean_inc(v_head_712_);
lean_dec_ref(v_x_708_);
v___x_713_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_712_);
return v___x_713_;
}
else
{
lean_object* v_head_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_inc(v_tail_711_);
v_head_714_ = lean_ctor_get(v_x_708_, 0);
lean_inc(v_head_714_);
lean_dec_ref(v_x_708_);
v___x_715_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_714_);
v___x_716_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(v_x_709_, v___x_715_, v_tail_711_);
return v___x_716_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0));
v___x_726_ = lean_string_length(v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5);
v___x_728_ = lean_nat_to_int(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(lean_object* v_xs_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_737_ = lean_array_get_size(v_xs_736_);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_nat_dec_eq(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_740_ = lean_array_to_list(v_xs_736_);
v___x_741_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3));
v___x_742_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(v___x_740_, v___x_741_);
v___x_743_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6);
v___x_744_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7));
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_744_);
lean_ctor_set(v___x_745_, 1, v___x_742_);
v___x_746_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8));
v___x_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_743_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_Std_Format_fill(v___x_748_);
return v___x_749_;
}
else
{
lean_object* v___x_750_; 
lean_dec_ref(v_xs_736_);
v___x_750_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10));
return v___x_750_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_unsigned_to_nat(11u);
v___x_761_ = lean_nat_to_int(v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg(lean_object* v_x_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_769_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_770_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3));
v___x_771_ = lean_obj_once(&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4, &l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4);
v___x_772_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_768_);
v___x_773_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = 0;
v___x_775_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*1, v___x_774_);
v___x_776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_770_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_778_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_box(1);
v___x_780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6));
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v___x_769_);
v___x_784_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_787_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_785_);
v___x_789_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_790_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_788_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_786_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set_uint8(v___x_792_, sizeof(void*)*1, v___x_774_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr(lean_object* v_x_793_, lean_object* v_prec_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg(v_x_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___boxed(lean_object* v_x_796_, lean_object* v_prec_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_Http_Header_instReprTransferEncoding_repr(v_x_796_, v_prec_797_);
lean_dec(v_prec_797_);
return v_res_798_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object* v_te_801_){
_start:
{
lean_object* v___y_803_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_806_ = lean_array_get_size(v_te_801_);
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_sub(v___x_806_, v___x_807_);
v___x_809_ = lean_nat_dec_lt(v___x_808_, v___x_806_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec(v___x_808_);
v___x_810_ = lean_box(0);
v___y_803_ = v___x_810_;
goto v___jp_802_;
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_array_fget_borrowed(v_te_801_, v___x_808_);
lean_dec(v___x_808_);
lean_inc(v___x_811_);
v___x_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___y_803_ = v___x_812_;
goto v___jp_802_;
}
v___jp_802_:
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v___x_805_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_803_, v___x_804_);
lean_dec(v___y_803_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_isChunked___boxed(lean_object* v_te_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_813_);
lean_dec_ref(v_te_813_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object* v_v_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v___x_818_; 
v___x_818_ = lean_box(0);
return v___x_818_;
}
else
{
lean_object* v_val_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_828_; 
v_val_819_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_828_ == 0)
{
v___x_821_ = v___x_817_;
v_isShared_822_ = v_isSharedCheck_828_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_val_819_);
lean_dec(v___x_817_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_828_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___x_823_; 
v___x_823_ = l_Std_Http_Header_TransferEncoding_Validate(v_val_819_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; 
lean_del_object(v___x_821_);
lean_dec(v_val_819_);
v___x_824_ = lean_box(0);
return v___x_824_;
}
else
{
lean_object* v___x_826_; 
if (v_isShared_822_ == 0)
{
v___x_826_ = v___x_821_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_val_819_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_serialize(lean_object* v_te_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v_value_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_830_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_831_ = lean_array_to_list(v_te_829_);
v_value_832_ = l_String_intercalate(v___x_830_, v___x_831_);
v___x_833_ = l_Std_Http_Header_Name_transferEncoding;
v___x_834_ = l_Std_Http_Header_Value_ofString_x21(v_value_832_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_833_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___redArg(lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_855_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_856_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__3));
v___x_857_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_858_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_854_);
v___x_859_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
v___x_860_ = 0;
v___x_861_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_861_, 0, v___x_859_);
lean_ctor_set_uint8(v___x_861_, sizeof(void*)*1, v___x_860_);
v___x_862_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_856_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_864_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_box(1);
v___x_866_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
v___x_867_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__5));
v___x_868_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_866_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
v___x_869_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_855_);
v___x_870_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_871_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_873_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_874_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_873_);
lean_ctor_set(v___x_874_, 1, v___x_871_);
v___x_875_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_876_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_877_, 0, v___x_872_);
lean_ctor_set(v___x_877_, 1, v___x_876_);
v___x_878_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set_uint8(v___x_878_, sizeof(void*)*1, v___x_860_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr(lean_object* v_x_879_, lean_object* v_prec_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_Http_Header_instReprConnection_repr___redArg(v_x_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___boxed(lean_object* v_x_882_, lean_object* v_prec_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_Http_Header_instReprConnection_repr(v_x_882_, v_prec_883_);
lean_dec(v_prec_883_);
return v_res_884_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(lean_object* v_token_887_, lean_object* v_as_888_, size_t v_i_889_, size_t v_stop_890_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = lean_usize_dec_eq(v_i_889_, v_stop_890_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_array_uget_borrowed(v_as_888_, v_i_889_);
v___x_893_ = lean_string_dec_eq(v___x_892_, v_token_887_);
if (v___x_893_ == 0)
{
size_t v___x_894_; size_t v___x_895_; 
v___x_894_ = ((size_t)1ULL);
v___x_895_ = lean_usize_add(v_i_889_, v___x_894_);
v_i_889_ = v___x_895_;
goto _start;
}
else
{
return v___x_893_;
}
}
else
{
uint8_t v___x_897_; 
v___x_897_ = 0;
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(lean_object* v_token_898_, lean_object* v_as_899_, lean_object* v_i_900_, lean_object* v_stop_901_){
_start:
{
size_t v_i_boxed_902_; size_t v_stop_boxed_903_; uint8_t v_res_904_; lean_object* v_r_905_; 
v_i_boxed_902_ = lean_unbox_usize(v_i_900_);
lean_dec(v_i_900_);
v_stop_boxed_903_ = lean_unbox_usize(v_stop_901_);
lean_dec(v_stop_901_);
v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_898_, v_as_899_, v_i_boxed_902_, v_stop_boxed_903_);
lean_dec_ref(v_as_899_);
lean_dec_ref(v_token_898_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_containsToken(lean_object* v_connection_906_, lean_object* v_token_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = lean_array_get_size(v_connection_906_);
v___x_910_ = lean_nat_dec_lt(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_dec_ref(v_token_907_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; 
v___x_911_ = lean_string_utf8_byte_size(v_token_907_);
if (v___x_910_ == 0)
{
lean_dec_ref(v_token_907_);
return v___x_910_;
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v_token_915_; size_t v___x_916_; size_t v___x_917_; uint8_t v___x_918_; 
v___x_912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_912_, 0, v_token_907_);
lean_ctor_set(v___x_912_, 1, v___x_908_);
lean_ctor_set(v___x_912_, 2, v___x_911_);
v___x_913_ = l_String_Slice_trimAscii(v___x_912_);
v___x_914_ = l_String_Slice_toString(v___x_913_);
lean_dec_ref(v___x_913_);
v_token_915_ = l_String_mapAux___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_914_, v___x_908_);
v___x_916_ = ((size_t)0ULL);
v___x_917_ = lean_usize_of_nat(v___x_909_);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_915_, v_connection_906_, v___x_916_, v___x_917_);
lean_dec_ref(v_token_915_);
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_containsToken___boxed(lean_object* v_connection_919_, lean_object* v_token_920_){
_start:
{
uint8_t v_res_921_; lean_object* v_r_922_; 
v_res_921_ = l_Std_Http_Header_Connection_containsToken(v_connection_919_, v_token_920_);
lean_dec_ref(v_connection_919_);
v_r_922_ = lean_box(v_res_921_);
return v_r_922_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_shouldClose(lean_object* v_connection_924_){
_start:
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = ((lean_object*)(l_Std_Http_Header_Connection_shouldClose___closed__0));
v___x_926_ = l_Std_Http_Header_Connection_containsToken(v_connection_924_, v___x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_shouldClose___boxed(lean_object* v_connection_927_){
_start:
{
uint8_t v_res_928_; lean_object* v_r_929_; 
v_res_928_ = l_Std_Http_Header_Connection_shouldClose(v_connection_927_);
lean_dec_ref(v_connection_927_);
v_r_929_ = lean_box(v_res_928_);
return v_r_929_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(lean_object* v_as_930_, size_t v_i_931_, size_t v_stop_932_){
_start:
{
uint8_t v___x_933_; 
v___x_933_ = lean_usize_dec_eq(v_i_931_, v_stop_932_);
if (v___x_933_ == 0)
{
uint8_t v___x_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v___x_934_ = 1;
v___x_935_ = lean_array_uget_borrowed(v_as_930_, v_i_931_);
lean_inc(v___x_935_);
v___x_936_ = l_Std_Http_Internal_isToken(v___x_935_);
if (v___x_936_ == 0)
{
return v___x_934_;
}
else
{
if (v___x_933_ == 0)
{
size_t v___x_937_; size_t v___x_938_; 
v___x_937_ = ((size_t)1ULL);
v___x_938_ = lean_usize_add(v_i_931_, v___x_937_);
v_i_931_ = v___x_938_;
goto _start;
}
else
{
return v___x_934_;
}
}
}
else
{
uint8_t v___x_940_; 
v___x_940_ = 0;
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(lean_object* v_as_941_, lean_object* v_i_942_, lean_object* v_stop_943_){
_start:
{
size_t v_i_boxed_944_; size_t v_stop_boxed_945_; uint8_t v_res_946_; lean_object* v_r_947_; 
v_i_boxed_944_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_stop_boxed_945_ = lean_unbox_usize(v_stop_943_);
lean_dec(v_stop_943_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_941_, v_i_boxed_944_, v_stop_boxed_945_);
lean_dec_ref(v_as_941_);
v_r_947_ = lean_box(v_res_946_);
return v_r_947_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_parse(lean_object* v_v_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_948_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v___x_950_; 
v___x_950_ = lean_box(0);
return v___x_950_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_971_; 
v_val_951_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_971_ == 0)
{
v___x_953_ = v___x_949_;
v_isShared_954_ = v_isSharedCheck_971_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_dec(v___x_949_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_971_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_array_get_size(v_val_951_);
v___x_957_ = lean_nat_dec_lt(v___x_955_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_959_; 
if (v_isShared_954_ == 0)
{
v___x_959_ = v___x_953_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_val_951_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
if (v___x_957_ == 0)
{
lean_object* v___x_962_; 
if (v_isShared_954_ == 0)
{
v___x_962_ = v___x_953_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_val_951_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
else
{
size_t v___x_964_; size_t v___x_965_; uint8_t v___x_966_; 
v___x_964_ = ((size_t)0ULL);
v___x_965_ = lean_usize_of_nat(v___x_956_);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_val_951_, v___x_964_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_968_; 
if (v_isShared_954_ == 0)
{
v___x_968_ = v___x_953_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_val_951_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
lean_object* v___x_970_; 
lean_del_object(v___x_953_);
lean_dec(v_val_951_);
v___x_970_ = lean_box(0);
return v___x_970_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_serialize(lean_object* v_connection_972_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_value_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_973_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_974_ = lean_array_to_list(v_connection_972_);
v_value_975_ = l_String_intercalate(v___x_973_, v___x_974_);
v___x_976_ = l_Std_Http_Header_Name_connection;
v___x_977_ = l_Std_Http_Header_Value_ofString_x21(v_value_975_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
return v___x_978_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers_Name(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers_Value(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Internal_Http_Data_Headers_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Internal_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1 = _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1();
lean_mark_persistent(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Internal_Http_Data_Headers_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Internal_Http_Data_Headers_Name(uint8_t builtin);
lean_object* initialize_Std_Internal_Http_Data_Headers_Value(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Http_Data_Headers_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Http_Data_Headers_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Internal_Http_Data_Headers_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Internal_Http_Data_Headers_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

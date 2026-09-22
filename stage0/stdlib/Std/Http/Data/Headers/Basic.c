// Lean compiler output
// Module: Std.Http.Data.Headers.Basic
// Imports: public import Std.Http.Data.URI public import Std.Http.Data.Headers.Name public import Std.Http.Data.Headers.Value public import Std.Internal.Parsec.Basic import Init.Data.String.Search
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
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_Http_Internal_isToken(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_length(lean_object*);
extern lean_object* l_Std_Http_Header_Name_expect;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_Http_URI_instReprPort_repr(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
extern lean_object* l_Std_Http_Header_Name_contentLength;
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed(lean_object*);
lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object*, lean_object*);
uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0_value;
static const lean_string_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Std_Http_Header_instReprHost_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "host"};
static const lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Header_instReprHost_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__0_value)}};
static const lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_instReprHost_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__2 = (const lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Http_Header_instReprHost_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__2_value),((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5_value)}};
static const lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__3 = (const lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Http_Header_instReprHost_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__4;
static lean_once_cell_t l_Std_Http_Header_instReprHost_repr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__5;
static const lean_string_object l_Std_Http_Header_instReprHost_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Std.Http.URI.Host."};
static const lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__6 = (const lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__6_value;
static const lean_string_object l_Std_Http_Header_instReprHost_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "port"};
static const lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__7 = (const lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Http_Header_instReprHost_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__7_value)}};
static const lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__8 = (const lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__8_value;
static const lean_string_object l_Std_Http_Header_instReprHost_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__9 = (const lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__9_value;
static const lean_string_object l_Std_Http_Header_instReprHost_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ipv4"};
static const lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__10 = (const lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__10_value;
static const lean_string_object l_Std_Http_Header_instReprHost_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ipv6"};
static const lean_object* l_Std_Http_Header_instReprHost_repr___redArg___closed__11 = (const lean_object*)&l_Std_Http_Header_instReprHost_repr___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instReprHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instReprHost_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instReprHost___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprHost___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instReprHost = (const lean_object*)&l_Std_Http_Header_instReprHost___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqHost_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqHost_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instBEqHost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instBEqHost_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instBEqHost___closed__0 = (const lean_object*)&l_Std_Http_Header_instBEqHost___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instBEqHost = (const lean_object*)&l_Std_Http_Header_instBEqHost___closed__0_value;
static const lean_string_object l_Std_Http_Header_Host_parse___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "expected end of input"};
static const lean_object* l_Std_Http_Header_Host_parse___lam__0___closed__0 = (const lean_object*)&l_Std_Http_Header_Host_parse___lam__0___closed__0_value;
static const lean_ctor_object l_Std_Http_Header_Host_parse___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Http_Header_Host_parse___lam__0___closed__0_value)}};
static const lean_object* l_Std_Http_Header_Host_parse___lam__0___closed__1 = (const lean_object*)&l_Std_Http_Header_Host_parse___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Http_Header_Host_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(13) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(128) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1))}};
static const lean_object* l_Std_Http_Header_Host_parse___closed__0 = (const lean_object*)&l_Std_Http_Header_Host_parse___closed__0_value;
static const lean_closure_object l_Std_Http_Header_Host_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Host_parse___lam__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Header_Host_parse___closed__0_value)} };
static const lean_object* l_Std_Http_Header_Host_parse___closed__1 = (const lean_object*)&l_Std_Http_Header_Host_parse___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___boxed(lean_object*);
static const lean_string_object l_Std_Http_Header_Host_serialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_Header_Host_serialize___closed__0 = (const lean_object*)&l_Std_Http_Header_Host_serialize___closed__0_value;
static const lean_string_object l_Std_Http_Header_Host_serialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Header_Host_serialize___closed__1 = (const lean_object*)&l_Std_Http_Header_Host_serialize___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_serialize(lean_object*);
static const lean_closure_object l_Std_Http_Header_Host_inst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Host_parse___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Host_inst___closed__0 = (const lean_object*)&l_Std_Http_Header_Host_inst___closed__0_value;
static const lean_closure_object l_Std_Http_Header_Host_inst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Host_serialize, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Host_inst___closed__1 = (const lean_object*)&l_Std_Http_Header_Host_inst___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_Host_inst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Header_Host_inst___closed__0_value),((lean_object*)&l_Std_Http_Header_Host_inst___closed__1_value)}};
static const lean_object* l_Std_Http_Header_Host_inst___closed__2 = (const lean_object*)&l_Std_Http_Header_Host_inst___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Host_inst = (const lean_object*)&l_Std_Http_Header_Host_inst___closed__2_value;
static const lean_ctor_object l_Std_Http_Header_instReprExpect_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprExpect_repr___redArg___closed__0_value;
static const lean_ctor_object l_Std_Http_Header_instReprExpect_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprExpect_repr___redArg___closed__0_value),((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___closed__1 = (const lean_object*)&l_Std_Http_Header_instReprExpect_repr___redArg___closed__1_value;
static lean_once_cell_t l_Std_Http_Header_instReprExpect_repr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___closed__2;
static lean_once_cell_t l_Std_Http_Header_instReprExpect_repr___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_Header_instReprExpect_repr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprExpect_repr___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instReprExpect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instReprExpect_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instReprExpect___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprExpect___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instReprExpect = (const lean_object*)&l_Std_Http_Header_instReprExpect___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instBEqExpect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instBEqExpect_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instBEqExpect___closed__0 = (const lean_object*)&l_Std_Http_Header_instBEqExpect___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instBEqExpect = (const lean_object*)&l_Std_Http_Header_instBEqExpect___closed__0_value;
static const lean_string_object l_Std_Http_Header_Expect_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "100-continue"};
static const lean_object* l_Std_Http_Header_Expect_parse___closed__0 = (const lean_object*)&l_Std_Http_Header_Expect_parse___closed__0_value;
static const lean_ctor_object l_Std_Http_Header_Expect_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Header_Expect_parse___closed__1 = (const lean_object*)&l_Std_Http_Header_Expect_parse___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_parse(lean_object*);
static lean_once_cell_t l_Std_Http_Header_Expect_serialize___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Expect_serialize___redArg___closed__0;
static lean_once_cell_t l_Std_Http_Header_Expect_serialize___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Expect_serialize___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg();
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Http_Header_Expect_serialize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Expect_serialize___closed__0;
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize(lean_object*);
static const lean_closure_object l_Std_Http_Header_Expect_inst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Expect_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Expect_inst___closed__0 = (const lean_object*)&l_Std_Http_Header_Expect_inst___closed__0_value;
static const lean_closure_object l_Std_Http_Header_Expect_inst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Expect_serialize, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_Expect_inst___closed__1 = (const lean_object*)&l_Std_Http_Header_Expect_inst___closed__1_value;
static const lean_ctor_object l_Std_Http_Header_Expect_inst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Http_Header_Expect_inst___closed__0_value),((lean_object*)&l_Std_Http_Header_Expect_inst___closed__1_value)}};
static const lean_object* l_Std_Http_Header_Expect_inst___closed__2 = (const lean_object*)&l_Std_Http_Header_Expect_inst___closed__2_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_Expect_inst = (const lean_object*)&l_Std_Http_Header_Expect_inst___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v_fst_4_, lean_object* v___x_5_, uint32_t v___x_6_, lean_object* v___x_7_, lean_object* v_it_8_, lean_object* v_acc_9_, lean_object* v_hP_10_, lean_object* v_recur_11_){
_start:
{
lean_object* v_it_13_; lean_object* v_out_14_; lean_object* v___y_30_; uint32_t v___y_31_; lean_object* v___y_32_; uint8_t v___y_33_; lean_object* v_it_39_; lean_object* v_startInclusive_40_; lean_object* v_endExclusive_41_; 
if (lean_obj_tag(v_it_8_) == 0)
{
lean_object* v_currPos_48_; lean_object* v_searcher_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_71_; 
v_currPos_48_ = lean_ctor_get(v_it_8_, 0);
v_searcher_49_ = lean_ctor_get(v_it_8_, 1);
v_isSharedCheck_71_ = !lean_is_exclusive(v_it_8_);
if (v_isSharedCheck_71_ == 0)
{
v___x_51_ = v_it_8_;
v_isShared_52_ = v_isSharedCheck_71_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_searcher_49_);
lean_inc(v_currPos_48_);
lean_dec(v_it_8_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_71_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
uint8_t v_decide_53_; 
v_decide_53_ = lean_nat_dec_eq(v_searcher_49_, v___x_5_);
if (v_decide_53_ == 0)
{
uint32_t v___x_54_; uint8_t v___x_55_; 
lean_dec(v___x_5_);
v___x_54_ = lean_string_utf8_get_fast(v_fst_4_, v_searcher_49_);
v___x_55_ = lean_uint32_dec_eq(v___x_54_, v___x_6_);
if (v___x_55_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_56_ = lean_string_utf8_next_fast(v_fst_4_, v_searcher_49_);
lean_dec(v_searcher_49_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_56_);
v___x_58_ = v___x_51_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_currPos_48_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___x_56_);
v___x_58_ = v_reuseFailAlloc_60_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; 
v___x_59_ = lean_apply_4(v_recur_11_, v___x_58_, v_acc_9_, lean_box(0), lean_box(0));
return v___x_59_;
}
}
else
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v_slice_64_; lean_object* v_nextIt_66_; 
v___x_61_ = lean_string_utf8_next_fast(v_fst_4_, v_searcher_49_);
v___x_62_ = lean_nat_sub(v___x_61_, v_searcher_49_);
v___x_63_ = lean_nat_add(v_searcher_49_, v___x_62_);
lean_dec(v___x_62_);
v_slice_64_ = l_String_Slice_subslice_x21(v___x_7_, v_currPos_48_, v_searcher_49_);
lean_inc(v___x_63_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_63_);
lean_ctor_set(v___x_51_, 0, v___x_63_);
v_nextIt_66_ = v___x_51_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v___x_63_);
v_nextIt_66_ = v_reuseFailAlloc_69_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v_startInclusive_67_; lean_object* v_endExclusive_68_; 
v_startInclusive_67_ = lean_ctor_get(v_slice_64_, 0);
lean_inc(v_startInclusive_67_);
v_endExclusive_68_ = lean_ctor_get(v_slice_64_, 1);
lean_inc(v_endExclusive_68_);
lean_dec_ref(v_slice_64_);
v_it_39_ = v_nextIt_66_;
v_startInclusive_40_ = v_startInclusive_67_;
v_endExclusive_41_ = v_endExclusive_68_;
goto v___jp_38_;
}
}
}
else
{
lean_object* v___x_70_; 
lean_del_object(v___x_51_);
lean_dec(v_searcher_49_);
v___x_70_ = lean_box(1);
v_it_39_ = v___x_70_;
v_startInclusive_40_ = v_currPos_48_;
v_endExclusive_41_ = v___x_5_;
goto v___jp_38_;
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
v___x_21_ = lean_string_utf8_extract_fast(v___x_1_, v___x_2_, v___x_3_);
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
if (v___y_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = lean_string_utf8_set(v___y_30_, v___x_2_, v___y_31_);
v_it_13_ = v___y_32_;
v_out_14_ = v___x_34_;
goto v___jp_12_;
}
else
{
uint32_t v___x_35_; uint32_t v___x_36_; lean_object* v___x_37_; 
v___x_35_ = 4294967264;
v___x_36_ = lean_uint32_add(v___y_31_, v___x_35_);
v___x_37_ = lean_string_utf8_set(v___y_30_, v___x_2_, v___x_36_);
v_it_13_ = v___y_32_;
v_out_14_ = v___x_37_;
goto v___jp_12_;
}
}
v___jp_38_:
{
lean_object* v___x_42_; uint32_t v___x_43_; uint32_t v___x_44_; uint8_t v___x_45_; 
v___x_42_ = lean_string_utf8_extract_fast(v_fst_4_, v_startInclusive_40_, v_endExclusive_41_);
lean_dec(v_endExclusive_41_);
lean_dec(v_startInclusive_40_);
v___x_43_ = lean_string_utf8_get(v___x_42_, v___x_2_);
v___x_44_ = 97;
v___x_45_ = lean_uint32_dec_le(v___x_44_, v___x_43_);
if (v___x_45_ == 0)
{
v___y_30_ = v___x_42_;
v___y_31_ = v___x_43_;
v___y_32_ = v_it_39_;
v___y_33_ = v___x_45_;
goto v___jp_29_;
}
else
{
uint32_t v___x_46_; uint8_t v___x_47_; 
v___x_46_ = 122;
v___x_47_ = lean_uint32_dec_le(v___x_43_, v___x_46_);
v___y_30_ = v___x_42_;
v___y_31_ = v___x_43_;
v___y_32_ = v_it_39_;
v___y_33_ = v___x_47_;
goto v___jp_29_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed(lean_object* v___x_72_, lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v_fst_75_, lean_object* v___x_76_, lean_object* v___x_77_, lean_object* v___x_78_, lean_object* v_it_79_, lean_object* v_acc_80_, lean_object* v_hP_81_, lean_object* v_recur_82_){
_start:
{
uint32_t v___x_1423__boxed_83_; lean_object* v_res_84_; 
v___x_1423__boxed_83_ = lean_unbox_uint32(v___x_77_);
lean_dec(v___x_77_);
v_res_84_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(v___x_72_, v___x_73_, v___x_74_, v_fst_75_, v___x_76_, v___x_1423__boxed_83_, v___x_78_, v_it_79_, v_acc_80_, v_hP_81_, v_recur_82_);
lean_dec_ref(v___x_78_);
lean_dec_ref(v_fst_75_);
lean_dec(v___x_74_);
lean_dec(v___x_73_);
lean_dec_ref(v___x_72_);
return v_res_84_;
}
}
static lean_object* _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3));
v___x_90_ = lean_string_utf8_byte_size(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_92_; lean_object* v___x_93_; 
v___x_92_ = 45;
v___x_93_ = lean_box_uint32(v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1(lean_object* v_h_94_, lean_object* v_buffer_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_serialize_97_; lean_object* v___x_98_; lean_object* v_fst_99_; lean_object* v_snd_100_; lean_object* v___y_102_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v_it_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_serialize_97_ = lean_ctor_get(v_h_94_, 1);
lean_inc_ref(v_serialize_97_);
lean_dec_ref(v_h_94_);
v___x_98_ = lean_apply_1(v_serialize_97_, v_a_96_);
v_fst_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc_n(v_fst_99_, 2);
v_snd_100_ = lean_ctor_get(v___x_98_, 1);
lean_inc(v_snd_100_);
lean_dec_ref(v___x_98_);
v___f_121_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2));
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_string_utf8_byte_size(v_fst_99_);
v___x_124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_124_, 0, v_fst_99_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_123_);
lean_inc_ref(v___x_124_);
v_it_125_ = l_String_Slice_splitToSubslice___redArg(v___x_124_, v___f_121_);
v___x_126_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3));
v___x_127_ = lean_obj_once(&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4, &l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4_once, _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4);
v___x_128_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1;
v___f_129_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_129_, 0, v___x_126_);
lean_closure_set(v___f_129_, 1, v___x_122_);
lean_closure_set(v___f_129_, 2, v___x_127_);
lean_closure_set(v___f_129_, 3, v_fst_99_);
lean_closure_set(v___f_129_, 4, v___x_123_);
lean_closure_set(v___f_129_, 5, v___x_128_);
lean_closure_set(v___f_129_, 6, v___x_124_);
v___x_130_ = lean_box(0);
v___x_131_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_129_, v_it_125_, v___x_130_, lean_box(0));
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v___x_132_; 
v___x_132_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__5));
v___y_102_ = v___x_132_;
goto v___jp_101_;
}
else
{
lean_object* v_val_133_; 
v_val_133_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_val_133_);
lean_dec_ref_known(v___x_131_, 1);
v___y_102_ = v_val_133_;
goto v___jp_101_;
}
v___jp_101_:
{
lean_object* v_data_103_; lean_object* v_size_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_120_; 
v_data_103_ = lean_ctor_get(v_buffer_95_, 0);
v_size_104_ = lean_ctor_get(v_buffer_95_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_buffer_95_);
if (v_isSharedCheck_120_ == 0)
{
v___x_106_ = v_buffer_95_;
v_isShared_107_ = v_isSharedCheck_120_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_size_104_);
lean_inc(v_data_103_);
lean_dec(v_buffer_95_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_120_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_108_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0));
v___x_109_ = lean_string_append(v___y_102_, v___x_108_);
v___x_110_ = lean_string_append(v___x_109_, v_snd_100_);
lean_dec(v_snd_100_);
v___x_111_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1));
v___x_112_ = lean_string_append(v___x_110_, v___x_111_);
v___x_113_ = lean_string_to_utf8(v___x_112_);
lean_dec_ref(v___x_112_);
lean_inc_ref(v___x_113_);
v___x_114_ = lean_array_push(v_data_103_, v___x_113_);
v___x_115_ = lean_byte_array_size(v___x_113_);
lean_dec_ref(v___x_113_);
v___x_116_ = lean_nat_add(v_size_104_, v___x_115_);
lean_dec(v_size_104_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v___x_116_);
lean_ctor_set(v___x_106_, 0, v___x_114_);
v___x_118_ = v___x_106_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg(lean_object* v_h_134_){
_start:
{
lean_object* v___f_135_; 
v___f_135_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1), 3, 1);
lean_closure_set(v___f_135_, 0, v_h_134_);
return v___f_135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader(lean_object* v_00_u03b1_136_, lean_object* v_h_137_){
_start:
{
lean_object* v___f_138_; 
v___f_138_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1), 3, 1);
lean_closure_set(v___f_138_, 0, v_h_137_);
return v___f_138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg(){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___closed__0));
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___boxed(lean_object* v___dummy_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg();
return v_res_144_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0(void){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg();
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(lean_object* v_s_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(lean_object* v_s_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v_s_148_);
lean_dec_ref(v_s_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(lean_object* v_s_150_, lean_object* v_p_151_){
_start:
{
uint32_t v___y_153_; lean_object* v___x_158_; uint8_t v_decide_159_; 
v___x_158_ = lean_string_utf8_byte_size(v_s_150_);
v_decide_159_ = lean_nat_dec_eq(v_p_151_, v___x_158_);
if (v_decide_159_ == 0)
{
uint32_t v___x_160_; uint8_t v___y_162_; uint32_t v___x_165_; uint8_t v___x_166_; 
v___x_160_ = lean_string_utf8_get_fast(v_s_150_, v_p_151_);
v___x_165_ = 65;
v___x_166_ = lean_uint32_dec_le(v___x_165_, v___x_160_);
if (v___x_166_ == 0)
{
v___y_162_ = v___x_166_;
goto v___jp_161_;
}
else
{
uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_167_ = 90;
v___x_168_ = lean_uint32_dec_le(v___x_160_, v___x_167_);
v___y_162_ = v___x_168_;
goto v___jp_161_;
}
v___jp_161_:
{
if (v___y_162_ == 0)
{
v___y_153_ = v___x_160_;
goto v___jp_152_;
}
else
{
uint32_t v___x_163_; uint32_t v___x_164_; 
v___x_163_ = 32;
v___x_164_ = lean_uint32_add(v___x_160_, v___x_163_);
v___y_153_ = v___x_164_;
goto v___jp_152_;
}
}
}
else
{
lean_dec(v_p_151_);
return v_s_150_;
}
v___jp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
lean_inc(v_p_151_);
v___x_154_ = lean_string_utf8_set(v_s_150_, v_p_151_, v___y_153_);
v___x_155_ = l_Char_utf8Size(v___y_153_);
v___x_156_ = lean_nat_add(v_p_151_, v___x_155_);
lean_dec(v___x_155_);
lean_dec(v_p_151_);
v_s_150_ = v___x_154_;
v_p_151_ = v___x_156_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t v_sz_169_, size_t v_i_170_, lean_object* v_bs_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lean_usize_dec_lt(v_i_170_, v_sz_169_);
if (v___x_172_ == 0)
{
return v_bs_171_;
}
else
{
lean_object* v_v_173_; lean_object* v___x_174_; lean_object* v_bs_x27_175_; lean_object* v___x_176_; lean_object* v___x_177_; size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; 
v_v_173_ = lean_array_uget(v_bs_171_, v_i_170_);
v___x_174_ = lean_unsigned_to_nat(0u);
v_bs_x27_175_ = lean_array_uset(v_bs_171_, v_i_170_, v___x_174_);
v___x_176_ = l_String_Slice_toString(v_v_173_);
lean_dec(v_v_173_);
v___x_177_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_176_, v___x_174_);
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_170_, v___x_178_);
v___x_180_ = lean_array_uset(v_bs_x27_175_, v_i_170_, v___x_177_);
v_i_170_ = v___x_179_;
v_bs_171_ = v___x_180_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(lean_object* v_sz_182_, lean_object* v_i_183_, lean_object* v_bs_184_){
_start:
{
size_t v_sz_boxed_185_; size_t v_i_boxed_186_; lean_object* v_res_187_; 
v_sz_boxed_185_ = lean_unbox_usize(v_sz_182_);
lean_dec(v_sz_182_);
v_i_boxed_186_ = lean_unbox_usize(v_i_183_);
lean_dec(v_i_183_);
v_res_187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_boxed_185_, v_i_boxed_186_, v_bs_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(lean_object* v___x_188_, lean_object* v___x_189_, lean_object* v___x_190_, lean_object* v_a_191_, lean_object* v_b_192_){
_start:
{
lean_object* v_it_194_; lean_object* v_startInclusive_195_; lean_object* v_endExclusive_196_; 
if (lean_obj_tag(v_a_191_) == 0)
{
lean_object* v_currPos_201_; lean_object* v_searcher_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_231_; 
v_currPos_201_ = lean_ctor_get(v_a_191_, 0);
v_searcher_202_ = lean_ctor_get(v_a_191_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v_a_191_);
if (v_isSharedCheck_231_ == 0)
{
v___x_204_ = v_a_191_;
v_isShared_205_ = v_isSharedCheck_231_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_searcher_202_);
lean_inc(v_currPos_201_);
lean_dec(v_a_191_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_231_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v_str_206_; lean_object* v_startInclusive_207_; lean_object* v_endExclusive_208_; lean_object* v___x_209_; uint8_t v_decide_210_; 
v_str_206_ = lean_ctor_get(v___x_189_, 0);
v_startInclusive_207_ = lean_ctor_get(v___x_189_, 1);
v_endExclusive_208_ = lean_ctor_get(v___x_189_, 2);
v___x_209_ = lean_nat_sub(v_endExclusive_208_, v_startInclusive_207_);
v_decide_210_ = lean_nat_dec_eq(v_searcher_202_, v___x_209_);
lean_dec(v___x_209_);
if (v_decide_210_ == 0)
{
lean_object* v___x_211_; uint32_t v___x_212_; uint32_t v___x_213_; uint8_t v___x_214_; 
v___x_211_ = lean_nat_add(v_startInclusive_207_, v_searcher_202_);
v___x_212_ = lean_string_utf8_get_fast(v_str_206_, v___x_211_);
v___x_213_ = 44;
v___x_214_ = lean_uint32_dec_eq(v___x_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
lean_dec(v_searcher_202_);
v___x_215_ = lean_string_utf8_next_fast(v_str_206_, v___x_211_);
lean_dec(v___x_211_);
v___x_216_ = lean_nat_sub(v___x_215_, v_startInclusive_207_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_216_);
v___x_218_ = v___x_204_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_currPos_201_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v___x_216_);
v___x_218_ = v_reuseFailAlloc_220_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
v_a_191_ = v___x_218_;
goto _start;
}
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v_slice_224_; lean_object* v_nextIt_226_; 
v___x_221_ = lean_string_utf8_next_fast(v_str_206_, v___x_211_);
v___x_222_ = lean_nat_sub(v___x_221_, v___x_211_);
lean_dec(v___x_211_);
v___x_223_ = lean_nat_add(v_searcher_202_, v___x_222_);
lean_dec(v___x_222_);
v_slice_224_ = l_String_Slice_subslice_x21(v___x_189_, v_currPos_201_, v_searcher_202_);
lean_inc(v___x_223_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_223_);
lean_ctor_set(v___x_204_, 0, v___x_223_);
v_nextIt_226_ = v___x_204_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_223_);
v_nextIt_226_ = v_reuseFailAlloc_229_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v_startInclusive_227_; lean_object* v_endExclusive_228_; 
v_startInclusive_227_ = lean_ctor_get(v_slice_224_, 0);
lean_inc(v_startInclusive_227_);
v_endExclusive_228_ = lean_ctor_get(v_slice_224_, 1);
lean_inc(v_endExclusive_228_);
lean_dec_ref(v_slice_224_);
v_it_194_ = v_nextIt_226_;
v_startInclusive_195_ = v_startInclusive_227_;
v_endExclusive_196_ = v_endExclusive_228_;
goto v___jp_193_;
}
}
}
else
{
lean_object* v___x_230_; 
lean_del_object(v___x_204_);
lean_dec(v_searcher_202_);
v___x_230_ = lean_box(1);
lean_inc(v___x_190_);
v_it_194_ = v___x_230_;
v_startInclusive_195_ = v_currPos_201_;
v_endExclusive_196_ = v___x_190_;
goto v___jp_193_;
}
}
}
else
{
lean_dec(v___x_190_);
lean_dec_ref(v___x_188_);
return v_b_192_;
}
v___jp_193_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
lean_inc_ref(v___x_188_);
v___x_197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_197_, 0, v___x_188_);
lean_ctor_set(v___x_197_, 1, v_startInclusive_195_);
lean_ctor_set(v___x_197_, 2, v_endExclusive_196_);
v___x_198_ = l_String_Slice_trimAscii(v___x_197_);
v___x_199_ = lean_array_push(v_b_192_, v___x_198_);
v_a_191_ = v_it_194_;
v_b_192_ = v___x_199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(lean_object* v___x_232_, lean_object* v___x_233_, lean_object* v___x_234_, lean_object* v_a_235_, lean_object* v_b_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_232_, v___x_233_, v___x_234_, v_a_235_, v_b_236_);
lean_dec_ref(v___x_233_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(lean_object* v___x_238_, lean_object* v___x_239_, lean_object* v___x_240_, lean_object* v_a_241_, lean_object* v_b_242_){
_start:
{
lean_object* v_it_244_; lean_object* v_startInclusive_245_; lean_object* v_endExclusive_246_; 
if (lean_obj_tag(v_a_241_) == 0)
{
lean_object* v_currPos_251_; lean_object* v_searcher_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_281_; 
v_currPos_251_ = lean_ctor_get(v_a_241_, 0);
v_searcher_252_ = lean_ctor_get(v_a_241_, 1);
v_isSharedCheck_281_ = !lean_is_exclusive(v_a_241_);
if (v_isSharedCheck_281_ == 0)
{
v___x_254_ = v_a_241_;
v_isShared_255_ = v_isSharedCheck_281_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_searcher_252_);
lean_inc(v_currPos_251_);
lean_dec(v_a_241_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_281_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_str_256_; lean_object* v_startInclusive_257_; lean_object* v_endExclusive_258_; lean_object* v___x_259_; uint8_t v_decide_260_; 
v_str_256_ = lean_ctor_get(v___x_239_, 0);
v_startInclusive_257_ = lean_ctor_get(v___x_239_, 1);
v_endExclusive_258_ = lean_ctor_get(v___x_239_, 2);
v___x_259_ = lean_nat_sub(v_endExclusive_258_, v_startInclusive_257_);
v_decide_260_ = lean_nat_dec_eq(v_searcher_252_, v___x_259_);
lean_dec(v___x_259_);
if (v_decide_260_ == 0)
{
lean_object* v___x_261_; uint32_t v___x_262_; uint32_t v___x_263_; uint8_t v___x_264_; 
v___x_261_ = lean_nat_add(v_startInclusive_257_, v_searcher_252_);
v___x_262_ = lean_string_utf8_get_fast(v_str_256_, v___x_261_);
v___x_263_ = 44;
v___x_264_ = lean_uint32_dec_eq(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
lean_dec(v_searcher_252_);
v___x_265_ = lean_string_utf8_next_fast(v_str_256_, v___x_261_);
lean_dec(v___x_261_);
v___x_266_ = lean_nat_sub(v___x_265_, v_startInclusive_257_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_266_);
v___x_268_ = v___x_254_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_currPos_251_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v___x_266_);
v___x_268_ = v_reuseFailAlloc_270_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; 
v___x_269_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_238_, v___x_239_, v___x_240_, v___x_268_, v_b_242_);
return v___x_269_;
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_slice_274_; lean_object* v_nextIt_276_; 
v___x_271_ = lean_string_utf8_next_fast(v_str_256_, v___x_261_);
v___x_272_ = lean_nat_sub(v___x_271_, v___x_261_);
lean_dec(v___x_261_);
v___x_273_ = lean_nat_add(v_searcher_252_, v___x_272_);
lean_dec(v___x_272_);
v_slice_274_ = l_String_Slice_subslice_x21(v___x_239_, v_currPos_251_, v_searcher_252_);
lean_inc(v___x_273_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_273_);
lean_ctor_set(v___x_254_, 0, v___x_273_);
v_nextIt_276_ = v___x_254_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v___x_273_);
v_nextIt_276_ = v_reuseFailAlloc_279_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v_startInclusive_277_; lean_object* v_endExclusive_278_; 
v_startInclusive_277_ = lean_ctor_get(v_slice_274_, 0);
lean_inc(v_startInclusive_277_);
v_endExclusive_278_ = lean_ctor_get(v_slice_274_, 1);
lean_inc(v_endExclusive_278_);
lean_dec_ref(v_slice_274_);
v_it_244_ = v_nextIt_276_;
v_startInclusive_245_ = v_startInclusive_277_;
v_endExclusive_246_ = v_endExclusive_278_;
goto v___jp_243_;
}
}
}
else
{
lean_object* v___x_280_; 
lean_del_object(v___x_254_);
lean_dec(v_searcher_252_);
v___x_280_ = lean_box(1);
lean_inc(v___x_240_);
v_it_244_ = v___x_280_;
v_startInclusive_245_ = v_currPos_251_;
v_endExclusive_246_ = v___x_240_;
goto v___jp_243_;
}
}
}
else
{
lean_dec(v___x_240_);
lean_dec_ref(v___x_238_);
return v_b_242_;
}
v___jp_243_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_inc_ref(v___x_238_);
v___x_247_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_247_, 0, v___x_238_);
lean_ctor_set(v___x_247_, 1, v_startInclusive_245_);
lean_ctor_set(v___x_247_, 2, v_endExclusive_246_);
v___x_248_ = l_String_Slice_trimAscii(v___x_247_);
v___x_249_ = lean_array_push(v_b_242_, v___x_248_);
v___x_250_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_238_, v___x_239_, v___x_240_, v_it_244_, v___x_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(lean_object* v___x_282_, lean_object* v___x_283_, lean_object* v___x_284_, lean_object* v_a_285_, lean_object* v_b_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_282_, v___x_283_, v___x_284_, v_a_285_, v_b_286_);
lean_dec_ref(v___x_283_);
return v_res_287_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object* v___x_288_, lean_object* v___x_289_, lean_object* v___x_290_, lean_object* v_a_291_, uint8_t v_b_292_){
_start:
{
if (lean_obj_tag(v_a_291_) == 0)
{
lean_object* v_currPos_293_; lean_object* v_searcher_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_337_; 
v_currPos_293_ = lean_ctor_get(v_a_291_, 0);
v_searcher_294_ = lean_ctor_get(v_a_291_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_a_291_);
if (v_isSharedCheck_337_ == 0)
{
v___x_296_ = v_a_291_;
v_isShared_297_ = v_isSharedCheck_337_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_searcher_294_);
lean_inc(v_currPos_293_);
lean_dec(v_a_291_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_337_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v_str_298_; lean_object* v_startInclusive_299_; lean_object* v_endExclusive_300_; uint8_t v___x_301_; lean_object* v_it_303_; lean_object* v_startInclusive_304_; lean_object* v_endExclusive_305_; lean_object* v___x_315_; uint8_t v_decide_316_; 
v_str_298_ = lean_ctor_get(v___x_289_, 0);
v_startInclusive_299_ = lean_ctor_get(v___x_289_, 1);
v_endExclusive_300_ = lean_ctor_get(v___x_289_, 2);
v___x_301_ = 1;
v___x_315_ = lean_nat_sub(v_endExclusive_300_, v_startInclusive_299_);
v_decide_316_ = lean_nat_dec_eq(v_searcher_294_, v___x_315_);
lean_dec(v___x_315_);
if (v_decide_316_ == 0)
{
lean_object* v___x_317_; uint32_t v___x_318_; uint32_t v___x_319_; uint8_t v___x_320_; 
v___x_317_ = lean_nat_add(v_startInclusive_299_, v_searcher_294_);
v___x_318_ = lean_string_utf8_get_fast(v_str_298_, v___x_317_);
v___x_319_ = 44;
v___x_320_ = lean_uint32_dec_eq(v___x_318_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_dec(v_searcher_294_);
v___x_321_ = lean_string_utf8_next_fast(v_str_298_, v___x_317_);
lean_dec(v___x_317_);
v___x_322_ = lean_nat_sub(v___x_321_, v_startInclusive_299_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_322_);
v___x_324_ = v___x_296_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_currPos_293_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v___x_322_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
v_a_291_ = v___x_324_;
goto _start;
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v_slice_330_; lean_object* v_nextIt_332_; 
v___x_327_ = lean_string_utf8_next_fast(v_str_298_, v___x_317_);
v___x_328_ = lean_nat_sub(v___x_327_, v___x_317_);
lean_dec(v___x_317_);
v___x_329_ = lean_nat_add(v_searcher_294_, v___x_328_);
lean_dec(v___x_328_);
v_slice_330_ = l_String_Slice_subslice_x21(v___x_289_, v_currPos_293_, v_searcher_294_);
lean_inc(v___x_329_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v___x_329_);
lean_ctor_set(v___x_296_, 0, v___x_329_);
v_nextIt_332_ = v___x_296_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_329_);
v_nextIt_332_ = v_reuseFailAlloc_335_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v_startInclusive_333_; lean_object* v_endExclusive_334_; 
v_startInclusive_333_ = lean_ctor_get(v_slice_330_, 0);
lean_inc(v_startInclusive_333_);
v_endExclusive_334_ = lean_ctor_get(v_slice_330_, 1);
lean_inc(v_endExclusive_334_);
lean_dec_ref(v_slice_330_);
v_it_303_ = v_nextIt_332_;
v_startInclusive_304_ = v_startInclusive_333_;
v_endExclusive_305_ = v_endExclusive_334_;
goto v___jp_302_;
}
}
}
else
{
lean_object* v___x_336_; 
lean_del_object(v___x_296_);
lean_dec(v_searcher_294_);
v___x_336_ = lean_box(1);
lean_inc(v___x_290_);
v_it_303_ = v___x_336_;
v_startInclusive_304_ = v_currPos_293_;
v_endExclusive_305_ = v___x_290_;
goto v___jp_302_;
}
v___jp_302_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v_startInclusive_308_; lean_object* v_endExclusive_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
lean_inc_ref(v___x_288_);
v___x_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_306_, 0, v___x_288_);
lean_ctor_set(v___x_306_, 1, v_startInclusive_304_);
lean_ctor_set(v___x_306_, 2, v_endExclusive_305_);
v___x_307_ = l_String_Slice_trimAscii(v___x_306_);
v_startInclusive_308_ = lean_ctor_get(v___x_307_, 1);
lean_inc(v_startInclusive_308_);
v_endExclusive_309_ = lean_ctor_get(v___x_307_, 2);
lean_inc(v_endExclusive_309_);
lean_dec_ref(v___x_307_);
v___x_310_ = lean_nat_sub(v_endExclusive_309_, v_startInclusive_308_);
lean_dec(v_startInclusive_308_);
lean_dec(v_endExclusive_309_);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_nat_dec_eq(v___x_310_, v___x_311_);
lean_dec(v___x_310_);
if (v___x_312_ == 0)
{
v_a_291_ = v_it_303_;
v_b_292_ = v___x_301_;
goto _start;
}
else
{
uint8_t v___x_314_; 
lean_dec(v_it_303_);
lean_dec(v___x_290_);
lean_dec_ref(v___x_288_);
v___x_314_ = 0;
return v___x_314_;
}
}
}
}
else
{
lean_dec(v___x_290_);
lean_dec_ref(v___x_288_);
return v_b_292_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object* v___x_338_, lean_object* v___x_339_, lean_object* v___x_340_, lean_object* v_a_341_, lean_object* v_b_342_){
_start:
{
uint8_t v_b_boxed_343_; uint8_t v_res_344_; lean_object* v_r_345_; 
v_b_boxed_343_ = lean_unbox(v_b_342_);
v_res_344_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_338_, v___x_339_, v___x_340_, v_a_341_, v_b_boxed_343_);
lean_dec_ref(v___x_339_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object* v___x_346_, lean_object* v___x_347_, lean_object* v___x_348_, lean_object* v_a_349_, uint8_t v_b_350_){
_start:
{
if (lean_obj_tag(v_a_349_) == 0)
{
lean_object* v_currPos_351_; lean_object* v_searcher_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_395_; 
v_currPos_351_ = lean_ctor_get(v_a_349_, 0);
v_searcher_352_ = lean_ctor_get(v_a_349_, 1);
v_isSharedCheck_395_ = !lean_is_exclusive(v_a_349_);
if (v_isSharedCheck_395_ == 0)
{
v___x_354_ = v_a_349_;
v_isShared_355_ = v_isSharedCheck_395_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_searcher_352_);
lean_inc(v_currPos_351_);
lean_dec(v_a_349_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_395_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_str_356_; lean_object* v_startInclusive_357_; lean_object* v_endExclusive_358_; uint8_t v___x_359_; lean_object* v_it_361_; lean_object* v_startInclusive_362_; lean_object* v_endExclusive_363_; lean_object* v___x_373_; uint8_t v_decide_374_; 
v_str_356_ = lean_ctor_get(v___x_347_, 0);
v_startInclusive_357_ = lean_ctor_get(v___x_347_, 1);
v_endExclusive_358_ = lean_ctor_get(v___x_347_, 2);
v___x_359_ = 1;
v___x_373_ = lean_nat_sub(v_endExclusive_358_, v_startInclusive_357_);
v_decide_374_ = lean_nat_dec_eq(v_searcher_352_, v___x_373_);
lean_dec(v___x_373_);
if (v_decide_374_ == 0)
{
lean_object* v___x_375_; uint32_t v___x_376_; uint32_t v___x_377_; uint8_t v___x_378_; 
v___x_375_ = lean_nat_add(v_startInclusive_357_, v_searcher_352_);
v___x_376_ = lean_string_utf8_get_fast(v_str_356_, v___x_375_);
v___x_377_ = 44;
v___x_378_ = lean_uint32_dec_eq(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
lean_dec(v_searcher_352_);
v___x_379_ = lean_string_utf8_next_fast(v_str_356_, v___x_375_);
lean_dec(v___x_375_);
v___x_380_ = lean_nat_sub(v___x_379_, v_startInclusive_357_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v___x_380_);
v___x_382_ = v___x_354_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_currPos_351_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_384_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
uint8_t v___x_383_; 
v___x_383_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_346_, v___x_347_, v___x_348_, v___x_382_, v_b_350_);
return v___x_383_;
}
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v_slice_388_; lean_object* v_nextIt_390_; 
v___x_385_ = lean_string_utf8_next_fast(v_str_356_, v___x_375_);
v___x_386_ = lean_nat_sub(v___x_385_, v___x_375_);
lean_dec(v___x_375_);
v___x_387_ = lean_nat_add(v_searcher_352_, v___x_386_);
lean_dec(v___x_386_);
v_slice_388_ = l_String_Slice_subslice_x21(v___x_347_, v_currPos_351_, v_searcher_352_);
lean_inc(v___x_387_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v___x_387_);
lean_ctor_set(v___x_354_, 0, v___x_387_);
v_nextIt_390_ = v___x_354_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_387_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v___x_387_);
v_nextIt_390_ = v_reuseFailAlloc_393_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v_startInclusive_391_; lean_object* v_endExclusive_392_; 
v_startInclusive_391_ = lean_ctor_get(v_slice_388_, 0);
lean_inc(v_startInclusive_391_);
v_endExclusive_392_ = lean_ctor_get(v_slice_388_, 1);
lean_inc(v_endExclusive_392_);
lean_dec_ref(v_slice_388_);
v_it_361_ = v_nextIt_390_;
v_startInclusive_362_ = v_startInclusive_391_;
v_endExclusive_363_ = v_endExclusive_392_;
goto v___jp_360_;
}
}
}
else
{
lean_object* v___x_394_; 
lean_del_object(v___x_354_);
lean_dec(v_searcher_352_);
v___x_394_ = lean_box(1);
lean_inc(v___x_348_);
v_it_361_ = v___x_394_;
v_startInclusive_362_ = v_currPos_351_;
v_endExclusive_363_ = v___x_348_;
goto v___jp_360_;
}
v___jp_360_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_startInclusive_366_; lean_object* v_endExclusive_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
lean_inc_ref(v___x_346_);
v___x_364_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_364_, 0, v___x_346_);
lean_ctor_set(v___x_364_, 1, v_startInclusive_362_);
lean_ctor_set(v___x_364_, 2, v_endExclusive_363_);
v___x_365_ = l_String_Slice_trimAscii(v___x_364_);
v_startInclusive_366_ = lean_ctor_get(v___x_365_, 1);
lean_inc(v_startInclusive_366_);
v_endExclusive_367_ = lean_ctor_get(v___x_365_, 2);
lean_inc(v_endExclusive_367_);
lean_dec_ref(v___x_365_);
v___x_368_ = lean_nat_sub(v_endExclusive_367_, v_startInclusive_366_);
lean_dec(v_startInclusive_366_);
lean_dec(v_endExclusive_367_);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_nat_dec_eq(v___x_368_, v___x_369_);
lean_dec(v___x_368_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
v___x_371_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_346_, v___x_347_, v___x_348_, v_it_361_, v___x_359_);
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
lean_dec(v_it_361_);
lean_dec(v___x_348_);
lean_dec_ref(v___x_346_);
v___x_372_ = 0;
return v___x_372_;
}
}
}
}
else
{
lean_dec(v___x_348_);
lean_dec_ref(v___x_346_);
return v_b_350_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object* v___x_396_, lean_object* v___x_397_, lean_object* v___x_398_, lean_object* v_a_399_, lean_object* v_b_400_){
_start:
{
uint8_t v_b_boxed_401_; uint8_t v_res_402_; lean_object* v_r_403_; 
v_b_boxed_401_ = lean_unbox(v_b_400_);
v_res_402_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_396_, v___x_397_, v___x_398_, v_a_399_, v_b_boxed_401_);
lean_dec_ref(v___x_397_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object* v_v_406_){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_parts_410_; uint8_t v___x_411_; uint8_t v___x_412_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_string_utf8_byte_size(v_v_406_);
lean_inc_ref_n(v_v_406_, 2);
v___x_409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_409_, 0, v_v_406_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
lean_ctor_set(v___x_409_, 2, v___x_408_);
v_parts_410_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
v___x_411_ = 1;
v___x_412_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_406_, v___x_409_, v___x_408_, v_parts_410_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
lean_dec_ref_known(v___x_409_, 3);
lean_dec_ref(v_v_406_);
v___x_413_ = lean_box(0);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; size_t v_sz_416_; size_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_414_ = ((lean_object*)(l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0));
v___x_415_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v_v_406_, v___x_409_, v___x_408_, v_parts_410_, v___x_414_);
lean_dec_ref_known(v___x_409_, 3);
v_sz_416_ = lean_array_size(v___x_415_);
v___x_417_ = ((size_t)0ULL);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_416_, v___x_417_, v___x_415_);
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
return v___x_419_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object* v___x_420_, lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v_inst_423_, lean_object* v_R_424_, lean_object* v_a_425_, uint8_t v_b_426_, lean_object* v_c_427_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_420_, v___x_421_, v___x_422_, v_a_425_, v_b_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v___x_431_, lean_object* v_inst_432_, lean_object* v_R_433_, lean_object* v_a_434_, lean_object* v_b_435_, lean_object* v_c_436_){
_start:
{
uint8_t v_b_boxed_437_; uint8_t v_res_438_; lean_object* v_r_439_; 
v_b_boxed_437_ = lean_unbox(v_b_435_);
v_res_438_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_429_, v___x_430_, v___x_431_, v_inst_432_, v_R_433_, v_a_434_, v_b_boxed_437_, v_c_436_);
lean_dec_ref(v___x_430_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v_inst_443_, lean_object* v_R_444_, lean_object* v_a_445_, lean_object* v_b_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_440_, v___x_441_, v___x_442_, v_a_445_, v_b_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v_inst_451_, lean_object* v_R_452_, lean_object* v_a_453_, lean_object* v_b_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_448_, v___x_449_, v___x_450_, v_inst_451_, v_R_452_, v_a_453_, v_b_454_);
lean_dec_ref(v___x_449_);
return v_res_455_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object* v___x_456_, lean_object* v___x_457_, lean_object* v___x_458_, lean_object* v_inst_459_, lean_object* v_R_460_, lean_object* v_a_461_, uint8_t v_b_462_, lean_object* v_c_463_){
_start:
{
uint8_t v___x_464_; 
v___x_464_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_456_, v___x_457_, v___x_458_, v_a_461_, v_b_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v___x_467_, lean_object* v_inst_468_, lean_object* v_R_469_, lean_object* v_a_470_, lean_object* v_b_471_, lean_object* v_c_472_){
_start:
{
uint8_t v_b_boxed_473_; uint8_t v_res_474_; lean_object* v_r_475_; 
v_b_boxed_473_ = lean_unbox(v_b_471_);
v_res_474_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_465_, v___x_466_, v___x_467_, v_inst_468_, v_R_469_, v_a_470_, v_b_boxed_473_, v_c_472_);
lean_dec_ref(v___x_466_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v_inst_479_, lean_object* v_R_480_, lean_object* v_a_481_, lean_object* v_b_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_476_, v___x_477_, v___x_478_, v_a_481_, v_b_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v___x_486_, lean_object* v_inst_487_, lean_object* v_R_488_, lean_object* v_a_489_, lean_object* v_b_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(v___x_484_, v___x_485_, v___x_486_, v_inst_487_, v_R_488_, v_a_489_, v_b_490_);
lean_dec_ref(v___x_485_);
return v_res_491_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqContentLength_beq(lean_object* v_x_492_, lean_object* v_x_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_nat_dec_eq(v_x_492_, v_x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqContentLength_beq___boxed(lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = l_Std_Http_Header_instBEqContentLength_beq(v_x_495_, v_x_496_);
lean_dec(v_x_496_);
lean_dec(v_x_495_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprContentLength_repr_spec__0(lean_object* v_a_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = lean_nat_to_int(v_a_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(10u);
v___x_517_ = lean_nat_to_int(v___x_516_);
return v___x_517_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0));
v___x_520_ = lean_string_length(v___x_519_);
return v___x_520_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9);
v___x_522_ = lean_nat_to_int(v___x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg(lean_object* v_x_527_){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_528_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6));
v___x_529_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_530_ = l_Nat_reprFast(v_x_527_);
v___x_531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
v___x_532_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_529_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = 0;
v___x_534_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*1, v___x_533_);
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_528_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_537_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_535_);
v___x_539_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_536_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_533_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr(lean_object* v_x_543_, lean_object* v_prec_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_Http_Header_instReprContentLength_repr___redArg(v_x_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___boxed(lean_object* v_x_546_, lean_object* v_prec_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Http_Header_instReprContentLength_repr(v_x_546_, v_prec_547_);
lean_dec(v_prec_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(lean_object* v_s_551_, lean_object* v_pos_552_){
_start:
{
lean_object* v_str_553_; lean_object* v_startInclusive_554_; lean_object* v_endExclusive_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v_decide_559_; 
v_str_553_ = lean_ctor_get(v_s_551_, 0);
v_startInclusive_554_ = lean_ctor_get(v_s_551_, 1);
v_endExclusive_555_ = lean_ctor_get(v_s_551_, 2);
v___x_556_ = lean_nat_add(v_startInclusive_554_, v_pos_552_);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_nat_sub(v_endExclusive_555_, v___x_556_);
v_decide_559_ = lean_nat_dec_eq(v___x_557_, v___x_558_);
lean_dec(v___x_558_);
if (v_decide_559_ == 0)
{
uint32_t v___x_560_; uint32_t v___x_561_; uint8_t v___x_562_; 
v___x_560_ = lean_string_utf8_get_fast(v_str_553_, v___x_556_);
v___x_561_ = 48;
v___x_562_ = lean_uint32_dec_le(v___x_561_, v___x_560_);
if (v___x_562_ == 0)
{
lean_dec(v___x_556_);
return v_pos_552_;
}
else
{
uint32_t v___x_563_; uint8_t v___x_564_; 
v___x_563_ = 57;
v___x_564_ = lean_uint32_dec_le(v___x_560_, v___x_563_);
if (v___x_564_ == 0)
{
lean_dec(v___x_556_);
return v_pos_552_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_565_ = lean_string_utf8_next_fast(v_str_553_, v___x_556_);
v___x_566_ = lean_nat_sub(v___x_565_, v___x_556_);
lean_dec(v___x_556_);
v___x_567_ = lean_nat_add(v_pos_552_, v___x_566_);
lean_dec(v___x_566_);
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_add(v_pos_552_, v___x_568_);
v___x_570_ = lean_nat_dec_le(v___x_569_, v___x_567_);
lean_dec(v___x_569_);
if (v___x_570_ == 0)
{
lean_dec(v___x_567_);
return v_pos_552_;
}
else
{
lean_dec(v_pos_552_);
v_pos_552_ = v___x_567_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_556_);
return v_pos_552_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0___boxed(lean_object* v_s_572_, lean_object* v_pos_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v_s_572_, v_pos_573_);
lean_dec_ref(v_s_572_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_parse(lean_object* v_v_575_){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_576_ = lean_string_utf8_byte_size(v_v_575_);
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_nat_dec_eq(v___x_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v_decide_581_; 
v___x_579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_579_, 0, v_v_575_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
lean_ctor_set(v___x_579_, 2, v___x_576_);
v___x_580_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v___x_579_, v___x_577_);
v_decide_581_ = lean_nat_dec_eq(v___x_580_, v___x_576_);
lean_dec(v___x_580_);
if (v_decide_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec_ref_known(v___x_579_, 3);
v___x_582_ = lean_box(0);
return v___x_582_;
}
else
{
lean_object* v___x_583_; 
v___x_583_ = l_String_Slice_toNat_x3f(v___x_579_);
lean_dec_ref_known(v___x_579_, 3);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_box(0);
return v___x_584_;
}
else
{
lean_object* v_val_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
v_val_585_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_583_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_val_585_);
lean_dec(v___x_583_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_val_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
else
{
lean_object* v___x_593_; 
lean_dec_ref(v_v_575_);
v___x_593_ = lean_box(0);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_serialize(lean_object* v_h_594_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_595_ = l_Std_Http_Header_Name_contentLength;
v___x_596_ = l_Nat_reprFast(v_h_594_);
v___x_597_ = l_Std_Http_Header_Value_ofString_x21(v___x_596_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
if (lean_obj_tag(v_x_606_) == 0)
{
uint8_t v___x_607_; 
v___x_607_ = 1;
return v___x_607_;
}
else
{
uint8_t v___x_608_; 
v___x_608_ = 0;
return v___x_608_;
}
}
else
{
if (lean_obj_tag(v_x_606_) == 0)
{
uint8_t v___x_609_; 
v___x_609_ = 0;
return v___x_609_;
}
else
{
lean_object* v_val_610_; lean_object* v_val_611_; uint8_t v___x_612_; 
v_val_610_ = lean_ctor_get(v_x_605_, 0);
v_val_611_ = lean_ctor_get(v_x_606_, 0);
v___x_612_ = lean_string_dec_eq(v_val_610_, v_val_611_);
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_613_, v_x_614_);
lean_dec(v_x_614_);
lean_dec(v_x_613_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object* v_as_618_, size_t v_i_619_, size_t v_stop_620_, lean_object* v_b_621_){
_start:
{
lean_object* v___y_623_; uint8_t v___x_627_; 
v___x_627_ = lean_usize_dec_eq(v_i_619_, v_stop_620_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_628_ = lean_array_uget_borrowed(v_as_618_, v_i_619_);
v___x_629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_630_ = lean_string_dec_eq(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
v___y_623_ = v_b_621_;
goto v___jp_622_;
}
else
{
lean_object* v___x_631_; 
lean_inc(v___x_628_);
v___x_631_ = lean_array_push(v_b_621_, v___x_628_);
v___y_623_ = v___x_631_;
goto v___jp_622_;
}
}
else
{
return v_b_621_;
}
v___jp_622_:
{
size_t v___x_624_; size_t v___x_625_; 
v___x_624_ = ((size_t)1ULL);
v___x_625_ = lean_usize_add(v_i_619_, v___x_624_);
v_i_619_ = v___x_625_;
v_b_621_ = v___y_623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object* v_as_632_, lean_object* v_i_633_, lean_object* v_stop_634_, lean_object* v_b_635_){
_start:
{
size_t v_i_boxed_636_; size_t v_stop_boxed_637_; lean_object* v_res_638_; 
v_i_boxed_636_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_stop_boxed_637_ = lean_unbox_usize(v_stop_634_);
lean_dec(v_stop_634_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_632_, v_i_boxed_636_, v_stop_boxed_637_, v_b_635_);
lean_dec_ref(v_as_632_);
return v_res_638_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object* v___x_639_, lean_object* v_as_640_, size_t v_i_641_, size_t v_stop_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = lean_usize_dec_eq(v_i_641_, v_stop_642_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_644_ = 1;
v___x_645_ = lean_array_uget_borrowed(v_as_640_, v_i_641_);
lean_inc(v___x_645_);
v___x_646_ = l_Std_Http_Internal_isToken(v___x_645_);
if (v___x_646_ == 0)
{
return v___x_644_;
}
else
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = lean_nat_dec_eq(v___x_639_, v___x_647_);
if (v___x_648_ == 0)
{
size_t v___x_649_; size_t v___x_650_; 
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_i_641_, v___x_649_);
v_i_641_ = v___x_650_;
goto _start;
}
else
{
return v___x_644_;
}
}
}
else
{
uint8_t v___x_652_; 
v___x_652_ = 0;
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object* v___x_653_, lean_object* v_as_654_, lean_object* v_i_655_, lean_object* v_stop_656_){
_start:
{
size_t v_i_boxed_657_; size_t v_stop_boxed_658_; uint8_t v_res_659_; lean_object* v_r_660_; 
v_i_boxed_657_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_stop_boxed_658_ = lean_unbox_usize(v_stop_656_);
lean_dec(v_stop_656_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_653_, v_as_654_, v_i_boxed_657_, v_stop_boxed_658_);
lean_dec_ref(v_as_654_);
lean_dec(v___x_653_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object* v_codings_665_){
_start:
{
lean_object* v___y_667_; uint8_t v___y_668_; uint8_t v___y_669_; lean_object* v___y_670_; uint8_t v___y_677_; uint8_t v___y_678_; lean_object* v___y_679_; uint8_t v___y_689_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_array_get_size(v_codings_665_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_nat_dec_eq(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
uint8_t v___x_705_; 
v___x_705_ = lean_nat_dec_lt(v___x_703_, v___x_702_);
if (v___x_705_ == 0)
{
v___y_689_ = v___x_705_;
goto v___jp_688_;
}
else
{
if (v___x_705_ == 0)
{
v___y_689_ = v___x_705_;
goto v___jp_688_;
}
else
{
size_t v___x_706_; size_t v___x_707_; uint8_t v___x_708_; 
v___x_706_ = ((size_t)0ULL);
v___x_707_ = lean_usize_of_nat(v___x_702_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_702_, v_codings_665_, v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
v___y_689_ = v___x_708_;
goto v___jp_688_;
}
else
{
return v___x_704_;
}
}
}
}
else
{
uint8_t v___x_709_; 
v___x_709_ = 0;
return v___x_709_;
}
v___jp_666_:
{
lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_dec_lt(v___x_671_, v___y_667_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_eq(v___y_667_, v___x_671_);
lean_dec(v___y_667_);
if (v___x_673_ == 0)
{
lean_dec(v___y_670_);
return v___y_669_;
}
else
{
lean_object* v___x_674_; uint8_t v_lastIsChunked_675_; 
v___x_674_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v_lastIsChunked_675_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_670_, v___x_674_);
lean_dec(v___y_670_);
if (v_lastIsChunked_675_ == 0)
{
return v___x_672_;
}
else
{
return v___y_669_;
}
}
}
else
{
lean_dec(v___y_670_);
lean_dec(v___y_667_);
return v___y_668_;
}
}
v___jp_676_:
{
lean_object* v_chunkedCount_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_chunkedCount_680_ = lean_array_get_size(v___y_679_);
lean_dec_ref(v___y_679_);
v___x_681_ = lean_array_get_size(v_codings_665_);
v___x_682_ = lean_unsigned_to_nat(1u);
v___x_683_ = lean_nat_sub(v___x_681_, v___x_682_);
v___x_684_ = lean_nat_dec_lt(v___x_683_, v___x_681_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; 
lean_dec(v___x_683_);
v___x_685_ = lean_box(0);
v___y_667_ = v_chunkedCount_680_;
v___y_668_ = v___y_678_;
v___y_669_ = v___y_677_;
v___y_670_ = v___x_685_;
goto v___jp_666_;
}
else
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_array_fget_borrowed(v_codings_665_, v___x_683_);
lean_dec(v___x_683_);
lean_inc(v___x_686_);
v___x_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
v___y_667_ = v_chunkedCount_680_;
v___y_668_ = v___y_678_;
v___y_669_ = v___y_677_;
v___y_670_ = v___x_687_;
goto v___jp_666_;
}
}
v___jp_688_:
{
uint8_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_690_ = 1;
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_array_get_size(v_codings_665_);
v___x_693_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__1));
v___x_694_ = lean_nat_dec_lt(v___x_691_, v___x_692_);
if (v___x_694_ == 0)
{
v___y_677_ = v___x_690_;
v___y_678_ = v___y_689_;
v___y_679_ = v___x_693_;
goto v___jp_676_;
}
else
{
uint8_t v___x_695_; 
v___x_695_ = lean_nat_dec_le(v___x_692_, v___x_692_);
if (v___x_695_ == 0)
{
if (v___x_694_ == 0)
{
v___y_677_ = v___x_690_;
v___y_678_ = v___y_689_;
v___y_679_ = v___x_693_;
goto v___jp_676_;
}
else
{
size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
v___x_696_ = ((size_t)0ULL);
v___x_697_ = lean_usize_of_nat(v___x_692_);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_665_, v___x_696_, v___x_697_, v___x_693_);
v___y_677_ = v___x_690_;
v___y_678_ = v___y_689_;
v___y_679_ = v___x_698_;
goto v___jp_676_;
}
}
else
{
size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((size_t)0ULL);
v___x_700_ = lean_usize_of_nat(v___x_692_);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_665_, v___x_699_, v___x_700_, v___x_693_);
v___y_677_ = v___x_690_;
v___y_678_ = v___y_689_;
v___y_679_ = v___x_701_;
goto v___jp_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_Validate___boxed(lean_object* v_codings_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_710_);
lean_dec_ref(v_codings_710_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(lean_object* v___y_713_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = l_String_quote(v___y_713_);
v___x_715_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_718_) == 0)
{
lean_dec(v_x_716_);
return v_x_717_;
}
else
{
lean_object* v_head_719_; lean_object* v_tail_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_731_; 
v_head_719_ = lean_ctor_get(v_x_718_, 0);
v_tail_720_ = lean_ctor_get(v_x_718_, 1);
v_isSharedCheck_731_ = !lean_is_exclusive(v_x_718_);
if (v_isSharedCheck_731_ == 0)
{
v___x_722_ = v_x_718_;
v_isShared_723_ = v_isSharedCheck_731_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_tail_720_);
lean_inc(v_head_719_);
lean_dec(v_x_718_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_731_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
lean_inc(v_x_716_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 5);
lean_ctor_set(v___x_722_, 1, v_x_716_);
lean_ctor_set(v___x_722_, 0, v_x_717_);
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_x_717_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_x_716_);
v___x_725_ = v_reuseFailAlloc_730_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = l_String_quote(v_head_719_);
v___x_727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
v___x_728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_725_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v_x_717_ = v___x_728_;
v_x_718_ = v_tail_720_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_dec(v_x_732_);
return v_x_733_;
}
else
{
lean_object* v_head_735_; lean_object* v_tail_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_747_; 
v_head_735_ = lean_ctor_get(v_x_734_, 0);
v_tail_736_ = lean_ctor_get(v_x_734_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_x_734_);
if (v_isSharedCheck_747_ == 0)
{
v___x_738_ = v_x_734_;
v_isShared_739_ = v_isSharedCheck_747_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_tail_736_);
lean_inc(v_head_735_);
lean_dec(v_x_734_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_747_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
lean_inc(v_x_732_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 5);
lean_ctor_set(v___x_738_, 1, v_x_732_);
lean_ctor_set(v___x_738_, 0, v_x_733_);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_x_733_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_x_732_);
v___x_741_ = v_reuseFailAlloc_746_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_742_ = l_String_quote(v_head_735_);
v___x_743_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
v___x_744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_741_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(v_x_732_, v___x_744_, v_tail_736_);
return v___x_745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_748_) == 0)
{
lean_object* v___x_750_; 
lean_dec(v_x_749_);
v___x_750_ = lean_box(0);
return v___x_750_;
}
else
{
lean_object* v_tail_751_; 
v_tail_751_ = lean_ctor_get(v_x_748_, 1);
if (lean_obj_tag(v_tail_751_) == 0)
{
lean_object* v_head_752_; lean_object* v___x_753_; 
lean_dec(v_x_749_);
v_head_752_ = lean_ctor_get(v_x_748_, 0);
lean_inc(v_head_752_);
lean_dec_ref_known(v_x_748_, 2);
v___x_753_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_752_);
return v___x_753_;
}
else
{
lean_object* v_head_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
lean_inc(v_tail_751_);
v_head_754_ = lean_ctor_get(v_x_748_, 0);
lean_inc(v_head_754_);
lean_dec_ref_known(v_x_748_, 2);
v___x_755_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_754_);
v___x_756_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(v_x_749_, v___x_755_, v_tail_751_);
return v___x_756_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0));
v___x_766_ = lean_string_length(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5);
v___x_768_ = lean_nat_to_int(v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(lean_object* v_xs_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_777_ = lean_array_get_size(v_xs_776_);
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_nat_dec_eq(v___x_777_, v___x_778_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_780_ = lean_array_to_list(v_xs_776_);
v___x_781_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3));
v___x_782_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(v___x_780_, v___x_781_);
v___x_783_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6);
v___x_784_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7));
v___x_785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v___x_782_);
v___x_786_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8));
v___x_787_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_783_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = l_Std_Format_fill(v___x_788_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; 
lean_dec_ref(v_xs_776_);
v___x_790_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10));
return v___x_790_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(11u);
v___x_801_ = lean_nat_to_int(v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg(lean_object* v_x_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_809_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_810_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3));
v___x_811_ = lean_obj_once(&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4, &l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4);
v___x_812_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_808_);
v___x_813_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = 0;
v___x_815_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set_uint8(v___x_815_, sizeof(void*)*1, v___x_814_);
v___x_816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_810_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_box(1);
v___x_820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6));
v___x_822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_809_);
v___x_824_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_827_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_828_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_825_);
v___x_829_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_830_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_826_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set_uint8(v___x_832_, sizeof(void*)*1, v___x_814_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr(lean_object* v_x_833_, lean_object* v_prec_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg(v_x_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___boxed(lean_object* v_x_836_, lean_object* v_prec_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_Http_Header_instReprTransferEncoding_repr(v_x_836_, v_prec_837_);
lean_dec(v_prec_837_);
return v_res_838_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object* v_te_841_){
_start:
{
lean_object* v___y_843_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_846_ = lean_array_get_size(v_te_841_);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_sub(v___x_846_, v___x_847_);
v___x_849_ = lean_nat_dec_lt(v___x_848_, v___x_846_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; 
lean_dec(v___x_848_);
v___x_850_ = lean_box(0);
v___y_843_ = v___x_850_;
goto v___jp_842_;
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_array_fget_borrowed(v_te_841_, v___x_848_);
lean_dec(v___x_848_);
lean_inc(v___x_851_);
v___x_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
v___y_843_ = v___x_852_;
goto v___jp_842_;
}
v___jp_842_:
{
lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_844_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v___x_845_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_843_, v___x_844_);
lean_dec(v___y_843_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_isChunked___boxed(lean_object* v_te_853_){
_start:
{
uint8_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_853_);
lean_dec_ref(v_te_853_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object* v_v_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v___x_858_; 
v___x_858_ = lean_box(0);
return v___x_858_;
}
else
{
lean_object* v_val_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_868_; 
v_val_859_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_868_ == 0)
{
v___x_861_ = v___x_857_;
v_isShared_862_ = v_isSharedCheck_868_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_val_859_);
lean_dec(v___x_857_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_868_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
uint8_t v___x_863_; 
v___x_863_ = l_Std_Http_Header_TransferEncoding_Validate(v_val_859_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; 
lean_del_object(v___x_861_);
lean_dec(v_val_859_);
v___x_864_ = lean_box(0);
return v___x_864_;
}
else
{
lean_object* v___x_866_; 
if (v_isShared_862_ == 0)
{
v___x_866_ = v___x_861_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_val_859_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_serialize(lean_object* v_te_869_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v_value_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_870_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_871_ = lean_array_to_list(v_te_869_);
v_value_872_ = l_String_intercalate(v___x_870_, v___x_871_);
v___x_873_ = l_Std_Http_Header_Name_transferEncoding;
v___x_874_ = l_Std_Http_Header_Value_ofString_x21(v_value_872_);
v___x_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___redArg(lean_object* v_x_894_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_895_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_896_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__3));
v___x_897_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_898_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_894_);
v___x_899_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = 0;
v___x_901_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*1, v___x_900_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_896_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_box(1);
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__5));
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_895_);
v___x_910_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_913_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_911_);
v___x_915_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_912_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set_uint8(v___x_918_, sizeof(void*)*1, v___x_900_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr(lean_object* v_x_919_, lean_object* v_prec_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Std_Http_Header_instReprConnection_repr___redArg(v_x_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___boxed(lean_object* v_x_922_, lean_object* v_prec_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Std_Http_Header_instReprConnection_repr(v_x_922_, v_prec_923_);
lean_dec(v_prec_923_);
return v_res_924_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(lean_object* v_token_927_, lean_object* v_as_928_, size_t v_i_929_, size_t v_stop_930_){
_start:
{
uint8_t v___x_931_; 
v___x_931_ = lean_usize_dec_eq(v_i_929_, v_stop_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_932_ = lean_array_uget_borrowed(v_as_928_, v_i_929_);
v___x_933_ = lean_string_dec_eq(v___x_932_, v_token_927_);
if (v___x_933_ == 0)
{
size_t v___x_934_; size_t v___x_935_; 
v___x_934_ = ((size_t)1ULL);
v___x_935_ = lean_usize_add(v_i_929_, v___x_934_);
v_i_929_ = v___x_935_;
goto _start;
}
else
{
return v___x_933_;
}
}
else
{
uint8_t v___x_937_; 
v___x_937_ = 0;
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(lean_object* v_token_938_, lean_object* v_as_939_, lean_object* v_i_940_, lean_object* v_stop_941_){
_start:
{
size_t v_i_boxed_942_; size_t v_stop_boxed_943_; uint8_t v_res_944_; lean_object* v_r_945_; 
v_i_boxed_942_ = lean_unbox_usize(v_i_940_);
lean_dec(v_i_940_);
v_stop_boxed_943_ = lean_unbox_usize(v_stop_941_);
lean_dec(v_stop_941_);
v_res_944_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_938_, v_as_939_, v_i_boxed_942_, v_stop_boxed_943_);
lean_dec_ref(v_as_939_);
lean_dec_ref(v_token_938_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_containsToken(lean_object* v_connection_946_, lean_object* v_token_947_){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = lean_array_get_size(v_connection_946_);
v___x_950_ = lean_nat_dec_lt(v___x_948_, v___x_949_);
if (v___x_950_ == 0)
{
lean_dec_ref(v_token_947_);
return v___x_950_;
}
else
{
lean_object* v___x_951_; 
v___x_951_ = lean_string_utf8_byte_size(v_token_947_);
if (v___x_950_ == 0)
{
lean_dec_ref(v_token_947_);
return v___x_950_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v_token_955_; size_t v___x_956_; size_t v___x_957_; uint8_t v___x_958_; 
v___x_952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_952_, 0, v_token_947_);
lean_ctor_set(v___x_952_, 1, v___x_948_);
lean_ctor_set(v___x_952_, 2, v___x_951_);
v___x_953_ = l_String_Slice_trimAscii(v___x_952_);
v___x_954_ = l_String_Slice_toString(v___x_953_);
lean_dec_ref(v___x_953_);
v_token_955_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_954_, v___x_948_);
v___x_956_ = ((size_t)0ULL);
v___x_957_ = lean_usize_of_nat(v___x_949_);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_955_, v_connection_946_, v___x_956_, v___x_957_);
lean_dec_ref(v_token_955_);
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_containsToken___boxed(lean_object* v_connection_959_, lean_object* v_token_960_){
_start:
{
uint8_t v_res_961_; lean_object* v_r_962_; 
v_res_961_ = l_Std_Http_Header_Connection_containsToken(v_connection_959_, v_token_960_);
lean_dec_ref(v_connection_959_);
v_r_962_ = lean_box(v_res_961_);
return v_r_962_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_shouldClose(lean_object* v_connection_964_){
_start:
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = ((lean_object*)(l_Std_Http_Header_Connection_shouldClose___closed__0));
v___x_966_ = l_Std_Http_Header_Connection_containsToken(v_connection_964_, v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_shouldClose___boxed(lean_object* v_connection_967_){
_start:
{
uint8_t v_res_968_; lean_object* v_r_969_; 
v_res_968_ = l_Std_Http_Header_Connection_shouldClose(v_connection_967_);
lean_dec_ref(v_connection_967_);
v_r_969_ = lean_box(v_res_968_);
return v_r_969_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(lean_object* v_as_970_, size_t v_i_971_, size_t v_stop_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = lean_usize_dec_eq(v_i_971_, v_stop_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_974_ = lean_array_uget_borrowed(v_as_970_, v_i_971_);
lean_inc(v___x_974_);
v___x_975_ = l_Std_Http_Internal_isToken(v___x_974_);
if (v___x_975_ == 0)
{
uint8_t v___x_976_; 
v___x_976_ = 1;
return v___x_976_;
}
else
{
size_t v___x_977_; size_t v___x_978_; 
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_add(v_i_971_, v___x_977_);
v_i_971_ = v___x_978_;
goto _start;
}
}
else
{
uint8_t v___x_980_; 
v___x_980_ = 0;
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(lean_object* v_as_981_, lean_object* v_i_982_, lean_object* v_stop_983_){
_start:
{
size_t v_i_boxed_984_; size_t v_stop_boxed_985_; uint8_t v_res_986_; lean_object* v_r_987_; 
v_i_boxed_984_ = lean_unbox_usize(v_i_982_);
lean_dec(v_i_982_);
v_stop_boxed_985_ = lean_unbox_usize(v_stop_983_);
lean_dec(v_stop_983_);
v_res_986_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_981_, v_i_boxed_984_, v_stop_boxed_985_);
lean_dec_ref(v_as_981_);
v_r_987_ = lean_box(v_res_986_);
return v_r_987_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_parse(lean_object* v_v_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v___x_990_; 
v___x_990_ = lean_box(0);
return v___x_990_;
}
else
{
lean_object* v_val_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1011_; 
v_val_991_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_993_ = v___x_989_;
v_isShared_994_ = v_isSharedCheck_1011_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_val_991_);
lean_dec(v___x_989_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1011_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_array_get_size(v_val_991_);
v___x_997_ = lean_nat_dec_lt(v___x_995_, v___x_996_);
if (v___x_997_ == 0)
{
lean_object* v___x_999_; 
if (v_isShared_994_ == 0)
{
v___x_999_ = v___x_993_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_val_991_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
else
{
if (v___x_997_ == 0)
{
lean_object* v___x_1002_; 
if (v_isShared_994_ == 0)
{
v___x_1002_ = v___x_993_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_val_991_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
size_t v___x_1004_; size_t v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = ((size_t)0ULL);
v___x_1005_ = lean_usize_of_nat(v___x_996_);
v___x_1006_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_val_991_, v___x_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1008_; 
if (v_isShared_994_ == 0)
{
v___x_1008_ = v___x_993_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_val_991_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
else
{
lean_object* v___x_1010_; 
lean_del_object(v___x_993_);
lean_dec(v_val_991_);
v___x_1010_ = lean_box(0);
return v___x_1010_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_serialize(lean_object* v_connection_1012_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_value_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1013_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_1014_ = lean_array_to_list(v_connection_1012_);
v_value_1015_ = l_String_intercalate(v___x_1013_, v___x_1014_);
v___x_1016_ = l_Std_Http_Header_Name_connection;
v___x_1017_ = l_Std_Http_Header_Value_ofString_x21(v_value_1015_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_unsigned_to_nat(8u);
v___x_1035_ = lean_nat_to_int(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_unsigned_to_nat(2u);
v___x_1037_ = lean_nat_to_int(v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___redArg(lean_object* v_x_1045_){
_start:
{
lean_object* v_host_1046_; lean_object* v_port_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1121_; 
v_host_1046_ = lean_ctor_get(v_x_1045_, 0);
v_port_1047_ = lean_ctor_get(v_x_1045_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_x_1045_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1049_ = v_x_1045_;
v_isShared_1050_ = v_isSharedCheck_1121_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_port_1047_);
lean_inc(v_host_1046_);
lean_dec(v_x_1045_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1121_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v_ctr_1057_; lean_object* v_a_1058_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_1052_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__3));
v___x_1053_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__4, &l_Std_Http_Header_instReprHost_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4);
v___x_1054_ = lean_unsigned_to_nat(0u);
v___x_1055_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__5, &l_Std_Http_Header_instReprHost_repr___redArg___closed__5_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5);
switch(lean_obj_tag(v_host_1046_))
{
case 0:
{
lean_object* v_name_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1100_; 
v_name_1091_ = lean_ctor_get(v_host_1046_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_host_1046_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1093_ = v_host_1046_;
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_name_1091_);
lean_dec(v_host_1046_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1095_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__9));
v___x_1096_ = l_String_quote(v_name_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 3);
lean_ctor_set(v___x_1093_, 0, v___x_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
v_ctr_1057_ = v___x_1095_;
v_a_1058_ = v___x_1098_;
goto v___jp_1056_;
}
}
}
case 1:
{
lean_object* v_ipv4_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1110_; 
v_ipv4_1101_ = lean_ctor_get(v_host_1046_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_host_1046_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1103_ = v_host_1046_;
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_ipv4_1101_);
lean_dec(v_host_1046_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1105_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__10));
v___x_1106_ = lean_uv_ntop_v4(v_ipv4_1101_);
lean_dec_ref(v_ipv4_1101_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set_tag(v___x_1103_, 3);
lean_ctor_set(v___x_1103_, 0, v___x_1106_);
v___x_1108_ = v___x_1103_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
v_ctr_1057_ = v___x_1105_;
v_a_1058_ = v___x_1108_;
goto v___jp_1056_;
}
}
}
default: 
{
lean_object* v_ipv6_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1120_; 
v_ipv6_1111_ = lean_ctor_get(v_host_1046_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_host_1046_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1113_ = v_host_1046_;
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_ipv6_1111_);
lean_dec(v_host_1046_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1115_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__11));
v___x_1116_ = lean_uv_ntop_v6(v_ipv6_1111_);
lean_dec_ref(v_ipv6_1111_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set_tag(v___x_1113_, 3);
lean_ctor_set(v___x_1113_, 0, v___x_1116_);
v___x_1118_ = v___x_1113_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
v_ctr_1057_ = v___x_1115_;
v_a_1058_ = v___x_1118_;
goto v___jp_1056_;
}
}
}
}
v___jp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1059_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__6));
v___x_1060_ = lean_string_append(v___x_1059_, v_ctr_1057_);
v___x_1061_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
v___x_1062_ = lean_box(1);
if (v_isShared_1050_ == 0)
{
lean_ctor_set_tag(v___x_1049_, 5);
lean_ctor_set(v___x_1049_, 1, v___x_1062_);
lean_ctor_set(v___x_1049_, 0, v___x_1061_);
v___x_1064_ = v___x_1049_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1090_, 1, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1065_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_a_1058_);
v___x_1066_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1055_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = 0;
v___x_1068_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*1, v___x_1067_);
v___x_1069_ = l_Repr_addAppParen(v___x_1068_, v___x_1054_);
v___x_1070_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1053_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set_uint8(v___x_1071_, sizeof(void*)*1, v___x_1067_);
v___x_1072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1052_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_1074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v___x_1062_);
v___x_1076_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__8));
v___x_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___x_1051_);
v___x_1079_ = l_Std_Http_URI_instReprPort_repr(v_port_1047_, v___x_1054_);
lean_dec(v_port_1047_);
v___x_1080_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1053_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*1, v___x_1067_);
v___x_1082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1078_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1084_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_1085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v___x_1082_);
v___x_1086_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_1087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1083_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
lean_ctor_set_uint8(v___x_1089_, sizeof(void*)*1, v___x_1067_);
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr(lean_object* v_x_1122_, lean_object* v_prec_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Std_Http_Header_instReprHost_repr___redArg(v_x_1122_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___boxed(lean_object* v_x_1125_, lean_object* v_prec_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Std_Http_Header_instReprHost_repr(v_x_1125_, v_prec_1126_);
lean_dec(v_prec_1126_);
return v_res_1127_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqHost_beq(lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
lean_object* v_host_1132_; lean_object* v_port_1133_; lean_object* v_host_1134_; lean_object* v_port_1135_; uint8_t v___x_1136_; 
v_host_1132_ = lean_ctor_get(v_x_1130_, 0);
v_port_1133_ = lean_ctor_get(v_x_1130_, 1);
v_host_1134_ = lean_ctor_get(v_x_1131_, 0);
v_port_1135_ = lean_ctor_get(v_x_1131_, 1);
v___x_1136_ = l_Std_Http_URI_instBEqHost_beq(v_host_1132_, v_host_1134_);
if (v___x_1136_ == 0)
{
return v___x_1136_;
}
else
{
uint8_t v___x_1137_; 
v___x_1137_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1133_, v_port_1135_);
return v___x_1137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqHost_beq___boxed(lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
uint8_t v_res_1140_; lean_object* v_r_1141_; 
v_res_1140_ = l_Std_Http_Header_instBEqHost_beq(v_x_1138_, v_x_1139_);
lean_dec_ref(v_x_1139_);
lean_dec_ref(v_x_1138_);
v_r_1141_ = lean_box(v_res_1140_);
return v_r_1141_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0(lean_object* v___x_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Std_Http_URI_Parser_parseHostHeader(v___x_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_pos_1150_; lean_object* v_array_1151_; lean_object* v_idx_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_pos_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_pos_1150_);
v_array_1151_ = lean_ctor_get(v_pos_1150_, 0);
v_idx_1152_ = lean_ctor_get(v_pos_1150_, 1);
v___x_1153_ = lean_byte_array_size(v_array_1151_);
v___x_1154_ = lean_nat_dec_lt(v_idx_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_dec(v_pos_1150_);
return v___x_1149_;
}
else
{
lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1162_; 
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; lean_object* v_unused_1164_; 
v_unused_1163_ = lean_ctor_get(v___x_1149_, 1);
lean_dec(v_unused_1163_);
v_unused_1164_ = lean_ctor_get(v___x_1149_, 0);
lean_dec(v_unused_1164_);
v___x_1156_ = v___x_1149_;
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
else
{
lean_dec(v___x_1149_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1162_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = ((lean_object*)(l_Std_Http_Header_Host_parse___lam__0___closed__1));
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 1);
lean_ctor_set(v___x_1156_, 1, v___x_1158_);
v___x_1160_ = v___x_1156_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_pos_1150_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0___boxed(lean_object* v___x_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Std_Http_Header_Host_parse___lam__0(v___x_1165_, v___y_1166_);
lean_dec_ref(v___x_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse(lean_object* v_v_1178_){
_start:
{
lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v_parsed_1181_; 
v___f_1179_ = ((lean_object*)(l_Std_Http_Header_Host_parse___closed__1));
v___x_1180_ = lean_string_to_utf8(v_v_1178_);
v_parsed_1181_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1179_, v___x_1180_);
if (lean_obj_tag(v_parsed_1181_) == 0)
{
lean_object* v___x_1182_; 
lean_dec_ref_known(v_parsed_1181_, 1);
v___x_1182_ = lean_box(0);
return v___x_1182_;
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1199_; 
v_a_1183_ = lean_ctor_get(v_parsed_1181_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_parsed_1181_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1185_ = v_parsed_1181_;
v_isShared_1186_ = v_isSharedCheck_1199_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v_parsed_1181_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1199_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_fst_1187_; lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1198_; 
v_fst_1187_ = lean_ctor_get(v_a_1183_, 0);
v_snd_1188_ = lean_ctor_get(v_a_1183_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_a_1183_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1190_ = v_a_1183_;
v_isShared_1191_ = v_isSharedCheck_1198_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_inc(v_fst_1187_);
lean_dec(v_a_1183_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1198_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_fst_1187_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_snd_1188_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1195_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1193_);
v___x_1195_ = v___x_1185_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___boxed(lean_object* v_v_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Std_Http_Header_Host_parse(v_v_1200_);
lean_dec_ref(v_v_1200_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_serialize(lean_object* v_host_1204_){
_start:
{
lean_object* v___y_1206_; lean_object* v___y_1210_; lean_object* v_port_1214_; 
v_port_1214_ = lean_ctor_get(v_host_1204_, 1);
switch(lean_obj_tag(v_port_1214_))
{
case 0:
{
lean_object* v_host_1215_; 
v_host_1215_ = lean_ctor_get(v_host_1204_, 0);
lean_inc_ref(v_host_1215_);
lean_dec_ref(v_host_1204_);
switch(lean_obj_tag(v_host_1215_))
{
case 0:
{
lean_object* v_name_1216_; lean_object* v___x_1217_; 
v_name_1216_ = lean_ctor_get(v_host_1215_, 0);
lean_inc_ref(v_name_1216_);
lean_dec_ref_known(v_host_1215_, 1);
v___x_1217_ = l_Std_Http_Header_Value_ofString_x21(v_name_1216_);
v___y_1206_ = v___x_1217_;
goto v___jp_1205_;
}
case 1:
{
lean_object* v_ipv4_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_ipv4_1218_ = lean_ctor_get(v_host_1215_, 0);
lean_inc_ref(v_ipv4_1218_);
lean_dec_ref_known(v_host_1215_, 1);
v___x_1219_ = lean_uv_ntop_v4(v_ipv4_1218_);
lean_dec_ref(v_ipv4_1218_);
v___x_1220_ = l_Std_Http_Header_Value_ofString_x21(v___x_1219_);
v___y_1206_ = v___x_1220_;
goto v___jp_1205_;
}
default: 
{
lean_object* v_ipv6_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_ipv6_1221_ = lean_ctor_get(v_host_1215_, 0);
lean_inc_ref(v_ipv6_1221_);
lean_dec_ref_known(v_host_1215_, 1);
v___x_1222_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1223_ = lean_uv_ntop_v6(v_ipv6_1221_);
lean_dec_ref(v_ipv6_1221_);
v___x_1224_ = lean_string_append(v___x_1222_, v___x_1223_);
lean_dec_ref(v___x_1223_);
v___x_1225_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1226_ = lean_string_append(v___x_1224_, v___x_1225_);
v___x_1227_ = l_Std_Http_Header_Value_ofString_x21(v___x_1226_);
v___y_1206_ = v___x_1227_;
goto v___jp_1205_;
}
}
}
case 1:
{
lean_object* v_host_1228_; 
v_host_1228_ = lean_ctor_get(v_host_1204_, 0);
lean_inc_ref(v_host_1228_);
lean_dec_ref(v_host_1204_);
switch(lean_obj_tag(v_host_1228_))
{
case 0:
{
lean_object* v_name_1229_; 
v_name_1229_ = lean_ctor_get(v_host_1228_, 0);
lean_inc_ref(v_name_1229_);
lean_dec_ref_known(v_host_1228_, 1);
v___y_1210_ = v_name_1229_;
goto v___jp_1209_;
}
case 1:
{
lean_object* v_ipv4_1230_; lean_object* v___x_1231_; 
v_ipv4_1230_ = lean_ctor_get(v_host_1228_, 0);
lean_inc_ref(v_ipv4_1230_);
lean_dec_ref_known(v_host_1228_, 1);
v___x_1231_ = lean_uv_ntop_v4(v_ipv4_1230_);
lean_dec_ref(v_ipv4_1230_);
v___y_1210_ = v___x_1231_;
goto v___jp_1209_;
}
default: 
{
lean_object* v_ipv6_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_ipv6_1232_ = lean_ctor_get(v_host_1228_, 0);
lean_inc_ref(v_ipv6_1232_);
lean_dec_ref_known(v_host_1228_, 1);
v___x_1233_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1234_ = lean_uv_ntop_v6(v_ipv6_1232_);
lean_dec_ref(v_ipv6_1232_);
v___x_1235_ = lean_string_append(v___x_1233_, v___x_1234_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1237_ = lean_string_append(v___x_1235_, v___x_1236_);
v___y_1210_ = v___x_1237_;
goto v___jp_1209_;
}
}
}
default: 
{
lean_object* v_host_1238_; uint16_t v_port_1239_; lean_object* v___y_1241_; 
lean_inc_ref(v_port_1214_);
v_host_1238_ = lean_ctor_get(v_host_1204_, 0);
lean_inc_ref(v_host_1238_);
lean_dec_ref(v_host_1204_);
v_port_1239_ = lean_ctor_get_uint16(v_port_1214_, 0);
lean_dec_ref_known(v_port_1214_, 0);
switch(lean_obj_tag(v_host_1238_))
{
case 0:
{
lean_object* v_name_1248_; 
v_name_1248_ = lean_ctor_get(v_host_1238_, 0);
lean_inc_ref(v_name_1248_);
lean_dec_ref_known(v_host_1238_, 1);
v___y_1241_ = v_name_1248_;
goto v___jp_1240_;
}
case 1:
{
lean_object* v_ipv4_1249_; lean_object* v___x_1250_; 
v_ipv4_1249_ = lean_ctor_get(v_host_1238_, 0);
lean_inc_ref(v_ipv4_1249_);
lean_dec_ref_known(v_host_1238_, 1);
v___x_1250_ = lean_uv_ntop_v4(v_ipv4_1249_);
lean_dec_ref(v_ipv4_1249_);
v___y_1241_ = v___x_1250_;
goto v___jp_1240_;
}
default: 
{
lean_object* v_ipv6_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_ipv6_1251_ = lean_ctor_get(v_host_1238_, 0);
lean_inc_ref(v_ipv6_1251_);
lean_dec_ref_known(v_host_1238_, 1);
v___x_1252_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1253_ = lean_uv_ntop_v6(v_ipv6_1251_);
lean_dec_ref(v_ipv6_1251_);
v___x_1254_ = lean_string_append(v___x_1252_, v___x_1253_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1256_ = lean_string_append(v___x_1254_, v___x_1255_);
v___y_1241_ = v___x_1256_;
goto v___jp_1240_;
}
}
v___jp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1242_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1243_ = lean_string_append(v___y_1241_, v___x_1242_);
v___x_1244_ = lean_uint16_to_nat(v_port_1239_);
v___x_1245_ = l_Nat_reprFast(v___x_1244_);
v___x_1246_ = lean_string_append(v___x_1243_, v___x_1245_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = l_Std_Http_Header_Value_ofString_x21(v___x_1246_);
v___y_1206_ = v___x_1247_;
goto v___jp_1205_;
}
}
}
v___jp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__0));
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___y_1206_);
return v___x_1208_;
}
v___jp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1212_ = lean_string_append(v___y_1210_, v___x_1211_);
v___x_1213_ = l_Std_Http_Header_Value_ofString_x21(v___x_1212_);
v___y_1206_ = v___x_1213_;
goto v___jp_1205_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1269_ = ((lean_object*)(l_Std_Http_Header_instReprExpect_repr___redArg___closed__1));
v___x_1270_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1271_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1270_);
lean_ctor_set(v___x_1271_, 1, v___x_1269_);
return v___x_1271_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3(void){
_start:
{
uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = 0;
v___x_1273_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__2, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__2_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2);
v___x_1274_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set_uint8(v___x_1274_, sizeof(void*)*1, v___x_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg(){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__3, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__3_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___boxed(lean_object* v___dummy_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v_res_1278_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___closed__0(void){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr(lean_object* v_x_1280_, lean_object* v_prec_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___closed__0, &l_Std_Http_Header_instReprExpect_repr___closed__0_once, _init_l_Std_Http_Header_instReprExpect_repr___closed__0);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___boxed(lean_object* v_x_1283_, lean_object* v_prec_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Std_Http_Header_instReprExpect_repr(v_x_1283_, v_prec_1284_);
lean_dec(v_prec_1284_);
return v_res_1285_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq___redArg(){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = 1;
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___redArg___boxed(lean_object* v___dummy_1290_){
_start:
{
uint8_t v_res_1291_; lean_object* v_r_1292_; 
v_res_1291_ = l_Std_Http_Header_instBEqExpect_beq___redArg();
v_r_1292_ = lean_box(v_res_1291_);
return v_r_1292_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq(lean_object* v_x_1293_, lean_object* v_y_1294_){
_start:
{
uint8_t v___x_1295_; 
v___x_1295_ = 1;
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___boxed(lean_object* v_x_1296_, lean_object* v_y_1297_){
_start:
{
uint8_t v_res_1298_; lean_object* v_r_1299_; 
v_res_1298_ = l_Std_Http_Header_instBEqExpect_beq(v_x_1296_, v_y_1297_);
v_r_1299_ = lean_box(v_res_1298_);
return v_r_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_parse(lean_object* v_v_1305_){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v_normalized_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_string_utf8_byte_size(v_v_1305_);
v___x_1308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1308_, 0, v_v_1305_);
lean_ctor_set(v___x_1308_, 1, v___x_1306_);
lean_ctor_set(v___x_1308_, 2, v___x_1307_);
v___x_1309_ = l_String_Slice_trimAscii(v___x_1308_);
v___x_1310_ = l_String_Slice_toString(v___x_1309_);
lean_dec_ref(v___x_1309_);
v_normalized_1311_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_1310_, v___x_1306_);
v___x_1312_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1313_ = lean_string_dec_eq(v_normalized_1311_, v___x_1312_);
lean_dec_ref(v_normalized_1311_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_box(0);
return v___x_1314_;
}
else
{
lean_object* v___x_1315_; 
v___x_1315_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__1));
return v___x_1315_;
}
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1317_ = l_Std_Http_Header_Value_ofString_x21(v___x_1316_);
return v___x_1317_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__0, &l_Std_Http_Header_Expect_serialize___redArg___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0);
v___x_1319_ = l_Std_Http_Header_Name_expect;
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___x_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg(){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__1, &l_Std_Http_Header_Expect_serialize___redArg___closed__1_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg___boxed(lean_object* v___dummy_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Std_Http_Header_Expect_serialize___redArg();
return v_res_1324_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___closed__0(void){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Std_Http_Header_Expect_serialize___redArg();
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize(lean_object* v_x_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___closed__0, &l_Std_Http_Header_Expect_serialize___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___closed__0);
return v___x_1327_;
}
}
lean_object* runtime_initialize_Std_Http_Data_URI(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers_Name(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers_Value(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Headers_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers_Value(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Headers_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Http_Data_URI(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Headers_Name(uint8_t builtin);
lean_object* initialize_Std_Http_Data_Headers_Value(uint8_t builtin);
lean_object* initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Headers_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Http_Data_URI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Headers_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Http_Data_Headers_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Headers_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Headers_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Headers_Basic(builtin);
}
#ifdef __cplusplus
}
#endif

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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
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
static const lean_string_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4_value;
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object*, lean_object*);
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
uint8_t v_decide_49_; 
v_decide_49_ = lean_nat_dec_eq(v_searcher_45_, v___x_5_);
if (v_decide_49_ == 0)
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
lean_object* v___x_33_; uint32_t v___x_34_; uint32_t v___x_35_; uint8_t v___x_36_; 
v___x_33_ = lean_string_utf8_extract_fast(v_fst_4_, v_startInclusive_31_, v_endExclusive_32_);
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
uint32_t v___x_1381__boxed_79_; lean_object* v_res_80_; 
v___x_1381__boxed_79_ = lean_unbox_uint32(v___x_73_);
lean_dec(v___x_73_);
v_res_80_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(v___x_68_, v___x_69_, v___x_70_, v_fst_71_, v___x_72_, v___x_1381__boxed_79_, v___x_74_, v_it_75_, v_acc_76_, v_hP_77_, v_recur_78_);
lean_dec_ref(v___x_74_);
lean_dec_ref(v_fst_71_);
lean_dec(v___x_70_);
lean_dec(v___x_69_);
lean_dec_ref(v___x_68_);
return v_res_80_;
}
}
static lean_object* _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_86_; lean_object* v___x_87_; 
v___x_86_ = 45;
v___x_87_ = lean_box_uint32(v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1(lean_object* v_h_88_, lean_object* v_buffer_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_serialize_91_; lean_object* v___x_92_; lean_object* v_fst_93_; lean_object* v_snd_94_; lean_object* v___y_96_; lean_object* v___f_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_it_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___f_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_serialize_91_ = lean_ctor_get(v_h_88_, 1);
lean_inc_ref(v_serialize_91_);
lean_dec_ref(v_h_88_);
v___x_92_ = lean_apply_1(v_serialize_91_, v_a_90_);
v_fst_93_ = lean_ctor_get(v___x_92_, 0);
lean_inc_n(v_fst_93_, 2);
v_snd_94_ = lean_ctor_get(v___x_92_, 1);
lean_inc(v_snd_94_);
lean_dec_ref(v___x_92_);
v___f_115_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2));
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_string_utf8_byte_size(v_fst_93_);
v___x_118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_118_, 0, v_fst_93_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
lean_ctor_set(v___x_118_, 2, v___x_117_);
lean_inc_ref(v___x_118_);
v_it_119_ = l_String_Slice_splitToSubslice___redArg(v___x_118_, v___f_115_);
v___x_120_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3));
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1;
v___f_123_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_123_, 0, v___x_120_);
lean_closure_set(v___f_123_, 1, v___x_116_);
lean_closure_set(v___f_123_, 2, v___x_121_);
lean_closure_set(v___f_123_, 3, v_fst_93_);
lean_closure_set(v___f_123_, 4, v___x_117_);
lean_closure_set(v___f_123_, 5, v___x_122_);
lean_closure_set(v___f_123_, 6, v___x_118_);
v___x_124_ = lean_box(0);
v___x_125_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_123_, v_it_119_, v___x_124_, lean_box(0));
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v___x_126_; 
v___x_126_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4));
v___y_96_ = v___x_126_;
goto v___jp_95_;
}
else
{
lean_object* v_val_127_; 
v_val_127_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_val_127_);
lean_dec_ref_known(v___x_125_, 1);
v___y_96_ = v_val_127_;
goto v___jp_95_;
}
v___jp_95_:
{
lean_object* v_data_97_; lean_object* v_size_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_114_; 
v_data_97_ = lean_ctor_get(v_buffer_89_, 0);
v_size_98_ = lean_ctor_get(v_buffer_89_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_buffer_89_);
if (v_isSharedCheck_114_ == 0)
{
v___x_100_ = v_buffer_89_;
v_isShared_101_ = v_isSharedCheck_114_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_size_98_);
lean_inc(v_data_97_);
lean_dec(v_buffer_89_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_114_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_102_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0));
v___x_103_ = lean_string_append(v___y_96_, v___x_102_);
v___x_104_ = lean_string_append(v___x_103_, v_snd_94_);
lean_dec(v_snd_94_);
v___x_105_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1));
v___x_106_ = lean_string_append(v___x_104_, v___x_105_);
v___x_107_ = lean_string_to_utf8(v___x_106_);
lean_dec_ref(v___x_106_);
lean_inc_ref(v___x_107_);
v___x_108_ = lean_array_push(v_data_97_, v___x_107_);
v___x_109_ = lean_byte_array_size(v___x_107_);
lean_dec_ref(v___x_107_);
v___x_110_ = lean_nat_add(v_size_98_, v___x_109_);
lean_dec(v_size_98_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 1, v___x_110_);
lean_ctor_set(v___x_100_, 0, v___x_108_);
v___x_112_ = v___x_100_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg(lean_object* v_h_128_){
_start:
{
lean_object* v___f_129_; 
v___f_129_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1), 3, 1);
lean_closure_set(v___f_129_, 0, v_h_128_);
return v___f_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader(lean_object* v_00_u03b1_130_, lean_object* v_h_131_){
_start:
{
lean_object* v___f_132_; 
v___f_132_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1), 3, 1);
lean_closure_set(v___f_132_, 0, v_h_131_);
return v___f_132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg(){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___closed__0));
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___boxed(lean_object* v___dummy_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg();
return v_res_138_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0(void){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg();
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(lean_object* v_s_140_){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(lean_object* v_s_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v_s_142_);
lean_dec_ref(v_s_142_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(lean_object* v_s_144_, lean_object* v_p_145_){
_start:
{
uint32_t v___y_147_; lean_object* v___x_152_; uint8_t v_decide_153_; 
v___x_152_ = lean_string_utf8_byte_size(v_s_144_);
v_decide_153_ = lean_nat_dec_eq(v_p_145_, v___x_152_);
if (v_decide_153_ == 0)
{
uint32_t v___x_154_; uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_154_ = lean_string_utf8_get_fast(v_s_144_, v_p_145_);
v___x_155_ = 65;
v___x_156_ = lean_uint32_dec_le(v___x_155_, v___x_154_);
if (v___x_156_ == 0)
{
v___y_147_ = v___x_154_;
goto v___jp_146_;
}
else
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 90;
v___x_158_ = lean_uint32_dec_le(v___x_154_, v___x_157_);
if (v___x_158_ == 0)
{
v___y_147_ = v___x_154_;
goto v___jp_146_;
}
else
{
uint32_t v___x_159_; uint32_t v___x_160_; 
v___x_159_ = 32;
v___x_160_ = lean_uint32_add(v___x_154_, v___x_159_);
v___y_147_ = v___x_160_;
goto v___jp_146_;
}
}
}
else
{
lean_dec(v_p_145_);
return v_s_144_;
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_inc(v_p_145_);
v___x_148_ = lean_string_utf8_set(v_s_144_, v_p_145_, v___y_147_);
v___x_149_ = l_Char_utf8Size(v___y_147_);
v___x_150_ = lean_nat_add(v_p_145_, v___x_149_);
lean_dec(v___x_149_);
lean_dec(v_p_145_);
v_s_144_ = v___x_148_;
v_p_145_ = v___x_150_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t v_sz_161_, size_t v_i_162_, lean_object* v_bs_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = lean_usize_dec_lt(v_i_162_, v_sz_161_);
if (v___x_164_ == 0)
{
return v_bs_163_;
}
else
{
lean_object* v_v_165_; lean_object* v___x_166_; lean_object* v_bs_x27_167_; lean_object* v___x_168_; lean_object* v___x_169_; size_t v___x_170_; size_t v___x_171_; lean_object* v___x_172_; 
v_v_165_ = lean_array_uget(v_bs_163_, v_i_162_);
v___x_166_ = lean_unsigned_to_nat(0u);
v_bs_x27_167_ = lean_array_uset(v_bs_163_, v_i_162_, v___x_166_);
v___x_168_ = l_String_Slice_toString(v_v_165_);
lean_dec(v_v_165_);
v___x_169_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_168_, v___x_166_);
v___x_170_ = ((size_t)1ULL);
v___x_171_ = lean_usize_add(v_i_162_, v___x_170_);
v___x_172_ = lean_array_uset(v_bs_x27_167_, v_i_162_, v___x_169_);
v_i_162_ = v___x_171_;
v_bs_163_ = v___x_172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(lean_object* v_sz_174_, lean_object* v_i_175_, lean_object* v_bs_176_){
_start:
{
size_t v_sz_boxed_177_; size_t v_i_boxed_178_; lean_object* v_res_179_; 
v_sz_boxed_177_ = lean_unbox_usize(v_sz_174_);
lean_dec(v_sz_174_);
v_i_boxed_178_ = lean_unbox_usize(v_i_175_);
lean_dec(v_i_175_);
v_res_179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_boxed_177_, v_i_boxed_178_, v_bs_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(lean_object* v___x_180_, lean_object* v___x_181_, lean_object* v___x_182_, lean_object* v_a_183_, lean_object* v_b_184_){
_start:
{
lean_object* v_it_186_; lean_object* v_startInclusive_187_; lean_object* v_endExclusive_188_; 
if (lean_obj_tag(v_a_183_) == 0)
{
lean_object* v_currPos_193_; lean_object* v_searcher_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_223_; 
v_currPos_193_ = lean_ctor_get(v_a_183_, 0);
v_searcher_194_ = lean_ctor_get(v_a_183_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_a_183_);
if (v_isSharedCheck_223_ == 0)
{
v___x_196_ = v_a_183_;
v_isShared_197_ = v_isSharedCheck_223_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_searcher_194_);
lean_inc(v_currPos_193_);
lean_dec(v_a_183_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_223_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_str_198_; lean_object* v_startInclusive_199_; lean_object* v_endExclusive_200_; lean_object* v___x_201_; uint8_t v_decide_202_; 
v_str_198_ = lean_ctor_get(v___x_181_, 0);
v_startInclusive_199_ = lean_ctor_get(v___x_181_, 1);
v_endExclusive_200_ = lean_ctor_get(v___x_181_, 2);
v___x_201_ = lean_nat_sub(v_endExclusive_200_, v_startInclusive_199_);
v_decide_202_ = lean_nat_dec_eq(v_searcher_194_, v___x_201_);
lean_dec(v___x_201_);
if (v_decide_202_ == 0)
{
lean_object* v___x_203_; uint32_t v___x_204_; uint32_t v___x_205_; uint8_t v___x_206_; 
v___x_203_ = lean_nat_add(v_startInclusive_199_, v_searcher_194_);
v___x_204_ = lean_string_utf8_get_fast(v_str_198_, v___x_203_);
v___x_205_ = 44;
v___x_206_ = lean_uint32_dec_eq(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
lean_dec(v_searcher_194_);
v___x_207_ = lean_string_utf8_next_fast(v_str_198_, v___x_203_);
lean_dec(v___x_203_);
v___x_208_ = lean_nat_sub(v___x_207_, v_startInclusive_199_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v___x_208_);
v___x_210_ = v___x_196_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_currPos_193_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_212_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
v_a_183_ = v___x_210_;
goto _start;
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_slice_216_; lean_object* v_nextIt_218_; 
v___x_213_ = lean_string_utf8_next_fast(v_str_198_, v___x_203_);
v___x_214_ = lean_nat_sub(v___x_213_, v___x_203_);
lean_dec(v___x_203_);
v___x_215_ = lean_nat_add(v_searcher_194_, v___x_214_);
lean_dec(v___x_214_);
v_slice_216_ = l_String_Slice_subslice_x21(v___x_181_, v_currPos_193_, v_searcher_194_);
lean_inc(v___x_215_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v___x_215_);
lean_ctor_set(v___x_196_, 0, v___x_215_);
v_nextIt_218_ = v___x_196_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_215_);
v_nextIt_218_ = v_reuseFailAlloc_221_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v_startInclusive_219_; lean_object* v_endExclusive_220_; 
v_startInclusive_219_ = lean_ctor_get(v_slice_216_, 0);
lean_inc(v_startInclusive_219_);
v_endExclusive_220_ = lean_ctor_get(v_slice_216_, 1);
lean_inc(v_endExclusive_220_);
lean_dec_ref(v_slice_216_);
v_it_186_ = v_nextIt_218_;
v_startInclusive_187_ = v_startInclusive_219_;
v_endExclusive_188_ = v_endExclusive_220_;
goto v___jp_185_;
}
}
}
else
{
lean_object* v___x_222_; 
lean_del_object(v___x_196_);
lean_dec(v_searcher_194_);
v___x_222_ = lean_box(1);
lean_inc(v___x_182_);
v_it_186_ = v___x_222_;
v_startInclusive_187_ = v_currPos_193_;
v_endExclusive_188_ = v___x_182_;
goto v___jp_185_;
}
}
}
else
{
lean_dec(v___x_182_);
lean_dec_ref(v___x_180_);
return v_b_184_;
}
v___jp_185_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_inc_ref(v___x_180_);
v___x_189_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_189_, 0, v___x_180_);
lean_ctor_set(v___x_189_, 1, v_startInclusive_187_);
lean_ctor_set(v___x_189_, 2, v_endExclusive_188_);
v___x_190_ = l_String_Slice_trimAscii(v___x_189_);
v___x_191_ = lean_array_push(v_b_184_, v___x_190_);
v_a_183_ = v_it_186_;
v_b_184_ = v___x_191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(lean_object* v___x_224_, lean_object* v___x_225_, lean_object* v___x_226_, lean_object* v_a_227_, lean_object* v_b_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_224_, v___x_225_, v___x_226_, v_a_227_, v_b_228_);
lean_dec_ref(v___x_225_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(lean_object* v___x_230_, lean_object* v___x_231_, lean_object* v___x_232_, lean_object* v_a_233_, lean_object* v_b_234_){
_start:
{
lean_object* v_it_236_; lean_object* v_startInclusive_237_; lean_object* v_endExclusive_238_; 
if (lean_obj_tag(v_a_233_) == 0)
{
lean_object* v_currPos_243_; lean_object* v_searcher_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_273_; 
v_currPos_243_ = lean_ctor_get(v_a_233_, 0);
v_searcher_244_ = lean_ctor_get(v_a_233_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_a_233_);
if (v_isSharedCheck_273_ == 0)
{
v___x_246_ = v_a_233_;
v_isShared_247_ = v_isSharedCheck_273_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_searcher_244_);
lean_inc(v_currPos_243_);
lean_dec(v_a_233_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_273_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_str_248_; lean_object* v_startInclusive_249_; lean_object* v_endExclusive_250_; lean_object* v___x_251_; uint8_t v_decide_252_; 
v_str_248_ = lean_ctor_get(v___x_231_, 0);
v_startInclusive_249_ = lean_ctor_get(v___x_231_, 1);
v_endExclusive_250_ = lean_ctor_get(v___x_231_, 2);
v___x_251_ = lean_nat_sub(v_endExclusive_250_, v_startInclusive_249_);
v_decide_252_ = lean_nat_dec_eq(v_searcher_244_, v___x_251_);
lean_dec(v___x_251_);
if (v_decide_252_ == 0)
{
lean_object* v___x_253_; uint32_t v___x_254_; uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_253_ = lean_nat_add(v_startInclusive_249_, v_searcher_244_);
v___x_254_ = lean_string_utf8_get_fast(v_str_248_, v___x_253_);
v___x_255_ = 44;
v___x_256_ = lean_uint32_dec_eq(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
lean_dec(v_searcher_244_);
v___x_257_ = lean_string_utf8_next_fast(v_str_248_, v___x_253_);
lean_dec(v___x_253_);
v___x_258_ = lean_nat_sub(v___x_257_, v_startInclusive_249_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v___x_258_);
v___x_260_ = v___x_246_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_currPos_243_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_262_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_261_; 
v___x_261_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_230_, v___x_231_, v___x_232_, v___x_260_, v_b_234_);
return v___x_261_;
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v_slice_266_; lean_object* v_nextIt_268_; 
v___x_263_ = lean_string_utf8_next_fast(v_str_248_, v___x_253_);
v___x_264_ = lean_nat_sub(v___x_263_, v___x_253_);
lean_dec(v___x_253_);
v___x_265_ = lean_nat_add(v_searcher_244_, v___x_264_);
lean_dec(v___x_264_);
v_slice_266_ = l_String_Slice_subslice_x21(v___x_231_, v_currPos_243_, v_searcher_244_);
lean_inc(v___x_265_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v___x_265_);
lean_ctor_set(v___x_246_, 0, v___x_265_);
v_nextIt_268_ = v___x_246_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_265_);
v_nextIt_268_ = v_reuseFailAlloc_271_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v_startInclusive_269_; lean_object* v_endExclusive_270_; 
v_startInclusive_269_ = lean_ctor_get(v_slice_266_, 0);
lean_inc(v_startInclusive_269_);
v_endExclusive_270_ = lean_ctor_get(v_slice_266_, 1);
lean_inc(v_endExclusive_270_);
lean_dec_ref(v_slice_266_);
v_it_236_ = v_nextIt_268_;
v_startInclusive_237_ = v_startInclusive_269_;
v_endExclusive_238_ = v_endExclusive_270_;
goto v___jp_235_;
}
}
}
else
{
lean_object* v___x_272_; 
lean_del_object(v___x_246_);
lean_dec(v_searcher_244_);
v___x_272_ = lean_box(1);
lean_inc(v___x_232_);
v_it_236_ = v___x_272_;
v_startInclusive_237_ = v_currPos_243_;
v_endExclusive_238_ = v___x_232_;
goto v___jp_235_;
}
}
}
else
{
lean_dec(v___x_232_);
lean_dec_ref(v___x_230_);
return v_b_234_;
}
v___jp_235_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc_ref(v___x_230_);
v___x_239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_239_, 0, v___x_230_);
lean_ctor_set(v___x_239_, 1, v_startInclusive_237_);
lean_ctor_set(v___x_239_, 2, v_endExclusive_238_);
v___x_240_ = l_String_Slice_trimAscii(v___x_239_);
v___x_241_ = lean_array_push(v_b_234_, v___x_240_);
v___x_242_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_230_, v___x_231_, v___x_232_, v_it_236_, v___x_241_);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(lean_object* v___x_274_, lean_object* v___x_275_, lean_object* v___x_276_, lean_object* v_a_277_, lean_object* v_b_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_274_, v___x_275_, v___x_276_, v_a_277_, v_b_278_);
lean_dec_ref(v___x_275_);
return v_res_279_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object* v___x_280_, lean_object* v___x_281_, lean_object* v___x_282_, lean_object* v_a_283_, uint8_t v_b_284_){
_start:
{
if (lean_obj_tag(v_a_283_) == 0)
{
lean_object* v_currPos_285_; lean_object* v_searcher_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_329_; 
v_currPos_285_ = lean_ctor_get(v_a_283_, 0);
v_searcher_286_ = lean_ctor_get(v_a_283_, 1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_a_283_);
if (v_isSharedCheck_329_ == 0)
{
v___x_288_ = v_a_283_;
v_isShared_289_ = v_isSharedCheck_329_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_searcher_286_);
lean_inc(v_currPos_285_);
lean_dec(v_a_283_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_329_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_str_290_; lean_object* v_startInclusive_291_; lean_object* v_endExclusive_292_; uint8_t v___x_293_; lean_object* v_it_295_; lean_object* v_startInclusive_296_; lean_object* v_endExclusive_297_; lean_object* v___x_307_; uint8_t v_decide_308_; 
v_str_290_ = lean_ctor_get(v___x_281_, 0);
v_startInclusive_291_ = lean_ctor_get(v___x_281_, 1);
v_endExclusive_292_ = lean_ctor_get(v___x_281_, 2);
v___x_293_ = 1;
v___x_307_ = lean_nat_sub(v_endExclusive_292_, v_startInclusive_291_);
v_decide_308_ = lean_nat_dec_eq(v_searcher_286_, v___x_307_);
lean_dec(v___x_307_);
if (v_decide_308_ == 0)
{
lean_object* v___x_309_; uint32_t v___x_310_; uint32_t v___x_311_; uint8_t v___x_312_; 
v___x_309_ = lean_nat_add(v_startInclusive_291_, v_searcher_286_);
v___x_310_ = lean_string_utf8_get_fast(v_str_290_, v___x_309_);
v___x_311_ = 44;
v___x_312_ = lean_uint32_dec_eq(v___x_310_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
lean_dec(v_searcher_286_);
v___x_313_ = lean_string_utf8_next_fast(v_str_290_, v___x_309_);
lean_dec(v___x_309_);
v___x_314_ = lean_nat_sub(v___x_313_, v_startInclusive_291_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_314_);
v___x_316_ = v___x_288_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_currPos_285_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_318_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v_a_283_ = v___x_316_;
goto _start;
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_slice_322_; lean_object* v_nextIt_324_; 
v___x_319_ = lean_string_utf8_next_fast(v_str_290_, v___x_309_);
v___x_320_ = lean_nat_sub(v___x_319_, v___x_309_);
lean_dec(v___x_309_);
v___x_321_ = lean_nat_add(v_searcher_286_, v___x_320_);
lean_dec(v___x_320_);
v_slice_322_ = l_String_Slice_subslice_x21(v___x_281_, v_currPos_285_, v_searcher_286_);
lean_inc(v___x_321_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_321_);
lean_ctor_set(v___x_288_, 0, v___x_321_);
v_nextIt_324_ = v___x_288_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_321_);
v_nextIt_324_ = v_reuseFailAlloc_327_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v_startInclusive_325_; lean_object* v_endExclusive_326_; 
v_startInclusive_325_ = lean_ctor_get(v_slice_322_, 0);
lean_inc(v_startInclusive_325_);
v_endExclusive_326_ = lean_ctor_get(v_slice_322_, 1);
lean_inc(v_endExclusive_326_);
lean_dec_ref(v_slice_322_);
v_it_295_ = v_nextIt_324_;
v_startInclusive_296_ = v_startInclusive_325_;
v_endExclusive_297_ = v_endExclusive_326_;
goto v___jp_294_;
}
}
}
else
{
lean_object* v___x_328_; 
lean_del_object(v___x_288_);
lean_dec(v_searcher_286_);
v___x_328_ = lean_box(1);
lean_inc(v___x_282_);
v_it_295_ = v___x_328_;
v_startInclusive_296_ = v_currPos_285_;
v_endExclusive_297_ = v___x_282_;
goto v___jp_294_;
}
v___jp_294_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_startInclusive_300_; lean_object* v_endExclusive_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
lean_inc_ref(v___x_280_);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v___x_280_);
lean_ctor_set(v___x_298_, 1, v_startInclusive_296_);
lean_ctor_set(v___x_298_, 2, v_endExclusive_297_);
v___x_299_ = l_String_Slice_trimAscii(v___x_298_);
v_startInclusive_300_ = lean_ctor_get(v___x_299_, 1);
lean_inc(v_startInclusive_300_);
v_endExclusive_301_ = lean_ctor_get(v___x_299_, 2);
lean_inc(v_endExclusive_301_);
lean_dec_ref(v___x_299_);
v___x_302_ = lean_nat_sub(v_endExclusive_301_, v_startInclusive_300_);
lean_dec(v_startInclusive_300_);
lean_dec(v_endExclusive_301_);
v___x_303_ = lean_unsigned_to_nat(0u);
v___x_304_ = lean_nat_dec_eq(v___x_302_, v___x_303_);
lean_dec(v___x_302_);
if (v___x_304_ == 0)
{
v_a_283_ = v_it_295_;
v_b_284_ = v___x_293_;
goto _start;
}
else
{
uint8_t v___x_306_; 
lean_dec(v_it_295_);
lean_dec(v___x_282_);
lean_dec_ref(v___x_280_);
v___x_306_ = 0;
return v___x_306_;
}
}
}
}
else
{
lean_dec(v___x_282_);
lean_dec_ref(v___x_280_);
return v_b_284_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object* v___x_330_, lean_object* v___x_331_, lean_object* v___x_332_, lean_object* v_a_333_, lean_object* v_b_334_){
_start:
{
uint8_t v_b_boxed_335_; uint8_t v_res_336_; lean_object* v_r_337_; 
v_b_boxed_335_ = lean_unbox(v_b_334_);
v_res_336_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_330_, v___x_331_, v___x_332_, v_a_333_, v_b_boxed_335_);
lean_dec_ref(v___x_331_);
v_r_337_ = lean_box(v_res_336_);
return v_r_337_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object* v___x_338_, lean_object* v___x_339_, lean_object* v___x_340_, lean_object* v_a_341_, uint8_t v_b_342_){
_start:
{
if (lean_obj_tag(v_a_341_) == 0)
{
lean_object* v_currPos_343_; lean_object* v_searcher_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_387_; 
v_currPos_343_ = lean_ctor_get(v_a_341_, 0);
v_searcher_344_ = lean_ctor_get(v_a_341_, 1);
v_isSharedCheck_387_ = !lean_is_exclusive(v_a_341_);
if (v_isSharedCheck_387_ == 0)
{
v___x_346_ = v_a_341_;
v_isShared_347_ = v_isSharedCheck_387_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_searcher_344_);
lean_inc(v_currPos_343_);
lean_dec(v_a_341_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_387_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_str_348_; lean_object* v_startInclusive_349_; lean_object* v_endExclusive_350_; uint8_t v___x_351_; lean_object* v_it_353_; lean_object* v_startInclusive_354_; lean_object* v_endExclusive_355_; lean_object* v___x_365_; uint8_t v_decide_366_; 
v_str_348_ = lean_ctor_get(v___x_339_, 0);
v_startInclusive_349_ = lean_ctor_get(v___x_339_, 1);
v_endExclusive_350_ = lean_ctor_get(v___x_339_, 2);
v___x_351_ = 1;
v___x_365_ = lean_nat_sub(v_endExclusive_350_, v_startInclusive_349_);
v_decide_366_ = lean_nat_dec_eq(v_searcher_344_, v___x_365_);
lean_dec(v___x_365_);
if (v_decide_366_ == 0)
{
lean_object* v___x_367_; uint32_t v___x_368_; uint32_t v___x_369_; uint8_t v___x_370_; 
v___x_367_ = lean_nat_add(v_startInclusive_349_, v_searcher_344_);
v___x_368_ = lean_string_utf8_get_fast(v_str_348_, v___x_367_);
v___x_369_ = 44;
v___x_370_ = lean_uint32_dec_eq(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
lean_dec(v_searcher_344_);
v___x_371_ = lean_string_utf8_next_fast(v_str_348_, v___x_367_);
lean_dec(v___x_367_);
v___x_372_ = lean_nat_sub(v___x_371_, v_startInclusive_349_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_372_);
v___x_374_ = v___x_346_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_currPos_343_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_376_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
uint8_t v___x_375_; 
v___x_375_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_338_, v___x_339_, v___x_340_, v___x_374_, v_b_342_);
return v___x_375_;
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v_slice_380_; lean_object* v_nextIt_382_; 
v___x_377_ = lean_string_utf8_next_fast(v_str_348_, v___x_367_);
v___x_378_ = lean_nat_sub(v___x_377_, v___x_367_);
lean_dec(v___x_367_);
v___x_379_ = lean_nat_add(v_searcher_344_, v___x_378_);
lean_dec(v___x_378_);
v_slice_380_ = l_String_Slice_subslice_x21(v___x_339_, v_currPos_343_, v_searcher_344_);
lean_inc(v___x_379_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_379_);
lean_ctor_set(v___x_346_, 0, v___x_379_);
v_nextIt_382_ = v___x_346_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v___x_379_);
v_nextIt_382_ = v_reuseFailAlloc_385_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_object* v_startInclusive_383_; lean_object* v_endExclusive_384_; 
v_startInclusive_383_ = lean_ctor_get(v_slice_380_, 0);
lean_inc(v_startInclusive_383_);
v_endExclusive_384_ = lean_ctor_get(v_slice_380_, 1);
lean_inc(v_endExclusive_384_);
lean_dec_ref(v_slice_380_);
v_it_353_ = v_nextIt_382_;
v_startInclusive_354_ = v_startInclusive_383_;
v_endExclusive_355_ = v_endExclusive_384_;
goto v___jp_352_;
}
}
}
else
{
lean_object* v___x_386_; 
lean_del_object(v___x_346_);
lean_dec(v_searcher_344_);
v___x_386_ = lean_box(1);
lean_inc(v___x_340_);
v_it_353_ = v___x_386_;
v_startInclusive_354_ = v_currPos_343_;
v_endExclusive_355_ = v___x_340_;
goto v___jp_352_;
}
v___jp_352_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v_startInclusive_358_; lean_object* v_endExclusive_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
lean_inc_ref(v___x_338_);
v___x_356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_356_, 0, v___x_338_);
lean_ctor_set(v___x_356_, 1, v_startInclusive_354_);
lean_ctor_set(v___x_356_, 2, v_endExclusive_355_);
v___x_357_ = l_String_Slice_trimAscii(v___x_356_);
v_startInclusive_358_ = lean_ctor_get(v___x_357_, 1);
lean_inc(v_startInclusive_358_);
v_endExclusive_359_ = lean_ctor_get(v___x_357_, 2);
lean_inc(v_endExclusive_359_);
lean_dec_ref(v___x_357_);
v___x_360_ = lean_nat_sub(v_endExclusive_359_, v_startInclusive_358_);
lean_dec(v_startInclusive_358_);
lean_dec(v_endExclusive_359_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
lean_dec(v___x_360_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; 
v___x_363_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_338_, v___x_339_, v___x_340_, v_it_353_, v___x_351_);
return v___x_363_;
}
else
{
uint8_t v___x_364_; 
lean_dec(v_it_353_);
lean_dec(v___x_340_);
lean_dec_ref(v___x_338_);
v___x_364_ = 0;
return v___x_364_;
}
}
}
}
else
{
lean_dec(v___x_340_);
lean_dec_ref(v___x_338_);
return v_b_342_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object* v___x_388_, lean_object* v___x_389_, lean_object* v___x_390_, lean_object* v_a_391_, lean_object* v_b_392_){
_start:
{
uint8_t v_b_boxed_393_; uint8_t v_res_394_; lean_object* v_r_395_; 
v_b_boxed_393_ = lean_unbox(v_b_392_);
v_res_394_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_388_, v___x_389_, v___x_390_, v_a_391_, v_b_boxed_393_);
lean_dec_ref(v___x_389_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object* v_v_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v_parts_402_; uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_string_utf8_byte_size(v_v_398_);
lean_inc_ref_n(v_v_398_, 2);
v___x_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_401_, 0, v_v_398_);
lean_ctor_set(v___x_401_, 1, v___x_399_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
v_parts_402_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
v___x_403_ = 1;
v___x_404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_398_, v___x_401_, v___x_400_, v_parts_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; 
lean_dec_ref_known(v___x_401_, 3);
lean_dec_ref(v_v_398_);
v___x_405_ = lean_box(0);
return v___x_405_;
}
else
{
lean_object* v___x_406_; lean_object* v___x_407_; size_t v_sz_408_; size_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_406_ = ((lean_object*)(l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0));
v___x_407_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v_v_398_, v___x_401_, v___x_400_, v_parts_402_, v___x_406_);
lean_dec_ref_known(v___x_401_, 3);
v_sz_408_ = lean_array_size(v___x_407_);
v___x_409_ = ((size_t)0ULL);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_408_, v___x_409_, v___x_407_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v___x_414_, lean_object* v_inst_415_, lean_object* v_R_416_, lean_object* v_a_417_, uint8_t v_b_418_, lean_object* v_c_419_){
_start:
{
uint8_t v___x_420_; 
v___x_420_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_412_, v___x_413_, v___x_414_, v_a_417_, v_b_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object* v___x_421_, lean_object* v___x_422_, lean_object* v___x_423_, lean_object* v_inst_424_, lean_object* v_R_425_, lean_object* v_a_426_, lean_object* v_b_427_, lean_object* v_c_428_){
_start:
{
uint8_t v_b_boxed_429_; uint8_t v_res_430_; lean_object* v_r_431_; 
v_b_boxed_429_ = lean_unbox(v_b_427_);
v_res_430_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_421_, v___x_422_, v___x_423_, v_inst_424_, v_R_425_, v_a_426_, v_b_boxed_429_, v_c_428_);
lean_dec_ref(v___x_422_);
v_r_431_ = lean_box(v_res_430_);
return v_r_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object* v___x_432_, lean_object* v___x_433_, lean_object* v___x_434_, lean_object* v_inst_435_, lean_object* v_R_436_, lean_object* v_a_437_, lean_object* v_b_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_432_, v___x_433_, v___x_434_, v_a_437_, v_b_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object* v___x_440_, lean_object* v___x_441_, lean_object* v___x_442_, lean_object* v_inst_443_, lean_object* v_R_444_, lean_object* v_a_445_, lean_object* v_b_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_440_, v___x_441_, v___x_442_, v_inst_443_, v_R_444_, v_a_445_, v_b_446_);
lean_dec_ref(v___x_441_);
return v_res_447_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v_inst_451_, lean_object* v_R_452_, lean_object* v_a_453_, uint8_t v_b_454_, lean_object* v_c_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_448_, v___x_449_, v___x_450_, v_a_453_, v_b_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object* v___x_457_, lean_object* v___x_458_, lean_object* v___x_459_, lean_object* v_inst_460_, lean_object* v_R_461_, lean_object* v_a_462_, lean_object* v_b_463_, lean_object* v_c_464_){
_start:
{
uint8_t v_b_boxed_465_; uint8_t v_res_466_; lean_object* v_r_467_; 
v_b_boxed_465_ = lean_unbox(v_b_463_);
v_res_466_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_457_, v___x_458_, v___x_459_, v_inst_460_, v_R_461_, v_a_462_, v_b_boxed_465_, v_c_464_);
lean_dec_ref(v___x_458_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object* v___x_468_, lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v_inst_471_, lean_object* v_R_472_, lean_object* v_a_473_, lean_object* v_b_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_468_, v___x_469_, v___x_470_, v_a_473_, v_b_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v___x_478_, lean_object* v_inst_479_, lean_object* v_R_480_, lean_object* v_a_481_, lean_object* v_b_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(v___x_476_, v___x_477_, v___x_478_, v_inst_479_, v_R_480_, v_a_481_, v_b_482_);
lean_dec_ref(v___x_477_);
return v_res_483_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqContentLength_beq(lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = lean_nat_dec_eq(v_x_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqContentLength_beq___boxed(lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_Std_Http_Header_instBEqContentLength_beq(v_x_487_, v_x_488_);
lean_dec(v_x_488_);
lean_dec(v_x_487_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprContentLength_repr_spec__0(lean_object* v_a_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = lean_nat_to_int(v_a_493_);
return v___x_494_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(10u);
v___x_509_ = lean_nat_to_int(v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0));
v___x_512_ = lean_string_length(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9);
v___x_514_ = lean_nat_to_int(v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg(lean_object* v_x_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_520_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6));
v___x_521_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_522_ = l_Nat_reprFast(v_x_519_);
v___x_523_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
v___x_524_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_521_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = 0;
v___x_526_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set_uint8(v___x_526_, sizeof(void*)*1, v___x_525_);
v___x_527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_520_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_529_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___x_527_);
v___x_531_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_528_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_534_, 0, v___x_533_);
lean_ctor_set_uint8(v___x_534_, sizeof(void*)*1, v___x_525_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr(lean_object* v_x_535_, lean_object* v_prec_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_Http_Header_instReprContentLength_repr___redArg(v_x_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___boxed(lean_object* v_x_538_, lean_object* v_prec_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_Http_Header_instReprContentLength_repr(v_x_538_, v_prec_539_);
lean_dec(v_prec_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(lean_object* v_s_543_, lean_object* v_pos_544_){
_start:
{
lean_object* v_str_545_; lean_object* v_startInclusive_546_; lean_object* v_endExclusive_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v_decide_551_; 
v_str_545_ = lean_ctor_get(v_s_543_, 0);
v_startInclusive_546_ = lean_ctor_get(v_s_543_, 1);
v_endExclusive_547_ = lean_ctor_get(v_s_543_, 2);
v___x_548_ = lean_nat_add(v_startInclusive_546_, v_pos_544_);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_nat_sub(v_endExclusive_547_, v___x_548_);
v_decide_551_ = lean_nat_dec_eq(v___x_549_, v___x_550_);
lean_dec(v___x_550_);
if (v_decide_551_ == 0)
{
uint32_t v___x_552_; uint32_t v___x_553_; uint8_t v___x_554_; 
v___x_552_ = lean_string_utf8_get_fast(v_str_545_, v___x_548_);
v___x_553_ = 48;
v___x_554_ = lean_uint32_dec_le(v___x_553_, v___x_552_);
if (v___x_554_ == 0)
{
lean_dec(v___x_548_);
return v_pos_544_;
}
else
{
uint32_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = 57;
v___x_556_ = lean_uint32_dec_le(v___x_552_, v___x_555_);
if (v___x_556_ == 0)
{
lean_dec(v___x_548_);
return v_pos_544_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_557_ = lean_string_utf8_next_fast(v_str_545_, v___x_548_);
v___x_558_ = lean_nat_sub(v___x_557_, v___x_548_);
lean_dec(v___x_548_);
v___x_559_ = lean_nat_add(v_pos_544_, v___x_558_);
lean_dec(v___x_558_);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_add(v_pos_544_, v___x_560_);
v___x_562_ = lean_nat_dec_le(v___x_561_, v___x_559_);
lean_dec(v___x_561_);
if (v___x_562_ == 0)
{
lean_dec(v___x_559_);
return v_pos_544_;
}
else
{
lean_dec(v_pos_544_);
v_pos_544_ = v___x_559_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_548_);
return v_pos_544_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0___boxed(lean_object* v_s_564_, lean_object* v_pos_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v_s_564_, v_pos_565_);
lean_dec_ref(v_s_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_parse(lean_object* v_v_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_568_ = lean_string_utf8_byte_size(v_v_567_);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_nat_dec_eq(v___x_568_, v___x_569_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v_decide_573_; 
v___x_571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_571_, 0, v_v_567_);
lean_ctor_set(v___x_571_, 1, v___x_569_);
lean_ctor_set(v___x_571_, 2, v___x_568_);
v___x_572_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v___x_571_, v___x_569_);
v_decide_573_ = lean_nat_dec_eq(v___x_572_, v___x_568_);
lean_dec(v___x_572_);
if (v_decide_573_ == 0)
{
lean_object* v___x_574_; 
lean_dec_ref_known(v___x_571_, 3);
v___x_574_ = lean_box(0);
return v___x_574_;
}
else
{
lean_object* v___x_575_; 
v___x_575_ = l_String_Slice_toNat_x3f(v___x_571_);
lean_dec_ref_known(v___x_571_, 3);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; 
v___x_576_ = lean_box(0);
return v___x_576_;
}
else
{
lean_object* v_val_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
v_val_577_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_575_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_val_577_);
lean_dec(v___x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_val_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
else
{
lean_object* v___x_585_; 
lean_dec_ref(v_v_567_);
v___x_585_ = lean_box(0);
return v___x_585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_serialize(lean_object* v_h_586_){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_587_ = l_Std_Http_Header_Name_contentLength;
v___x_588_ = l_Nat_reprFast(v_h_586_);
v___x_589_ = l_Std_Http_Header_Value_ofString_x21(v___x_588_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_587_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
if (lean_obj_tag(v_x_598_) == 0)
{
uint8_t v___x_599_; 
v___x_599_ = 1;
return v___x_599_;
}
else
{
uint8_t v___x_600_; 
v___x_600_ = 0;
return v___x_600_;
}
}
else
{
if (lean_obj_tag(v_x_598_) == 0)
{
uint8_t v___x_601_; 
v___x_601_ = 0;
return v___x_601_;
}
else
{
lean_object* v_val_602_; lean_object* v_val_603_; uint8_t v___x_604_; 
v_val_602_ = lean_ctor_get(v_x_597_, 0);
v_val_603_ = lean_ctor_get(v_x_598_, 0);
v___x_604_ = lean_string_dec_eq(v_val_602_, v_val_603_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
uint8_t v_res_607_; lean_object* v_r_608_; 
v_res_607_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_605_, v_x_606_);
lean_dec(v_x_606_);
lean_dec(v_x_605_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object* v_as_610_, size_t v_i_611_, size_t v_stop_612_, lean_object* v_b_613_){
_start:
{
lean_object* v___y_615_; uint8_t v___x_619_; 
v___x_619_ = lean_usize_dec_eq(v_i_611_, v_stop_612_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_620_ = lean_array_uget_borrowed(v_as_610_, v_i_611_);
v___x_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_622_ = lean_string_dec_eq(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
v___y_615_ = v_b_613_;
goto v___jp_614_;
}
else
{
lean_object* v___x_623_; 
lean_inc(v___x_620_);
v___x_623_ = lean_array_push(v_b_613_, v___x_620_);
v___y_615_ = v___x_623_;
goto v___jp_614_;
}
}
else
{
return v_b_613_;
}
v___jp_614_:
{
size_t v___x_616_; size_t v___x_617_; 
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_add(v_i_611_, v___x_616_);
v_i_611_ = v___x_617_;
v_b_613_ = v___y_615_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object* v_as_624_, lean_object* v_i_625_, lean_object* v_stop_626_, lean_object* v_b_627_){
_start:
{
size_t v_i_boxed_628_; size_t v_stop_boxed_629_; lean_object* v_res_630_; 
v_i_boxed_628_ = lean_unbox_usize(v_i_625_);
lean_dec(v_i_625_);
v_stop_boxed_629_ = lean_unbox_usize(v_stop_626_);
lean_dec(v_stop_626_);
v_res_630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_624_, v_i_boxed_628_, v_stop_boxed_629_, v_b_627_);
lean_dec_ref(v_as_624_);
return v_res_630_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object* v___x_631_, lean_object* v_as_632_, size_t v_i_633_, size_t v_stop_634_){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = lean_usize_dec_eq(v_i_633_, v_stop_634_);
if (v___x_635_ == 0)
{
uint8_t v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_636_ = 1;
v___x_637_ = lean_array_uget_borrowed(v_as_632_, v_i_633_);
lean_inc(v___x_637_);
v___x_638_ = l_Std_Http_Internal_isToken(v___x_637_);
if (v___x_638_ == 0)
{
return v___x_636_;
}
else
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_nat_dec_eq(v___x_631_, v___x_639_);
if (v___x_640_ == 0)
{
size_t v___x_641_; size_t v___x_642_; 
v___x_641_ = ((size_t)1ULL);
v___x_642_ = lean_usize_add(v_i_633_, v___x_641_);
v_i_633_ = v___x_642_;
goto _start;
}
else
{
return v___x_636_;
}
}
}
else
{
uint8_t v___x_644_; 
v___x_644_ = 0;
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object* v___x_645_, lean_object* v_as_646_, lean_object* v_i_647_, lean_object* v_stop_648_){
_start:
{
size_t v_i_boxed_649_; size_t v_stop_boxed_650_; uint8_t v_res_651_; lean_object* v_r_652_; 
v_i_boxed_649_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_stop_boxed_650_ = lean_unbox_usize(v_stop_648_);
lean_dec(v_stop_648_);
v_res_651_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_645_, v_as_646_, v_i_boxed_649_, v_stop_boxed_650_);
lean_dec_ref(v_as_646_);
lean_dec(v___x_645_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object* v_codings_657_){
_start:
{
uint8_t v___y_659_; lean_object* v___y_660_; uint8_t v___y_661_; lean_object* v___y_662_; uint8_t v___y_669_; uint8_t v___y_670_; lean_object* v___y_671_; uint8_t v___y_681_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_694_ = lean_array_get_size(v_codings_657_);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_nat_dec_eq(v___x_694_, v___x_695_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; 
v___x_697_ = lean_nat_dec_lt(v___x_695_, v___x_694_);
if (v___x_697_ == 0)
{
v___y_681_ = v___x_697_;
goto v___jp_680_;
}
else
{
if (v___x_697_ == 0)
{
v___y_681_ = v___x_697_;
goto v___jp_680_;
}
else
{
size_t v___x_698_; size_t v___x_699_; uint8_t v___x_700_; 
v___x_698_ = ((size_t)0ULL);
v___x_699_ = lean_usize_of_nat(v___x_694_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_694_, v_codings_657_, v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
v___y_681_ = v___x_700_;
goto v___jp_680_;
}
else
{
return v___x_696_;
}
}
}
}
else
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
v___jp_658_:
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_dec_lt(v___x_663_, v___y_660_);
if (v___x_664_ == 0)
{
uint8_t v___x_665_; 
v___x_665_ = lean_nat_dec_eq(v___y_660_, v___x_663_);
lean_dec(v___y_660_);
if (v___x_665_ == 0)
{
lean_dec(v___y_662_);
return v___y_661_;
}
else
{
lean_object* v___x_666_; uint8_t v_lastIsChunked_667_; 
v___x_666_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v_lastIsChunked_667_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_662_, v___x_666_);
lean_dec(v___y_662_);
if (v_lastIsChunked_667_ == 0)
{
return v___x_664_;
}
else
{
return v___y_661_;
}
}
}
else
{
lean_dec(v___y_662_);
lean_dec(v___y_660_);
return v___y_659_;
}
}
v___jp_668_:
{
lean_object* v_chunkedCount_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_chunkedCount_672_ = lean_array_get_size(v___y_671_);
lean_dec_ref(v___y_671_);
v___x_673_ = lean_array_get_size(v_codings_657_);
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_sub(v___x_673_, v___x_674_);
v___x_676_ = lean_nat_dec_lt(v___x_675_, v___x_673_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; 
lean_dec(v___x_675_);
v___x_677_ = lean_box(0);
v___y_659_ = v___y_669_;
v___y_660_ = v_chunkedCount_672_;
v___y_661_ = v___y_670_;
v___y_662_ = v___x_677_;
goto v___jp_658_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_array_fget_borrowed(v_codings_657_, v___x_675_);
lean_dec(v___x_675_);
lean_inc(v___x_678_);
v___x_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
v___y_659_ = v___y_669_;
v___y_660_ = v_chunkedCount_672_;
v___y_661_ = v___y_670_;
v___y_662_ = v___x_679_;
goto v___jp_658_;
}
}
v___jp_680_:
{
uint8_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_682_ = 1;
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_array_get_size(v_codings_657_);
v___x_685_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__1));
v___x_686_ = lean_nat_dec_lt(v___x_683_, v___x_684_);
if (v___x_686_ == 0)
{
v___y_669_ = v___y_681_;
v___y_670_ = v___x_682_;
v___y_671_ = v___x_685_;
goto v___jp_668_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = lean_nat_dec_le(v___x_684_, v___x_684_);
if (v___x_687_ == 0)
{
if (v___x_686_ == 0)
{
v___y_669_ = v___y_681_;
v___y_670_ = v___x_682_;
v___y_671_ = v___x_685_;
goto v___jp_668_;
}
else
{
size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; 
v___x_688_ = ((size_t)0ULL);
v___x_689_ = lean_usize_of_nat(v___x_684_);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_657_, v___x_688_, v___x_689_, v___x_685_);
v___y_669_ = v___y_681_;
v___y_670_ = v___x_682_;
v___y_671_ = v___x_690_;
goto v___jp_668_;
}
}
else
{
size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_691_ = ((size_t)0ULL);
v___x_692_ = lean_usize_of_nat(v___x_684_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_657_, v___x_691_, v___x_692_, v___x_685_);
v___y_669_ = v___y_681_;
v___y_670_ = v___x_682_;
v___y_671_ = v___x_693_;
goto v___jp_668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_Validate___boxed(lean_object* v_codings_702_){
_start:
{
uint8_t v_res_703_; lean_object* v_r_704_; 
v_res_703_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_702_);
lean_dec_ref(v_codings_702_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(lean_object* v___y_705_){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = l_String_quote(v___y_705_);
v___x_707_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_710_) == 0)
{
lean_dec(v_x_708_);
return v_x_709_;
}
else
{
lean_object* v_head_711_; lean_object* v_tail_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_723_; 
v_head_711_ = lean_ctor_get(v_x_710_, 0);
v_tail_712_ = lean_ctor_get(v_x_710_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_710_);
if (v_isSharedCheck_723_ == 0)
{
v___x_714_ = v_x_710_;
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_tail_712_);
lean_inc(v_head_711_);
lean_dec(v_x_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
lean_inc(v_x_708_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 5);
lean_ctor_set(v___x_714_, 1, v_x_708_);
lean_ctor_set(v___x_714_, 0, v_x_709_);
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_x_709_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_x_708_);
v___x_717_ = v_reuseFailAlloc_722_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = l_String_quote(v_head_711_);
v___x_719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_717_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v_x_709_ = v___x_720_;
v_x_710_ = v_tail_712_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
lean_dec(v_x_724_);
return v_x_725_;
}
else
{
lean_object* v_head_727_; lean_object* v_tail_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_739_; 
v_head_727_ = lean_ctor_get(v_x_726_, 0);
v_tail_728_ = lean_ctor_get(v_x_726_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_x_726_);
if (v_isSharedCheck_739_ == 0)
{
v___x_730_ = v_x_726_;
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_tail_728_);
lean_inc(v_head_727_);
lean_dec(v_x_726_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
lean_inc(v_x_724_);
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 5);
lean_ctor_set(v___x_730_, 1, v_x_724_);
lean_ctor_set(v___x_730_, 0, v_x_725_);
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_x_725_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_x_724_);
v___x_733_ = v_reuseFailAlloc_738_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = l_String_quote(v_head_727_);
v___x_735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_733_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(v_x_724_, v___x_736_, v_tail_728_);
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(lean_object* v_x_740_, lean_object* v_x_741_){
_start:
{
if (lean_obj_tag(v_x_740_) == 0)
{
lean_object* v___x_742_; 
lean_dec(v_x_741_);
v___x_742_ = lean_box(0);
return v___x_742_;
}
else
{
lean_object* v_tail_743_; 
v_tail_743_ = lean_ctor_get(v_x_740_, 1);
if (lean_obj_tag(v_tail_743_) == 0)
{
lean_object* v_head_744_; lean_object* v___x_745_; 
lean_dec(v_x_741_);
v_head_744_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_head_744_);
lean_dec_ref_known(v_x_740_, 2);
v___x_745_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_744_);
return v___x_745_;
}
else
{
lean_object* v_head_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
lean_inc(v_tail_743_);
v_head_746_ = lean_ctor_get(v_x_740_, 0);
lean_inc(v_head_746_);
lean_dec_ref_known(v_x_740_, 2);
v___x_747_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_746_);
v___x_748_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(v_x_741_, v___x_747_, v_tail_743_);
return v___x_748_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0));
v___x_758_ = lean_string_length(v___x_757_);
return v___x_758_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5);
v___x_760_ = lean_nat_to_int(v___x_759_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(lean_object* v_xs_768_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_769_ = lean_array_get_size(v_xs_768_);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_nat_dec_eq(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_772_ = lean_array_to_list(v_xs_768_);
v___x_773_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3));
v___x_774_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(v___x_772_, v___x_773_);
v___x_775_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6);
v___x_776_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7));
v___x_777_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
lean_ctor_set(v___x_777_, 1, v___x_774_);
v___x_778_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8));
v___x_779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_775_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = l_Std_Format_fill(v___x_780_);
return v___x_781_;
}
else
{
lean_object* v___x_782_; 
lean_dec_ref(v_xs_768_);
v___x_782_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10));
return v___x_782_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(11u);
v___x_793_ = lean_nat_to_int(v___x_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg(lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_801_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_802_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3));
v___x_803_ = lean_obj_once(&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4, &l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4);
v___x_804_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_800_);
v___x_805_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = 0;
v___x_807_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set_uint8(v___x_807_, sizeof(void*)*1, v___x_806_);
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_802_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_box(1);
v___x_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6));
v___x_814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___x_801_);
v___x_816_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_819_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___x_817_);
v___x_821_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_818_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set_uint8(v___x_824_, sizeof(void*)*1, v___x_806_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr(lean_object* v_x_825_, lean_object* v_prec_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg(v_x_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___boxed(lean_object* v_x_828_, lean_object* v_prec_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_Http_Header_instReprTransferEncoding_repr(v_x_828_, v_prec_829_);
lean_dec(v_prec_829_);
return v_res_830_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object* v_te_833_){
_start:
{
lean_object* v___y_835_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_838_ = lean_array_get_size(v_te_833_);
v___x_839_ = lean_unsigned_to_nat(1u);
v___x_840_ = lean_nat_sub(v___x_838_, v___x_839_);
v___x_841_ = lean_nat_dec_lt(v___x_840_, v___x_838_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
lean_dec(v___x_840_);
v___x_842_ = lean_box(0);
v___y_835_ = v___x_842_;
goto v___jp_834_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_array_fget_borrowed(v_te_833_, v___x_840_);
lean_dec(v___x_840_);
lean_inc(v___x_843_);
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
v___y_835_ = v___x_844_;
goto v___jp_834_;
}
v___jp_834_:
{
lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_836_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v___x_837_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_835_, v___x_836_);
lean_dec(v___y_835_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_isChunked___boxed(lean_object* v_te_845_){
_start:
{
uint8_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_845_);
lean_dec_ref(v_te_845_);
v_r_847_ = lean_box(v_res_846_);
return v_r_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object* v_v_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_848_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v___x_850_; 
v___x_850_ = lean_box(0);
return v___x_850_;
}
else
{
lean_object* v_val_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_860_; 
v_val_851_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_860_ == 0)
{
v___x_853_ = v___x_849_;
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_val_851_);
lean_dec(v___x_849_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_860_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
uint8_t v___x_855_; 
v___x_855_ = l_Std_Http_Header_TransferEncoding_Validate(v_val_851_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_del_object(v___x_853_);
lean_dec(v_val_851_);
v___x_856_ = lean_box(0);
return v___x_856_;
}
else
{
lean_object* v___x_858_; 
if (v_isShared_854_ == 0)
{
v___x_858_ = v___x_853_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_val_851_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_serialize(lean_object* v_te_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v_value_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_862_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_863_ = lean_array_to_list(v_te_861_);
v_value_864_ = l_String_intercalate(v___x_862_, v___x_863_);
v___x_865_ = l_Std_Http_Header_Name_transferEncoding;
v___x_866_ = l_Std_Http_Header_Value_ofString_x21(v_value_864_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___redArg(lean_object* v_x_886_){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_887_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_888_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__3));
v___x_889_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_890_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_886_);
v___x_891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = 0;
v___x_893_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*1, v___x_892_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_888_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_box(1);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__5));
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_887_);
v___x_902_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_905_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_903_);
v___x_907_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_904_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*1, v___x_892_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr(lean_object* v_x_911_, lean_object* v_prec_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Std_Http_Header_instReprConnection_repr___redArg(v_x_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___boxed(lean_object* v_x_914_, lean_object* v_prec_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Std_Http_Header_instReprConnection_repr(v_x_914_, v_prec_915_);
lean_dec(v_prec_915_);
return v_res_916_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(lean_object* v_token_919_, lean_object* v_as_920_, size_t v_i_921_, size_t v_stop_922_){
_start:
{
uint8_t v___x_923_; 
v___x_923_ = lean_usize_dec_eq(v_i_921_, v_stop_922_);
if (v___x_923_ == 0)
{
lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_924_ = lean_array_uget_borrowed(v_as_920_, v_i_921_);
v___x_925_ = lean_string_dec_eq(v___x_924_, v_token_919_);
if (v___x_925_ == 0)
{
size_t v___x_926_; size_t v___x_927_; 
v___x_926_ = ((size_t)1ULL);
v___x_927_ = lean_usize_add(v_i_921_, v___x_926_);
v_i_921_ = v___x_927_;
goto _start;
}
else
{
return v___x_925_;
}
}
else
{
uint8_t v___x_929_; 
v___x_929_ = 0;
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(lean_object* v_token_930_, lean_object* v_as_931_, lean_object* v_i_932_, lean_object* v_stop_933_){
_start:
{
size_t v_i_boxed_934_; size_t v_stop_boxed_935_; uint8_t v_res_936_; lean_object* v_r_937_; 
v_i_boxed_934_ = lean_unbox_usize(v_i_932_);
lean_dec(v_i_932_);
v_stop_boxed_935_ = lean_unbox_usize(v_stop_933_);
lean_dec(v_stop_933_);
v_res_936_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_930_, v_as_931_, v_i_boxed_934_, v_stop_boxed_935_);
lean_dec_ref(v_as_931_);
lean_dec_ref(v_token_930_);
v_r_937_ = lean_box(v_res_936_);
return v_r_937_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_containsToken(lean_object* v_connection_938_, lean_object* v_token_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_array_get_size(v_connection_938_);
v___x_942_ = lean_nat_dec_lt(v___x_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_dec_ref(v_token_939_);
return v___x_942_;
}
else
{
lean_object* v___x_943_; 
v___x_943_ = lean_string_utf8_byte_size(v_token_939_);
if (v___x_942_ == 0)
{
lean_dec_ref(v_token_939_);
return v___x_942_;
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_token_947_; size_t v___x_948_; size_t v___x_949_; uint8_t v___x_950_; 
v___x_944_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_944_, 0, v_token_939_);
lean_ctor_set(v___x_944_, 1, v___x_940_);
lean_ctor_set(v___x_944_, 2, v___x_943_);
v___x_945_ = l_String_Slice_trimAscii(v___x_944_);
v___x_946_ = l_String_Slice_toString(v___x_945_);
lean_dec_ref(v___x_945_);
v_token_947_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_946_, v___x_940_);
v___x_948_ = ((size_t)0ULL);
v___x_949_ = lean_usize_of_nat(v___x_941_);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_947_, v_connection_938_, v___x_948_, v___x_949_);
lean_dec_ref(v_token_947_);
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_containsToken___boxed(lean_object* v_connection_951_, lean_object* v_token_952_){
_start:
{
uint8_t v_res_953_; lean_object* v_r_954_; 
v_res_953_ = l_Std_Http_Header_Connection_containsToken(v_connection_951_, v_token_952_);
lean_dec_ref(v_connection_951_);
v_r_954_ = lean_box(v_res_953_);
return v_r_954_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_shouldClose(lean_object* v_connection_956_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = ((lean_object*)(l_Std_Http_Header_Connection_shouldClose___closed__0));
v___x_958_ = l_Std_Http_Header_Connection_containsToken(v_connection_956_, v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_shouldClose___boxed(lean_object* v_connection_959_){
_start:
{
uint8_t v_res_960_; lean_object* v_r_961_; 
v_res_960_ = l_Std_Http_Header_Connection_shouldClose(v_connection_959_);
lean_dec_ref(v_connection_959_);
v_r_961_ = lean_box(v_res_960_);
return v_r_961_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(lean_object* v_as_962_, size_t v_i_963_, size_t v_stop_964_){
_start:
{
uint8_t v___x_965_; 
v___x_965_ = lean_usize_dec_eq(v_i_963_, v_stop_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_966_ = lean_array_uget_borrowed(v_as_962_, v_i_963_);
lean_inc(v___x_966_);
v___x_967_ = l_Std_Http_Internal_isToken(v___x_966_);
if (v___x_967_ == 0)
{
uint8_t v___x_968_; 
v___x_968_ = 1;
return v___x_968_;
}
else
{
size_t v___x_969_; size_t v___x_970_; 
v___x_969_ = ((size_t)1ULL);
v___x_970_ = lean_usize_add(v_i_963_, v___x_969_);
v_i_963_ = v___x_970_;
goto _start;
}
}
else
{
uint8_t v___x_972_; 
v___x_972_ = 0;
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(lean_object* v_as_973_, lean_object* v_i_974_, lean_object* v_stop_975_){
_start:
{
size_t v_i_boxed_976_; size_t v_stop_boxed_977_; uint8_t v_res_978_; lean_object* v_r_979_; 
v_i_boxed_976_ = lean_unbox_usize(v_i_974_);
lean_dec(v_i_974_);
v_stop_boxed_977_ = lean_unbox_usize(v_stop_975_);
lean_dec(v_stop_975_);
v_res_978_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_973_, v_i_boxed_976_, v_stop_boxed_977_);
lean_dec_ref(v_as_973_);
v_r_979_ = lean_box(v_res_978_);
return v_r_979_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_parse(lean_object* v_v_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_980_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_box(0);
return v___x_982_;
}
else
{
lean_object* v_val_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1003_; 
v_val_983_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_985_ = v___x_981_;
v_isShared_986_ = v_isSharedCheck_1003_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_val_983_);
lean_dec(v___x_981_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1003_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_array_get_size(v_val_983_);
v___x_989_ = lean_nat_dec_lt(v___x_987_, v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_991_; 
if (v_isShared_986_ == 0)
{
v___x_991_ = v___x_985_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_val_983_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
else
{
if (v___x_989_ == 0)
{
lean_object* v___x_994_; 
if (v_isShared_986_ == 0)
{
v___x_994_ = v___x_985_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_val_983_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
else
{
size_t v___x_996_; size_t v___x_997_; uint8_t v___x_998_; 
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_988_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_val_983_, v___x_996_, v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_1000_; 
if (v_isShared_986_ == 0)
{
v___x_1000_ = v___x_985_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_val_983_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
lean_object* v___x_1002_; 
lean_del_object(v___x_985_);
lean_dec(v_val_983_);
v___x_1002_ = lean_box(0);
return v___x_1002_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_serialize(lean_object* v_connection_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v_value_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1005_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_1006_ = lean_array_to_list(v_connection_1004_);
v_value_1007_ = l_String_intercalate(v___x_1005_, v___x_1006_);
v___x_1008_ = l_Std_Http_Header_Name_connection;
v___x_1009_ = l_Std_Http_Header_Value_ofString_x21(v_value_1007_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_unsigned_to_nat(8u);
v___x_1027_ = lean_nat_to_int(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_unsigned_to_nat(2u);
v___x_1029_ = lean_nat_to_int(v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___redArg(lean_object* v_x_1037_){
_start:
{
lean_object* v_host_1038_; lean_object* v_port_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1113_; 
v_host_1038_ = lean_ctor_get(v_x_1037_, 0);
v_port_1039_ = lean_ctor_get(v_x_1037_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_x_1037_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1041_ = v_x_1037_;
v_isShared_1042_ = v_isSharedCheck_1113_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_port_1039_);
lean_inc(v_host_1038_);
lean_dec(v_x_1037_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1113_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_ctr_1049_; lean_object* v_a_1050_; 
v___x_1043_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_1044_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__3));
v___x_1045_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__4, &l_Std_Http_Header_instReprHost_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4);
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__5, &l_Std_Http_Header_instReprHost_repr___redArg___closed__5_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5);
switch(lean_obj_tag(v_host_1038_))
{
case 0:
{
lean_object* v_name_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1092_; 
v_name_1083_ = lean_ctor_get(v_host_1038_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_host_1038_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1085_ = v_host_1038_;
v_isShared_1086_ = v_isSharedCheck_1092_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_name_1083_);
lean_dec(v_host_1038_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1092_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1087_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__9));
v___x_1088_ = l_String_quote(v_name_1083_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set_tag(v___x_1085_, 3);
lean_ctor_set(v___x_1085_, 0, v___x_1088_);
v___x_1090_ = v___x_1085_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
v_ctr_1049_ = v___x_1087_;
v_a_1050_ = v___x_1090_;
goto v___jp_1048_;
}
}
}
case 1:
{
lean_object* v_ipv4_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1102_; 
v_ipv4_1093_ = lean_ctor_get(v_host_1038_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_host_1038_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1095_ = v_host_1038_;
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_ipv4_1093_);
lean_dec(v_host_1038_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1102_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1097_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__10));
v___x_1098_ = lean_uv_ntop_v4(v_ipv4_1093_);
lean_dec_ref(v_ipv4_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 3);
lean_ctor_set(v___x_1095_, 0, v___x_1098_);
v___x_1100_ = v___x_1095_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
v_ctr_1049_ = v___x_1097_;
v_a_1050_ = v___x_1100_;
goto v___jp_1048_;
}
}
}
default: 
{
lean_object* v_ipv6_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1112_; 
v_ipv6_1103_ = lean_ctor_get(v_host_1038_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_host_1038_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1105_ = v_host_1038_;
v_isShared_1106_ = v_isSharedCheck_1112_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_ipv6_1103_);
lean_dec(v_host_1038_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1112_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1107_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__11));
v___x_1108_ = lean_uv_ntop_v6(v_ipv6_1103_);
lean_dec_ref(v_ipv6_1103_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set_tag(v___x_1105_, 3);
lean_ctor_set(v___x_1105_, 0, v___x_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
v_ctr_1049_ = v___x_1107_;
v_a_1050_ = v___x_1110_;
goto v___jp_1048_;
}
}
}
}
v___jp_1048_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1051_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__6));
v___x_1052_ = lean_string_append(v___x_1051_, v_ctr_1049_);
v___x_1053_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
v___x_1054_ = lean_box(1);
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 5);
lean_ctor_set(v___x_1041_, 1, v___x_1054_);
lean_ctor_set(v___x_1041_, 0, v___x_1053_);
v___x_1056_ = v___x_1041_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_a_1050_);
v___x_1058_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1047_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = 0;
v___x_1060_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*1, v___x_1059_);
v___x_1061_ = l_Repr_addAppParen(v___x_1060_, v___x_1046_);
v___x_1062_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1045_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*1, v___x_1059_);
v___x_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1044_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_1054_);
v___x_1068_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__8));
v___x_1069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1043_);
v___x_1071_ = l_Std_Http_URI_instReprPort_repr(v_port_1039_, v___x_1046_);
lean_dec(v_port_1039_);
v___x_1072_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1045_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*1, v___x_1059_);
v___x_1074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1070_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1076_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1074_);
v___x_1078_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1075_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set_uint8(v___x_1081_, sizeof(void*)*1, v___x_1059_);
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr(lean_object* v_x_1114_, lean_object* v_prec_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Std_Http_Header_instReprHost_repr___redArg(v_x_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___boxed(lean_object* v_x_1117_, lean_object* v_prec_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Std_Http_Header_instReprHost_repr(v_x_1117_, v_prec_1118_);
lean_dec(v_prec_1118_);
return v_res_1119_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqHost_beq(lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
lean_object* v_host_1124_; lean_object* v_port_1125_; lean_object* v_host_1126_; lean_object* v_port_1127_; uint8_t v___x_1128_; 
v_host_1124_ = lean_ctor_get(v_x_1122_, 0);
v_port_1125_ = lean_ctor_get(v_x_1122_, 1);
v_host_1126_ = lean_ctor_get(v_x_1123_, 0);
v_port_1127_ = lean_ctor_get(v_x_1123_, 1);
v___x_1128_ = l_Std_Http_URI_instBEqHost_beq(v_host_1124_, v_host_1126_);
if (v___x_1128_ == 0)
{
return v___x_1128_;
}
else
{
uint8_t v___x_1129_; 
v___x_1129_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1125_, v_port_1127_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqHost_beq___boxed(lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
uint8_t v_res_1132_; lean_object* v_r_1133_; 
v_res_1132_ = l_Std_Http_Header_instBEqHost_beq(v_x_1130_, v_x_1131_);
lean_dec_ref(v_x_1131_);
lean_dec_ref(v_x_1130_);
v_r_1133_ = lean_box(v_res_1132_);
return v_r_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0(lean_object* v___x_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Std_Http_URI_Parser_parseHostHeader(v___x_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_pos_1142_; lean_object* v_array_1143_; lean_object* v_idx_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_pos_1142_ = lean_ctor_get(v___x_1141_, 0);
v_array_1143_ = lean_ctor_get(v_pos_1142_, 0);
v_idx_1144_ = lean_ctor_get(v_pos_1142_, 1);
v___x_1145_ = lean_byte_array_size(v_array_1143_);
v___x_1146_ = lean_nat_dec_lt(v_idx_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
return v___x_1141_;
}
else
{
lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1154_; 
lean_inc(v_pos_1142_);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; lean_object* v_unused_1156_; 
v_unused_1155_ = lean_ctor_get(v___x_1141_, 1);
lean_dec(v_unused_1155_);
v_unused_1156_ = lean_ctor_get(v___x_1141_, 0);
lean_dec(v_unused_1156_);
v___x_1148_ = v___x_1141_;
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v___x_1141_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = ((lean_object*)(l_Std_Http_Header_Host_parse___lam__0___closed__1));
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 1);
lean_ctor_set(v___x_1148_, 1, v___x_1150_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_pos_1142_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0___boxed(lean_object* v___x_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Std_Http_Header_Host_parse___lam__0(v___x_1157_, v___y_1158_);
lean_dec_ref(v___x_1157_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse(lean_object* v_v_1170_){
_start:
{
lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v_parsed_1173_; 
v___f_1171_ = ((lean_object*)(l_Std_Http_Header_Host_parse___closed__1));
v___x_1172_ = lean_string_to_utf8(v_v_1170_);
v_parsed_1173_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1171_, v___x_1172_);
if (lean_obj_tag(v_parsed_1173_) == 0)
{
lean_object* v___x_1174_; 
lean_dec_ref_known(v_parsed_1173_, 1);
v___x_1174_ = lean_box(0);
return v___x_1174_;
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1191_; 
v_a_1175_ = lean_ctor_get(v_parsed_1173_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_parsed_1173_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1177_ = v_parsed_1173_;
v_isShared_1178_ = v_isSharedCheck_1191_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v_parsed_1173_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1191_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1190_; 
v_fst_1179_ = lean_ctor_get(v_a_1175_, 0);
v_snd_1180_ = lean_ctor_get(v_a_1175_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_a_1175_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1182_ = v_a_1175_;
v_isShared_1183_ = v_isSharedCheck_1190_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_inc(v_fst_1179_);
lean_dec(v_a_1175_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1190_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_fst_1179_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_snd_1180_);
v___x_1185_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1185_);
v___x_1187_ = v___x_1177_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___boxed(lean_object* v_v_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Std_Http_Header_Host_parse(v_v_1192_);
lean_dec_ref(v_v_1192_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_serialize(lean_object* v_host_1196_){
_start:
{
lean_object* v___y_1198_; lean_object* v___y_1202_; lean_object* v_port_1206_; 
v_port_1206_ = lean_ctor_get(v_host_1196_, 1);
switch(lean_obj_tag(v_port_1206_))
{
case 0:
{
lean_object* v_host_1207_; 
v_host_1207_ = lean_ctor_get(v_host_1196_, 0);
lean_inc_ref(v_host_1207_);
lean_dec_ref(v_host_1196_);
switch(lean_obj_tag(v_host_1207_))
{
case 0:
{
lean_object* v_name_1208_; lean_object* v___x_1209_; 
v_name_1208_ = lean_ctor_get(v_host_1207_, 0);
lean_inc_ref(v_name_1208_);
lean_dec_ref_known(v_host_1207_, 1);
v___x_1209_ = l_Std_Http_Header_Value_ofString_x21(v_name_1208_);
v___y_1198_ = v___x_1209_;
goto v___jp_1197_;
}
case 1:
{
lean_object* v_ipv4_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_ipv4_1210_ = lean_ctor_get(v_host_1207_, 0);
lean_inc_ref(v_ipv4_1210_);
lean_dec_ref_known(v_host_1207_, 1);
v___x_1211_ = lean_uv_ntop_v4(v_ipv4_1210_);
lean_dec_ref(v_ipv4_1210_);
v___x_1212_ = l_Std_Http_Header_Value_ofString_x21(v___x_1211_);
v___y_1198_ = v___x_1212_;
goto v___jp_1197_;
}
default: 
{
lean_object* v_ipv6_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_ipv6_1213_ = lean_ctor_get(v_host_1207_, 0);
lean_inc_ref(v_ipv6_1213_);
lean_dec_ref_known(v_host_1207_, 1);
v___x_1214_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1215_ = lean_uv_ntop_v6(v_ipv6_1213_);
lean_dec_ref(v_ipv6_1213_);
v___x_1216_ = lean_string_append(v___x_1214_, v___x_1215_);
lean_dec_ref(v___x_1215_);
v___x_1217_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1218_ = lean_string_append(v___x_1216_, v___x_1217_);
v___x_1219_ = l_Std_Http_Header_Value_ofString_x21(v___x_1218_);
v___y_1198_ = v___x_1219_;
goto v___jp_1197_;
}
}
}
case 1:
{
lean_object* v_host_1220_; 
v_host_1220_ = lean_ctor_get(v_host_1196_, 0);
lean_inc_ref(v_host_1220_);
lean_dec_ref(v_host_1196_);
switch(lean_obj_tag(v_host_1220_))
{
case 0:
{
lean_object* v_name_1221_; 
v_name_1221_ = lean_ctor_get(v_host_1220_, 0);
lean_inc_ref(v_name_1221_);
lean_dec_ref_known(v_host_1220_, 1);
v___y_1202_ = v_name_1221_;
goto v___jp_1201_;
}
case 1:
{
lean_object* v_ipv4_1222_; lean_object* v___x_1223_; 
v_ipv4_1222_ = lean_ctor_get(v_host_1220_, 0);
lean_inc_ref(v_ipv4_1222_);
lean_dec_ref_known(v_host_1220_, 1);
v___x_1223_ = lean_uv_ntop_v4(v_ipv4_1222_);
lean_dec_ref(v_ipv4_1222_);
v___y_1202_ = v___x_1223_;
goto v___jp_1201_;
}
default: 
{
lean_object* v_ipv6_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_ipv6_1224_ = lean_ctor_get(v_host_1220_, 0);
lean_inc_ref(v_ipv6_1224_);
lean_dec_ref_known(v_host_1220_, 1);
v___x_1225_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1226_ = lean_uv_ntop_v6(v_ipv6_1224_);
lean_dec_ref(v_ipv6_1224_);
v___x_1227_ = lean_string_append(v___x_1225_, v___x_1226_);
lean_dec_ref(v___x_1226_);
v___x_1228_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1229_ = lean_string_append(v___x_1227_, v___x_1228_);
v___y_1202_ = v___x_1229_;
goto v___jp_1201_;
}
}
}
default: 
{
lean_object* v_host_1230_; uint16_t v_port_1231_; lean_object* v___y_1233_; 
lean_inc_ref(v_port_1206_);
v_host_1230_ = lean_ctor_get(v_host_1196_, 0);
lean_inc_ref(v_host_1230_);
lean_dec_ref(v_host_1196_);
v_port_1231_ = lean_ctor_get_uint16(v_port_1206_, 0);
lean_dec_ref_known(v_port_1206_, 0);
switch(lean_obj_tag(v_host_1230_))
{
case 0:
{
lean_object* v_name_1240_; 
v_name_1240_ = lean_ctor_get(v_host_1230_, 0);
lean_inc_ref(v_name_1240_);
lean_dec_ref_known(v_host_1230_, 1);
v___y_1233_ = v_name_1240_;
goto v___jp_1232_;
}
case 1:
{
lean_object* v_ipv4_1241_; lean_object* v___x_1242_; 
v_ipv4_1241_ = lean_ctor_get(v_host_1230_, 0);
lean_inc_ref(v_ipv4_1241_);
lean_dec_ref_known(v_host_1230_, 1);
v___x_1242_ = lean_uv_ntop_v4(v_ipv4_1241_);
lean_dec_ref(v_ipv4_1241_);
v___y_1233_ = v___x_1242_;
goto v___jp_1232_;
}
default: 
{
lean_object* v_ipv6_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_ipv6_1243_ = lean_ctor_get(v_host_1230_, 0);
lean_inc_ref(v_ipv6_1243_);
lean_dec_ref_known(v_host_1230_, 1);
v___x_1244_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1245_ = lean_uv_ntop_v6(v_ipv6_1243_);
lean_dec_ref(v_ipv6_1243_);
v___x_1246_ = lean_string_append(v___x_1244_, v___x_1245_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1248_ = lean_string_append(v___x_1246_, v___x_1247_);
v___y_1233_ = v___x_1248_;
goto v___jp_1232_;
}
}
v___jp_1232_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___x_1234_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1235_ = lean_string_append(v___y_1233_, v___x_1234_);
v___x_1236_ = lean_uint16_to_nat(v_port_1231_);
v___x_1237_ = l_Nat_reprFast(v___x_1236_);
v___x_1238_ = lean_string_append(v___x_1235_, v___x_1237_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = l_Std_Http_Header_Value_ofString_x21(v___x_1238_);
v___y_1198_ = v___x_1239_;
goto v___jp_1197_;
}
}
}
v___jp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__0));
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v___y_1198_);
return v___x_1200_;
}
v___jp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1204_ = lean_string_append(v___y_1202_, v___x_1203_);
v___x_1205_ = l_Std_Http_Header_Value_ofString_x21(v___x_1204_);
v___y_1198_ = v___x_1205_;
goto v___jp_1197_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = ((lean_object*)(l_Std_Http_Header_instReprExpect_repr___redArg___closed__1));
v___x_1262_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1262_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
return v___x_1263_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3(void){
_start:
{
uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = 0;
v___x_1265_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__2, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__2_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2);
v___x_1266_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*1, v___x_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg(){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__3, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__3_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___boxed(lean_object* v___dummy_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v_res_1270_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___closed__0(void){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr(lean_object* v_x_1272_, lean_object* v_prec_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___closed__0, &l_Std_Http_Header_instReprExpect_repr___closed__0_once, _init_l_Std_Http_Header_instReprExpect_repr___closed__0);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___boxed(lean_object* v_x_1275_, lean_object* v_prec_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Std_Http_Header_instReprExpect_repr(v_x_1275_, v_prec_1276_);
lean_dec(v_prec_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq___redArg(){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = 1;
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___redArg___boxed(lean_object* v___dummy_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Std_Http_Header_instBEqExpect_beq___redArg();
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq(lean_object* v_x_1285_, lean_object* v_y_1286_){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = 1;
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___boxed(lean_object* v_x_1288_, lean_object* v_y_1289_){
_start:
{
uint8_t v_res_1290_; lean_object* v_r_1291_; 
v_res_1290_ = l_Std_Http_Header_instBEqExpect_beq(v_x_1288_, v_y_1289_);
v_r_1291_ = lean_box(v_res_1290_);
return v_r_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_parse(lean_object* v_v_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v_normalized_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_string_utf8_byte_size(v_v_1297_);
v___x_1300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1300_, 0, v_v_1297_);
lean_ctor_set(v___x_1300_, 1, v___x_1298_);
lean_ctor_set(v___x_1300_, 2, v___x_1299_);
v___x_1301_ = l_String_Slice_trimAscii(v___x_1300_);
v___x_1302_ = l_String_Slice_toString(v___x_1301_);
lean_dec_ref(v___x_1301_);
v_normalized_1303_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_1302_, v___x_1298_);
v___x_1304_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1305_ = lean_string_dec_eq(v_normalized_1303_, v___x_1304_);
lean_dec_ref(v_normalized_1303_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; 
v___x_1306_ = lean_box(0);
return v___x_1306_;
}
else
{
lean_object* v___x_1307_; 
v___x_1307_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__1));
return v___x_1307_;
}
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1309_ = l_Std_Http_Header_Value_ofString_x21(v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1(void){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__0, &l_Std_Http_Header_Expect_serialize___redArg___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0);
v___x_1311_ = l_Std_Http_Header_Name_expect;
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1311_);
lean_ctor_set(v___x_1312_, 1, v___x_1310_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg(){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__1, &l_Std_Http_Header_Expect_serialize___redArg___closed__1_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg___boxed(lean_object* v___dummy_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Std_Http_Header_Expect_serialize___redArg();
return v_res_1316_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___closed__0(void){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Std_Http_Header_Expect_serialize___redArg();
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize(lean_object* v_x_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___closed__0, &l_Std_Http_Header_Expect_serialize___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___closed__0);
return v___x_1319_;
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

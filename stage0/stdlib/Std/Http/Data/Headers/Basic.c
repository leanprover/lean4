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
lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v_fst_4_, lean_object* v___x_5_, uint32_t v___x_6_, lean_object* v___x_7_, lean_object* v_it_8_, lean_object* v_acc_9_, lean_object* v_hP_10_, lean_object* v_recur_11_){
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
LEAN_EXPORT void l_Std_Http_instEncodeV11OfHeader___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1_ = stack[0].m_obj;
lean_object* v___x_2_ = stack[1].m_obj;
lean_object* v___x_3_ = stack[2].m_obj;
lean_object* v_fst_4_ = stack[3].m_obj;
lean_object* v___x_5_ = stack[4].m_obj;
uint32_t v___x_6_ = stack[5].m_num;
lean_object* v___x_7_ = stack[6].m_obj;
lean_object* v_it_8_ = stack[7].m_obj;
lean_object* v_acc_9_ = stack[8].m_obj;
lean_object* v_recur_11_ = stack[10].m_obj;
lean_object* v_res_68_;
v_res_68_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(v___x_1_, v___x_2_, v___x_3_, v_fst_4_, v___x_5_, v___x_6_, v___x_7_, v_it_8_, v_acc_9_, lean_box(0), v_recur_11_);
stack->m_obj
 = v_res_68_;
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed(lean_object* v___x_69_, lean_object* v___x_70_, lean_object* v___x_71_, lean_object* v_fst_72_, lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v___x_75_, lean_object* v_it_76_, lean_object* v_acc_77_, lean_object* v_hP_78_, lean_object* v_recur_79_){
_start:
{
uint32_t v___x_1381__boxed_80_; lean_object* v_res_81_; 
v___x_1381__boxed_80_ = lean_unbox_uint32(v___x_74_);
lean_dec(v___x_74_);
v_res_81_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(v___x_69_, v___x_70_, v___x_71_, v_fst_72_, v___x_73_, v___x_1381__boxed_80_, v___x_75_, v_it_76_, v_acc_77_, v_hP_78_, v_recur_79_);
lean_dec_ref(v___x_75_);
lean_dec_ref(v_fst_72_);
lean_dec(v___x_71_);
lean_dec(v___x_70_);
lean_dec_ref(v___x_69_);
return v_res_81_;
}
}
static lean_object* _init_l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1(void){
_start:
{
uint32_t v___x_87_; lean_object* v___x_88_; 
v___x_87_ = 45;
v___x_88_ = lean_box_uint32(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1(lean_object* v_h_89_, lean_object* v_buffer_90_, lean_object* v_a_91_){
_start:
{
lean_object* v_serialize_92_; lean_object* v___x_93_; lean_object* v_fst_94_; lean_object* v_snd_95_; lean_object* v___y_97_; lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_it_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_serialize_92_ = lean_ctor_get(v_h_89_, 1);
lean_inc_ref(v_serialize_92_);
lean_dec_ref(v_h_89_);
v___x_93_ = lean_apply_1(v_serialize_92_, v_a_91_);
v_fst_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_n(v_fst_94_, 2);
v_snd_95_ = lean_ctor_get(v___x_93_, 1);
lean_inc(v_snd_95_);
lean_dec_ref(v___x_93_);
v___f_116_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2));
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_string_utf8_byte_size(v_fst_94_);
v___x_119_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_119_, 0, v_fst_94_);
lean_ctor_set(v___x_119_, 1, v___x_117_);
lean_ctor_set(v___x_119_, 2, v___x_118_);
lean_inc_ref(v___x_119_);
v_it_120_ = l_String_Slice_splitToSubslice___redArg(v___x_119_, v___f_116_);
v___x_121_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__3));
v___x_122_ = lean_unsigned_to_nat(1u);
v___x_123_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___boxed__const__1;
v___f_124_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_124_, 0, v___x_121_);
lean_closure_set(v___f_124_, 1, v___x_117_);
lean_closure_set(v___f_124_, 2, v___x_122_);
lean_closure_set(v___f_124_, 3, v_fst_94_);
lean_closure_set(v___f_124_, 4, v___x_118_);
lean_closure_set(v___f_124_, 5, v___x_123_);
lean_closure_set(v___f_124_, 6, v___x_119_);
v___x_125_ = lean_box(0);
v___x_126_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_124_, v_it_120_, v___x_125_, lean_box(0));
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v___x_127_; 
v___x_127_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__4));
v___y_97_ = v___x_127_;
goto v___jp_96_;
}
else
{
lean_object* v_val_128_; 
v_val_128_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_val_128_);
lean_dec_ref_known(v___x_126_, 1);
v___y_97_ = v_val_128_;
goto v___jp_96_;
}
v___jp_96_:
{
lean_object* v_data_98_; lean_object* v_size_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_115_; 
v_data_98_ = lean_ctor_get(v_buffer_90_, 0);
v_size_99_ = lean_ctor_get(v_buffer_90_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_buffer_90_);
if (v_isSharedCheck_115_ == 0)
{
v___x_101_ = v_buffer_90_;
v_isShared_102_ = v_isSharedCheck_115_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_size_99_);
lean_inc(v_data_98_);
lean_dec(v_buffer_90_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_115_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_103_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0));
v___x_104_ = lean_string_append(v___y_97_, v___x_103_);
v___x_105_ = lean_string_append(v___x_104_, v_snd_95_);
lean_dec(v_snd_95_);
v___x_106_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1));
v___x_107_ = lean_string_append(v___x_105_, v___x_106_);
v___x_108_ = lean_string_to_utf8(v___x_107_);
lean_dec_ref(v___x_107_);
lean_inc_ref(v___x_108_);
v___x_109_ = lean_array_push(v_data_98_, v___x_108_);
v___x_110_ = lean_byte_array_size(v___x_108_);
lean_dec_ref(v___x_108_);
v___x_111_ = lean_nat_add(v_size_99_, v___x_110_);
lean_dec(v_size_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_111_);
lean_ctor_set(v___x_101_, 0, v___x_109_);
v___x_113_ = v___x_101_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg(lean_object* v_h_129_){
_start:
{
lean_object* v___f_130_; 
v___f_130_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1), 3, 1);
lean_closure_set(v___f_130_, 0, v_h_129_);
return v___f_130_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader(lean_object* v_00_u03b1_131_, lean_object* v_h_132_){
_start:
{
lean_object* v___f_133_; 
v___f_133_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1), 3, 1);
lean_closure_set(v___f_133_, 0, v_h_132_);
return v___f_133_;
}
}
lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg(){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___closed__0));
return v___x_137_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_138_;
v_res_138_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg();
stack->m_obj
 = v_res_138_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___boxed(lean_object* v___dummy_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg();
return v_res_140_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg();
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(lean_object* v_s_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(lean_object* v_s_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v_s_144_);
lean_dec_ref(v_s_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(lean_object* v_s_146_, lean_object* v_p_147_){
_start:
{
uint32_t v___y_149_; lean_object* v___x_154_; uint8_t v_decide_155_; 
v___x_154_ = lean_string_utf8_byte_size(v_s_146_);
v_decide_155_ = lean_nat_dec_eq(v_p_147_, v___x_154_);
if (v_decide_155_ == 0)
{
uint32_t v___x_156_; uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_156_ = lean_string_utf8_get_fast(v_s_146_, v_p_147_);
v___x_157_ = 65;
v___x_158_ = lean_uint32_dec_le(v___x_157_, v___x_156_);
if (v___x_158_ == 0)
{
v___y_149_ = v___x_156_;
goto v___jp_148_;
}
else
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 90;
v___x_160_ = lean_uint32_dec_le(v___x_156_, v___x_159_);
if (v___x_160_ == 0)
{
v___y_149_ = v___x_156_;
goto v___jp_148_;
}
else
{
uint32_t v___x_161_; uint32_t v___x_162_; 
v___x_161_ = 32;
v___x_162_ = lean_uint32_add(v___x_156_, v___x_161_);
v___y_149_ = v___x_162_;
goto v___jp_148_;
}
}
}
else
{
lean_dec(v_p_147_);
return v_s_146_;
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
lean_inc(v_p_147_);
v___x_150_ = lean_string_utf8_set(v_s_146_, v_p_147_, v___y_149_);
v___x_151_ = l_Char_utf8Size(v___y_149_);
v___x_152_ = lean_nat_add(v_p_147_, v___x_151_);
lean_dec(v___x_151_);
lean_dec(v_p_147_);
v_s_146_ = v___x_150_;
v_p_147_ = v___x_152_;
goto _start;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t v_sz_163_, size_t v_i_164_, lean_object* v_bs_165_){
_start:
{
uint8_t v___x_166_; 
v___x_166_ = lean_usize_dec_lt(v_i_164_, v_sz_163_);
if (v___x_166_ == 0)
{
return v_bs_165_;
}
else
{
lean_object* v_v_167_; lean_object* v___x_168_; lean_object* v_bs_x27_169_; lean_object* v___x_170_; lean_object* v___x_171_; size_t v___x_172_; size_t v___x_173_; lean_object* v___x_174_; 
v_v_167_ = lean_array_uget(v_bs_165_, v_i_164_);
v___x_168_ = lean_unsigned_to_nat(0u);
v_bs_x27_169_ = lean_array_uset(v_bs_165_, v_i_164_, v___x_168_);
v___x_170_ = l_String_Slice_toString(v_v_167_);
lean_dec(v_v_167_);
v___x_171_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_170_, v___x_168_);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_add(v_i_164_, v___x_172_);
v___x_174_ = lean_array_uset(v_bs_x27_169_, v_i_164_, v___x_171_);
v_i_164_ = v___x_173_;
v_bs_165_ = v___x_174_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_163_ = stack[0].m_num;
size_t v_i_164_ = stack[1].m_num;
lean_object* v_bs_165_ = stack[2].m_obj;
lean_object* v_res_176_;
v_res_176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_163_, v_i_164_, v_bs_165_);
stack->m_obj
 = v_res_176_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(lean_object* v_sz_177_, lean_object* v_i_178_, lean_object* v_bs_179_){
_start:
{
size_t v_sz_boxed_180_; size_t v_i_boxed_181_; lean_object* v_res_182_; 
v_sz_boxed_180_ = lean_unbox_usize(v_sz_177_);
lean_dec(v_sz_177_);
v_i_boxed_181_ = lean_unbox_usize(v_i_178_);
lean_dec(v_i_178_);
v_res_182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_boxed_180_, v_i_boxed_181_, v_bs_179_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(lean_object* v___x_183_, lean_object* v___x_184_, lean_object* v___x_185_, lean_object* v_a_186_, lean_object* v_b_187_){
_start:
{
lean_object* v_it_189_; lean_object* v_startInclusive_190_; lean_object* v_endExclusive_191_; 
if (lean_obj_tag(v_a_186_) == 0)
{
lean_object* v_currPos_196_; lean_object* v_searcher_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_226_; 
v_currPos_196_ = lean_ctor_get(v_a_186_, 0);
v_searcher_197_ = lean_ctor_get(v_a_186_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_a_186_);
if (v_isSharedCheck_226_ == 0)
{
v___x_199_ = v_a_186_;
v_isShared_200_ = v_isSharedCheck_226_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_searcher_197_);
lean_inc(v_currPos_196_);
lean_dec(v_a_186_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_226_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v_str_201_; lean_object* v_startInclusive_202_; lean_object* v_endExclusive_203_; lean_object* v___x_204_; uint8_t v_decide_205_; 
v_str_201_ = lean_ctor_get(v___x_184_, 0);
v_startInclusive_202_ = lean_ctor_get(v___x_184_, 1);
v_endExclusive_203_ = lean_ctor_get(v___x_184_, 2);
v___x_204_ = lean_nat_sub(v_endExclusive_203_, v_startInclusive_202_);
v_decide_205_ = lean_nat_dec_eq(v_searcher_197_, v___x_204_);
lean_dec(v___x_204_);
if (v_decide_205_ == 0)
{
lean_object* v___x_206_; uint32_t v___x_207_; uint32_t v___x_208_; uint8_t v___x_209_; 
v___x_206_ = lean_nat_add(v_startInclusive_202_, v_searcher_197_);
v___x_207_ = lean_string_utf8_get_fast(v_str_201_, v___x_206_);
v___x_208_ = 44;
v___x_209_ = lean_uint32_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
lean_dec(v_searcher_197_);
v___x_210_ = lean_string_utf8_next_fast(v_str_201_, v___x_206_);
lean_dec(v___x_206_);
v___x_211_ = lean_nat_sub(v___x_210_, v_startInclusive_202_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v___x_211_);
v___x_213_ = v___x_199_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_currPos_196_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_211_);
v___x_213_ = v_reuseFailAlloc_215_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
v_a_186_ = v___x_213_;
goto _start;
}
}
else
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_slice_219_; lean_object* v_nextIt_221_; 
v___x_216_ = lean_string_utf8_next_fast(v_str_201_, v___x_206_);
v___x_217_ = lean_nat_sub(v___x_216_, v___x_206_);
lean_dec(v___x_206_);
v___x_218_ = lean_nat_add(v_searcher_197_, v___x_217_);
lean_dec(v___x_217_);
v_slice_219_ = l_String_Slice_subslice_x21(v___x_184_, v_currPos_196_, v_searcher_197_);
lean_inc(v___x_218_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v___x_218_);
lean_ctor_set(v___x_199_, 0, v___x_218_);
v_nextIt_221_ = v___x_199_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v___x_218_);
v_nextIt_221_ = v_reuseFailAlloc_224_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
lean_object* v_startInclusive_222_; lean_object* v_endExclusive_223_; 
v_startInclusive_222_ = lean_ctor_get(v_slice_219_, 0);
lean_inc(v_startInclusive_222_);
v_endExclusive_223_ = lean_ctor_get(v_slice_219_, 1);
lean_inc(v_endExclusive_223_);
lean_dec_ref(v_slice_219_);
v_it_189_ = v_nextIt_221_;
v_startInclusive_190_ = v_startInclusive_222_;
v_endExclusive_191_ = v_endExclusive_223_;
goto v___jp_188_;
}
}
}
else
{
lean_object* v___x_225_; 
lean_del_object(v___x_199_);
lean_dec(v_searcher_197_);
v___x_225_ = lean_box(1);
lean_inc(v___x_185_);
v_it_189_ = v___x_225_;
v_startInclusive_190_ = v_currPos_196_;
v_endExclusive_191_ = v___x_185_;
goto v___jp_188_;
}
}
}
else
{
lean_dec(v___x_185_);
lean_dec_ref(v___x_183_);
return v_b_187_;
}
v___jp_188_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_inc_ref(v___x_183_);
v___x_192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_183_);
lean_ctor_set(v___x_192_, 1, v_startInclusive_190_);
lean_ctor_set(v___x_192_, 2, v_endExclusive_191_);
v___x_193_ = l_String_Slice_trimAscii(v___x_192_);
v___x_194_ = lean_array_push(v_b_187_, v___x_193_);
v_a_186_ = v_it_189_;
v_b_187_ = v___x_194_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(lean_object* v___x_227_, lean_object* v___x_228_, lean_object* v___x_229_, lean_object* v_a_230_, lean_object* v_b_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_227_, v___x_228_, v___x_229_, v_a_230_, v_b_231_);
lean_dec_ref(v___x_228_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(lean_object* v___x_233_, lean_object* v___x_234_, lean_object* v___x_235_, lean_object* v_a_236_, lean_object* v_b_237_){
_start:
{
lean_object* v_it_239_; lean_object* v_startInclusive_240_; lean_object* v_endExclusive_241_; 
if (lean_obj_tag(v_a_236_) == 0)
{
lean_object* v_currPos_246_; lean_object* v_searcher_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_276_; 
v_currPos_246_ = lean_ctor_get(v_a_236_, 0);
v_searcher_247_ = lean_ctor_get(v_a_236_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_a_236_);
if (v_isSharedCheck_276_ == 0)
{
v___x_249_ = v_a_236_;
v_isShared_250_ = v_isSharedCheck_276_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_searcher_247_);
lean_inc(v_currPos_246_);
lean_dec(v_a_236_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_276_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_str_251_; lean_object* v_startInclusive_252_; lean_object* v_endExclusive_253_; lean_object* v___x_254_; uint8_t v_decide_255_; 
v_str_251_ = lean_ctor_get(v___x_234_, 0);
v_startInclusive_252_ = lean_ctor_get(v___x_234_, 1);
v_endExclusive_253_ = lean_ctor_get(v___x_234_, 2);
v___x_254_ = lean_nat_sub(v_endExclusive_253_, v_startInclusive_252_);
v_decide_255_ = lean_nat_dec_eq(v_searcher_247_, v___x_254_);
lean_dec(v___x_254_);
if (v_decide_255_ == 0)
{
lean_object* v___x_256_; uint32_t v___x_257_; uint32_t v___x_258_; uint8_t v___x_259_; 
v___x_256_ = lean_nat_add(v_startInclusive_252_, v_searcher_247_);
v___x_257_ = lean_string_utf8_get_fast(v_str_251_, v___x_256_);
v___x_258_ = 44;
v___x_259_ = lean_uint32_dec_eq(v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
lean_dec(v_searcher_247_);
v___x_260_ = lean_string_utf8_next_fast(v_str_251_, v___x_256_);
lean_dec(v___x_256_);
v___x_261_ = lean_nat_sub(v___x_260_, v_startInclusive_252_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v___x_261_);
v___x_263_ = v___x_249_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_currPos_246_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
lean_object* v___x_264_; 
v___x_264_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_233_, v___x_234_, v___x_235_, v___x_263_, v_b_237_);
return v___x_264_;
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_slice_269_; lean_object* v_nextIt_271_; 
v___x_266_ = lean_string_utf8_next_fast(v_str_251_, v___x_256_);
v___x_267_ = lean_nat_sub(v___x_266_, v___x_256_);
lean_dec(v___x_256_);
v___x_268_ = lean_nat_add(v_searcher_247_, v___x_267_);
lean_dec(v___x_267_);
v_slice_269_ = l_String_Slice_subslice_x21(v___x_234_, v_currPos_246_, v_searcher_247_);
lean_inc(v___x_268_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v___x_268_);
lean_ctor_set(v___x_249_, 0, v___x_268_);
v_nextIt_271_ = v___x_249_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_268_);
v_nextIt_271_ = v_reuseFailAlloc_274_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v_startInclusive_272_; lean_object* v_endExclusive_273_; 
v_startInclusive_272_ = lean_ctor_get(v_slice_269_, 0);
lean_inc(v_startInclusive_272_);
v_endExclusive_273_ = lean_ctor_get(v_slice_269_, 1);
lean_inc(v_endExclusive_273_);
lean_dec_ref(v_slice_269_);
v_it_239_ = v_nextIt_271_;
v_startInclusive_240_ = v_startInclusive_272_;
v_endExclusive_241_ = v_endExclusive_273_;
goto v___jp_238_;
}
}
}
else
{
lean_object* v___x_275_; 
lean_del_object(v___x_249_);
lean_dec(v_searcher_247_);
v___x_275_ = lean_box(1);
lean_inc(v___x_235_);
v_it_239_ = v___x_275_;
v_startInclusive_240_ = v_currPos_246_;
v_endExclusive_241_ = v___x_235_;
goto v___jp_238_;
}
}
}
else
{
lean_dec(v___x_235_);
lean_dec_ref(v___x_233_);
return v_b_237_;
}
v___jp_238_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_inc_ref(v___x_233_);
v___x_242_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_242_, 0, v___x_233_);
lean_ctor_set(v___x_242_, 1, v_startInclusive_240_);
lean_ctor_set(v___x_242_, 2, v_endExclusive_241_);
v___x_243_ = l_String_Slice_trimAscii(v___x_242_);
v___x_244_ = lean_array_push(v_b_237_, v___x_243_);
v___x_245_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_233_, v___x_234_, v___x_235_, v_it_239_, v___x_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(lean_object* v___x_277_, lean_object* v___x_278_, lean_object* v___x_279_, lean_object* v_a_280_, lean_object* v_b_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_277_, v___x_278_, v___x_279_, v_a_280_, v_b_281_);
lean_dec_ref(v___x_278_);
return v_res_282_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object* v___x_283_, lean_object* v___x_284_, lean_object* v___x_285_, lean_object* v_a_286_, uint8_t v_b_287_){
_start:
{
if (lean_obj_tag(v_a_286_) == 0)
{
lean_object* v_currPos_288_; lean_object* v_searcher_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_332_; 
v_currPos_288_ = lean_ctor_get(v_a_286_, 0);
v_searcher_289_ = lean_ctor_get(v_a_286_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_a_286_);
if (v_isSharedCheck_332_ == 0)
{
v___x_291_ = v_a_286_;
v_isShared_292_ = v_isSharedCheck_332_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_searcher_289_);
lean_inc(v_currPos_288_);
lean_dec(v_a_286_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_332_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_str_293_; lean_object* v_startInclusive_294_; lean_object* v_endExclusive_295_; uint8_t v___x_296_; lean_object* v_it_298_; lean_object* v_startInclusive_299_; lean_object* v_endExclusive_300_; lean_object* v___x_310_; uint8_t v_decide_311_; 
v_str_293_ = lean_ctor_get(v___x_284_, 0);
v_startInclusive_294_ = lean_ctor_get(v___x_284_, 1);
v_endExclusive_295_ = lean_ctor_get(v___x_284_, 2);
v___x_296_ = 1;
v___x_310_ = lean_nat_sub(v_endExclusive_295_, v_startInclusive_294_);
v_decide_311_ = lean_nat_dec_eq(v_searcher_289_, v___x_310_);
lean_dec(v___x_310_);
if (v_decide_311_ == 0)
{
lean_object* v___x_312_; uint32_t v___x_313_; uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_312_ = lean_nat_add(v_startInclusive_294_, v_searcher_289_);
v___x_313_ = lean_string_utf8_get_fast(v_str_293_, v___x_312_);
v___x_314_ = 44;
v___x_315_ = lean_uint32_dec_eq(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
lean_dec(v_searcher_289_);
v___x_316_ = lean_string_utf8_next_fast(v_str_293_, v___x_312_);
lean_dec(v___x_312_);
v___x_317_ = lean_nat_sub(v___x_316_, v_startInclusive_294_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v___x_317_);
v___x_319_ = v___x_291_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_currPos_288_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_317_);
v___x_319_ = v_reuseFailAlloc_321_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
v_a_286_ = v___x_319_;
goto _start;
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_slice_325_; lean_object* v_nextIt_327_; 
v___x_322_ = lean_string_utf8_next_fast(v_str_293_, v___x_312_);
v___x_323_ = lean_nat_sub(v___x_322_, v___x_312_);
lean_dec(v___x_312_);
v___x_324_ = lean_nat_add(v_searcher_289_, v___x_323_);
lean_dec(v___x_323_);
v_slice_325_ = l_String_Slice_subslice_x21(v___x_284_, v_currPos_288_, v_searcher_289_);
lean_inc(v___x_324_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v___x_324_);
lean_ctor_set(v___x_291_, 0, v___x_324_);
v_nextIt_327_ = v___x_291_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_324_);
v_nextIt_327_ = v_reuseFailAlloc_330_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v_startInclusive_328_; lean_object* v_endExclusive_329_; 
v_startInclusive_328_ = lean_ctor_get(v_slice_325_, 0);
lean_inc(v_startInclusive_328_);
v_endExclusive_329_ = lean_ctor_get(v_slice_325_, 1);
lean_inc(v_endExclusive_329_);
lean_dec_ref(v_slice_325_);
v_it_298_ = v_nextIt_327_;
v_startInclusive_299_ = v_startInclusive_328_;
v_endExclusive_300_ = v_endExclusive_329_;
goto v___jp_297_;
}
}
}
else
{
lean_object* v___x_331_; 
lean_del_object(v___x_291_);
lean_dec(v_searcher_289_);
v___x_331_ = lean_box(1);
lean_inc(v___x_285_);
v_it_298_ = v___x_331_;
v_startInclusive_299_ = v_currPos_288_;
v_endExclusive_300_ = v___x_285_;
goto v___jp_297_;
}
v___jp_297_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v_startInclusive_303_; lean_object* v_endExclusive_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
lean_inc_ref(v___x_283_);
v___x_301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_301_, 0, v___x_283_);
lean_ctor_set(v___x_301_, 1, v_startInclusive_299_);
lean_ctor_set(v___x_301_, 2, v_endExclusive_300_);
v___x_302_ = l_String_Slice_trimAscii(v___x_301_);
v_startInclusive_303_ = lean_ctor_get(v___x_302_, 1);
lean_inc(v_startInclusive_303_);
v_endExclusive_304_ = lean_ctor_get(v___x_302_, 2);
lean_inc(v_endExclusive_304_);
lean_dec_ref(v___x_302_);
v___x_305_ = lean_nat_sub(v_endExclusive_304_, v_startInclusive_303_);
lean_dec(v_startInclusive_303_);
lean_dec(v_endExclusive_304_);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_nat_dec_eq(v___x_305_, v___x_306_);
lean_dec(v___x_305_);
if (v___x_307_ == 0)
{
v_a_286_ = v_it_298_;
v_b_287_ = v___x_296_;
goto _start;
}
else
{
uint8_t v___x_309_; 
lean_dec(v_it_298_);
lean_dec(v___x_285_);
lean_dec_ref(v___x_283_);
v___x_309_ = 0;
return v___x_309_;
}
}
}
}
else
{
lean_dec(v___x_285_);
lean_dec_ref(v___x_283_);
return v_b_287_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_283_ = stack[0].m_obj;
lean_object* v___x_284_ = stack[1].m_obj;
lean_object* v___x_285_ = stack[2].m_obj;
lean_object* v_a_286_ = stack[3].m_obj;
uint8_t v_b_287_ = stack[4].m_num;
uint8_t v_res_333_;
v_res_333_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_283_, v___x_284_, v___x_285_, v_a_286_, v_b_287_);
stack->m_num = v_res_333_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object* v___x_334_, lean_object* v___x_335_, lean_object* v___x_336_, lean_object* v_a_337_, lean_object* v_b_338_){
_start:
{
uint8_t v_b_boxed_339_; uint8_t v_res_340_; lean_object* v_r_341_; 
v_b_boxed_339_ = lean_unbox(v_b_338_);
v_res_340_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_334_, v___x_335_, v___x_336_, v_a_337_, v_b_boxed_339_);
lean_dec_ref(v___x_335_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object* v___x_342_, lean_object* v___x_343_, lean_object* v___x_344_, lean_object* v_a_345_, uint8_t v_b_346_){
_start:
{
if (lean_obj_tag(v_a_345_) == 0)
{
lean_object* v_currPos_347_; lean_object* v_searcher_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_391_; 
v_currPos_347_ = lean_ctor_get(v_a_345_, 0);
v_searcher_348_ = lean_ctor_get(v_a_345_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_a_345_);
if (v_isSharedCheck_391_ == 0)
{
v___x_350_ = v_a_345_;
v_isShared_351_ = v_isSharedCheck_391_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_searcher_348_);
lean_inc(v_currPos_347_);
lean_dec(v_a_345_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_391_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v_str_352_; lean_object* v_startInclusive_353_; lean_object* v_endExclusive_354_; uint8_t v___x_355_; lean_object* v_it_357_; lean_object* v_startInclusive_358_; lean_object* v_endExclusive_359_; lean_object* v___x_369_; uint8_t v_decide_370_; 
v_str_352_ = lean_ctor_get(v___x_343_, 0);
v_startInclusive_353_ = lean_ctor_get(v___x_343_, 1);
v_endExclusive_354_ = lean_ctor_get(v___x_343_, 2);
v___x_355_ = 1;
v___x_369_ = lean_nat_sub(v_endExclusive_354_, v_startInclusive_353_);
v_decide_370_ = lean_nat_dec_eq(v_searcher_348_, v___x_369_);
lean_dec(v___x_369_);
if (v_decide_370_ == 0)
{
lean_object* v___x_371_; uint32_t v___x_372_; uint32_t v___x_373_; uint8_t v___x_374_; 
v___x_371_ = lean_nat_add(v_startInclusive_353_, v_searcher_348_);
v___x_372_ = lean_string_utf8_get_fast(v_str_352_, v___x_371_);
v___x_373_ = 44;
v___x_374_ = lean_uint32_dec_eq(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
lean_dec(v_searcher_348_);
v___x_375_ = lean_string_utf8_next_fast(v_str_352_, v___x_371_);
lean_dec(v___x_371_);
v___x_376_ = lean_nat_sub(v___x_375_, v_startInclusive_353_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___x_376_);
v___x_378_ = v___x_350_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_currPos_347_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
uint8_t v___x_379_; 
v___x_379_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_342_, v___x_343_, v___x_344_, v___x_378_, v_b_346_);
return v___x_379_;
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v_slice_384_; lean_object* v_nextIt_386_; 
v___x_381_ = lean_string_utf8_next_fast(v_str_352_, v___x_371_);
v___x_382_ = lean_nat_sub(v___x_381_, v___x_371_);
lean_dec(v___x_371_);
v___x_383_ = lean_nat_add(v_searcher_348_, v___x_382_);
lean_dec(v___x_382_);
v_slice_384_ = l_String_Slice_subslice_x21(v___x_343_, v_currPos_347_, v_searcher_348_);
lean_inc(v___x_383_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___x_383_);
lean_ctor_set(v___x_350_, 0, v___x_383_);
v_nextIt_386_ = v___x_350_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_383_);
v_nextIt_386_ = v_reuseFailAlloc_389_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v_startInclusive_387_; lean_object* v_endExclusive_388_; 
v_startInclusive_387_ = lean_ctor_get(v_slice_384_, 0);
lean_inc(v_startInclusive_387_);
v_endExclusive_388_ = lean_ctor_get(v_slice_384_, 1);
lean_inc(v_endExclusive_388_);
lean_dec_ref(v_slice_384_);
v_it_357_ = v_nextIt_386_;
v_startInclusive_358_ = v_startInclusive_387_;
v_endExclusive_359_ = v_endExclusive_388_;
goto v___jp_356_;
}
}
}
else
{
lean_object* v___x_390_; 
lean_del_object(v___x_350_);
lean_dec(v_searcher_348_);
v___x_390_ = lean_box(1);
lean_inc(v___x_344_);
v_it_357_ = v___x_390_;
v_startInclusive_358_ = v_currPos_347_;
v_endExclusive_359_ = v___x_344_;
goto v___jp_356_;
}
v___jp_356_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_startInclusive_362_; lean_object* v_endExclusive_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
lean_inc_ref(v___x_342_);
v___x_360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_360_, 0, v___x_342_);
lean_ctor_set(v___x_360_, 1, v_startInclusive_358_);
lean_ctor_set(v___x_360_, 2, v_endExclusive_359_);
v___x_361_ = l_String_Slice_trimAscii(v___x_360_);
v_startInclusive_362_ = lean_ctor_get(v___x_361_, 1);
lean_inc(v_startInclusive_362_);
v_endExclusive_363_ = lean_ctor_get(v___x_361_, 2);
lean_inc(v_endExclusive_363_);
lean_dec_ref(v___x_361_);
v___x_364_ = lean_nat_sub(v_endExclusive_363_, v_startInclusive_362_);
lean_dec(v_startInclusive_362_);
lean_dec(v_endExclusive_363_);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_nat_dec_eq(v___x_364_, v___x_365_);
lean_dec(v___x_364_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; 
v___x_367_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_342_, v___x_343_, v___x_344_, v_it_357_, v___x_355_);
return v___x_367_;
}
else
{
uint8_t v___x_368_; 
lean_dec(v_it_357_);
lean_dec(v___x_344_);
lean_dec_ref(v___x_342_);
v___x_368_ = 0;
return v___x_368_;
}
}
}
}
else
{
lean_dec(v___x_344_);
lean_dec_ref(v___x_342_);
return v_b_346_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_342_ = stack[0].m_obj;
lean_object* v___x_343_ = stack[1].m_obj;
lean_object* v___x_344_ = stack[2].m_obj;
lean_object* v_a_345_ = stack[3].m_obj;
uint8_t v_b_346_ = stack[4].m_num;
uint8_t v_res_392_;
v_res_392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_342_, v___x_343_, v___x_344_, v_a_345_, v_b_346_);
stack->m_num = v_res_392_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object* v___x_393_, lean_object* v___x_394_, lean_object* v___x_395_, lean_object* v_a_396_, lean_object* v_b_397_){
_start:
{
uint8_t v_b_boxed_398_; uint8_t v_res_399_; lean_object* v_r_400_; 
v_b_boxed_398_ = lean_unbox(v_b_397_);
v_res_399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_393_, v___x_394_, v___x_395_, v_a_396_, v_b_boxed_398_);
lean_dec_ref(v___x_394_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object* v_v_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_parts_407_; uint8_t v___x_408_; uint8_t v___x_409_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_string_utf8_byte_size(v_v_403_);
lean_inc_ref_n(v_v_403_, 2);
v___x_406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_406_, 0, v_v_403_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
lean_ctor_set(v___x_406_, 2, v___x_405_);
v_parts_407_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
v___x_408_ = 1;
v___x_409_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_403_, v___x_406_, v___x_405_, v_parts_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
lean_dec_ref_known(v___x_406_, 3);
lean_dec_ref(v_v_403_);
v___x_410_ = lean_box(0);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; size_t v_sz_413_; size_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_411_ = ((lean_object*)(l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0));
v___x_412_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v_v_403_, v___x_406_, v___x_405_, v_parts_407_, v___x_411_);
lean_dec_ref_known(v___x_406_, 3);
v_sz_413_ = lean_array_size(v___x_412_);
v___x_414_ = ((size_t)0ULL);
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_413_, v___x_414_, v___x_412_);
v___x_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object* v___x_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v_inst_420_, lean_object* v_R_421_, lean_object* v_a_422_, uint8_t v_b_423_, lean_object* v_c_424_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_417_, v___x_418_, v___x_419_, v_a_422_, v_b_423_);
return v___x_425_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_417_ = stack[0].m_obj;
lean_object* v___x_418_ = stack[1].m_obj;
lean_object* v___x_419_ = stack[2].m_obj;
lean_object* v_a_422_ = stack[5].m_obj;
uint8_t v_b_423_ = stack[6].m_num;
uint8_t v_res_426_;
v_res_426_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_417_, v___x_418_, v___x_419_, lean_box(0), lean_box(0), v_a_422_, v_b_423_, lean_box(0));
stack->m_num = v_res_426_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v___x_429_, lean_object* v_inst_430_, lean_object* v_R_431_, lean_object* v_a_432_, lean_object* v_b_433_, lean_object* v_c_434_){
_start:
{
uint8_t v_b_boxed_435_; uint8_t v_res_436_; lean_object* v_r_437_; 
v_b_boxed_435_ = lean_unbox(v_b_433_);
v_res_436_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_427_, v___x_428_, v___x_429_, v_inst_430_, v_R_431_, v_a_432_, v_b_boxed_435_, v_c_434_);
lean_dec_ref(v___x_428_);
v_r_437_ = lean_box(v_res_436_);
return v_r_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v___x_440_, lean_object* v_inst_441_, lean_object* v_R_442_, lean_object* v_a_443_, lean_object* v_b_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_438_, v___x_439_, v___x_440_, v_a_443_, v_b_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object* v___x_446_, lean_object* v___x_447_, lean_object* v___x_448_, lean_object* v_inst_449_, lean_object* v_R_450_, lean_object* v_a_451_, lean_object* v_b_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_446_, v___x_447_, v___x_448_, v_inst_449_, v_R_450_, v_a_451_, v_b_452_);
lean_dec_ref(v___x_447_);
return v_res_453_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object* v___x_454_, lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v_inst_457_, lean_object* v_R_458_, lean_object* v_a_459_, uint8_t v_b_460_, lean_object* v_c_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_454_, v___x_455_, v___x_456_, v_a_459_, v_b_460_);
return v___x_462_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_454_ = stack[0].m_obj;
lean_object* v___x_455_ = stack[1].m_obj;
lean_object* v___x_456_ = stack[2].m_obj;
lean_object* v_a_459_ = stack[5].m_obj;
uint8_t v_b_460_ = stack[6].m_num;
uint8_t v_res_463_;
v_res_463_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_454_, v___x_455_, v___x_456_, lean_box(0), lean_box(0), v_a_459_, v_b_460_, lean_box(0));
stack->m_num = v_res_463_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object* v___x_464_, lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v_inst_467_, lean_object* v_R_468_, lean_object* v_a_469_, lean_object* v_b_470_, lean_object* v_c_471_){
_start:
{
uint8_t v_b_boxed_472_; uint8_t v_res_473_; lean_object* v_r_474_; 
v_b_boxed_472_ = lean_unbox(v_b_470_);
v_res_473_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_464_, v___x_465_, v___x_466_, v_inst_467_, v_R_468_, v_a_469_, v_b_boxed_472_, v_c_471_);
lean_dec_ref(v___x_465_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object* v___x_475_, lean_object* v___x_476_, lean_object* v___x_477_, lean_object* v_inst_478_, lean_object* v_R_479_, lean_object* v_a_480_, lean_object* v_b_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_475_, v___x_476_, v___x_477_, v_a_480_, v_b_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object* v___x_483_, lean_object* v___x_484_, lean_object* v___x_485_, lean_object* v_inst_486_, lean_object* v_R_487_, lean_object* v_a_488_, lean_object* v_b_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(v___x_483_, v___x_484_, v___x_485_, v_inst_486_, v_R_487_, v_a_488_, v_b_489_);
lean_dec_ref(v___x_484_);
return v_res_490_;
}
}
uint8_t l_Std_Http_Header_instBEqContentLength_beq(lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
uint8_t v___x_493_; 
v___x_493_ = lean_nat_dec_eq(v_x_491_, v_x_492_);
return v___x_493_;
}
}
LEAN_EXPORT void l_Std_Http_Header_instBEqContentLength_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_491_ = stack[0].m_obj;
lean_object* v_x_492_ = stack[1].m_obj;
uint8_t v_res_494_;
v_res_494_ = l_Std_Http_Header_instBEqContentLength_beq(v_x_491_, v_x_492_);
stack->m_num = v_res_494_;
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
uint8_t l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object* v_x_605_, lean_object* v_x_606_){
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
LEAN_EXPORT void l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_605_ = stack[0].m_obj;
lean_object* v_x_606_ = stack[1].m_obj;
uint8_t v_res_613_;
v_res_613_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_605_, v_x_606_);
stack->m_num = v_res_613_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
uint8_t v_res_616_; lean_object* v_r_617_; 
v_res_616_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_614_, v_x_615_);
lean_dec(v_x_615_);
lean_dec(v_x_614_);
v_r_617_ = lean_box(v_res_616_);
return v_r_617_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object* v_as_619_, size_t v_i_620_, size_t v_stop_621_, lean_object* v_b_622_){
_start:
{
lean_object* v___y_624_; uint8_t v___x_628_; 
v___x_628_ = lean_usize_dec_eq(v_i_620_, v_stop_621_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_array_uget_borrowed(v_as_619_, v_i_620_);
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_631_ = lean_string_dec_eq(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
v___y_624_ = v_b_622_;
goto v___jp_623_;
}
else
{
lean_object* v___x_632_; 
lean_inc(v___x_629_);
v___x_632_ = lean_array_push(v_b_622_, v___x_629_);
v___y_624_ = v___x_632_;
goto v___jp_623_;
}
}
else
{
return v_b_622_;
}
v___jp_623_:
{
size_t v___x_625_; size_t v___x_626_; 
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_i_620_, v___x_625_);
v_i_620_ = v___x_626_;
v_b_622_ = v___y_624_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_619_ = stack[0].m_obj;
size_t v_i_620_ = stack[1].m_num;
size_t v_stop_621_ = stack[2].m_num;
lean_object* v_b_622_ = stack[3].m_obj;
lean_object* v_res_633_;
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_619_, v_i_620_, v_stop_621_, v_b_622_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object* v_as_634_, lean_object* v_i_635_, lean_object* v_stop_636_, lean_object* v_b_637_){
_start:
{
size_t v_i_boxed_638_; size_t v_stop_boxed_639_; lean_object* v_res_640_; 
v_i_boxed_638_ = lean_unbox_usize(v_i_635_);
lean_dec(v_i_635_);
v_stop_boxed_639_ = lean_unbox_usize(v_stop_636_);
lean_dec(v_stop_636_);
v_res_640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_634_, v_i_boxed_638_, v_stop_boxed_639_, v_b_637_);
lean_dec_ref(v_as_634_);
return v_res_640_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object* v___x_641_, lean_object* v_as_642_, size_t v_i_643_, size_t v_stop_644_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = lean_usize_dec_eq(v_i_643_, v_stop_644_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = 1;
v___x_647_ = lean_array_uget_borrowed(v_as_642_, v_i_643_);
lean_inc(v___x_647_);
v___x_648_ = l_Std_Http_Internal_isToken(v___x_647_);
if (v___x_648_ == 0)
{
return v___x_646_;
}
else
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_nat_dec_eq(v___x_641_, v___x_649_);
if (v___x_650_ == 0)
{
size_t v___x_651_; size_t v___x_652_; 
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_643_, v___x_651_);
v_i_643_ = v___x_652_;
goto _start;
}
else
{
return v___x_646_;
}
}
}
else
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_641_ = stack[0].m_obj;
lean_object* v_as_642_ = stack[1].m_obj;
size_t v_i_643_ = stack[2].m_num;
size_t v_stop_644_ = stack[3].m_num;
uint8_t v_res_655_;
v_res_655_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_641_, v_as_642_, v_i_643_, v_stop_644_);
stack->m_num = v_res_655_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object* v___x_656_, lean_object* v_as_657_, lean_object* v_i_658_, lean_object* v_stop_659_){
_start:
{
size_t v_i_boxed_660_; size_t v_stop_boxed_661_; uint8_t v_res_662_; lean_object* v_r_663_; 
v_i_boxed_660_ = lean_unbox_usize(v_i_658_);
lean_dec(v_i_658_);
v_stop_boxed_661_ = lean_unbox_usize(v_stop_659_);
lean_dec(v_stop_659_);
v_res_662_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_656_, v_as_657_, v_i_boxed_660_, v_stop_boxed_661_);
lean_dec_ref(v_as_657_);
lean_dec(v___x_656_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object* v_codings_668_){
_start:
{
uint8_t v___y_670_; lean_object* v___y_671_; uint8_t v___y_672_; lean_object* v___y_673_; uint8_t v___y_680_; uint8_t v___y_681_; lean_object* v___y_682_; uint8_t v___y_692_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_705_ = lean_array_get_size(v_codings_668_);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_nat_dec_eq(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
uint8_t v___x_708_; 
v___x_708_ = lean_nat_dec_lt(v___x_706_, v___x_705_);
if (v___x_708_ == 0)
{
v___y_692_ = v___x_708_;
goto v___jp_691_;
}
else
{
if (v___x_708_ == 0)
{
v___y_692_ = v___x_708_;
goto v___jp_691_;
}
else
{
size_t v___x_709_; size_t v___x_710_; uint8_t v___x_711_; 
v___x_709_ = ((size_t)0ULL);
v___x_710_ = lean_usize_of_nat(v___x_705_);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_705_, v_codings_668_, v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
v___y_692_ = v___x_711_;
goto v___jp_691_;
}
else
{
return v___x_707_;
}
}
}
}
else
{
uint8_t v___x_712_; 
v___x_712_ = 0;
return v___x_712_;
}
v___jp_669_:
{
lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_dec_lt(v___x_674_, v___y_671_);
if (v___x_675_ == 0)
{
uint8_t v___x_676_; 
v___x_676_ = lean_nat_dec_eq(v___y_671_, v___x_674_);
lean_dec(v___y_671_);
if (v___x_676_ == 0)
{
lean_dec(v___y_673_);
return v___y_672_;
}
else
{
lean_object* v___x_677_; uint8_t v_lastIsChunked_678_; 
v___x_677_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v_lastIsChunked_678_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_673_, v___x_677_);
lean_dec(v___y_673_);
if (v_lastIsChunked_678_ == 0)
{
return v___x_675_;
}
else
{
return v___y_672_;
}
}
}
else
{
lean_dec(v___y_673_);
lean_dec(v___y_671_);
return v___y_670_;
}
}
v___jp_679_:
{
lean_object* v_chunkedCount_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_chunkedCount_683_ = lean_array_get_size(v___y_682_);
lean_dec_ref(v___y_682_);
v___x_684_ = lean_array_get_size(v_codings_668_);
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_sub(v___x_684_, v___x_685_);
v___x_687_ = lean_nat_dec_lt(v___x_686_, v___x_684_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec(v___x_686_);
v___x_688_ = lean_box(0);
v___y_670_ = v___y_680_;
v___y_671_ = v_chunkedCount_683_;
v___y_672_ = v___y_681_;
v___y_673_ = v___x_688_;
goto v___jp_669_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_array_fget_borrowed(v_codings_668_, v___x_686_);
lean_dec(v___x_686_);
lean_inc(v___x_689_);
v___x_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
v___y_670_ = v___y_680_;
v___y_671_ = v_chunkedCount_683_;
v___y_672_ = v___y_681_;
v___y_673_ = v___x_690_;
goto v___jp_669_;
}
}
v___jp_691_:
{
uint8_t v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_693_ = 1;
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_array_get_size(v_codings_668_);
v___x_696_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__1));
v___x_697_ = lean_nat_dec_lt(v___x_694_, v___x_695_);
if (v___x_697_ == 0)
{
v___y_680_ = v___y_692_;
v___y_681_ = v___x_693_;
v___y_682_ = v___x_696_;
goto v___jp_679_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = lean_nat_dec_le(v___x_695_, v___x_695_);
if (v___x_698_ == 0)
{
if (v___x_697_ == 0)
{
v___y_680_ = v___y_692_;
v___y_681_ = v___x_693_;
v___y_682_ = v___x_696_;
goto v___jp_679_;
}
else
{
size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((size_t)0ULL);
v___x_700_ = lean_usize_of_nat(v___x_695_);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_668_, v___x_699_, v___x_700_, v___x_696_);
v___y_680_ = v___y_692_;
v___y_681_ = v___x_693_;
v___y_682_ = v___x_701_;
goto v___jp_679_;
}
}
else
{
size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
v___x_702_ = ((size_t)0ULL);
v___x_703_ = lean_usize_of_nat(v___x_695_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_668_, v___x_702_, v___x_703_, v___x_696_);
v___y_680_ = v___y_692_;
v___y_681_ = v___x_693_;
v___y_682_ = v___x_704_;
goto v___jp_679_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Http_Header_TransferEncoding_Validate_0interp(lean_interpreter_value* stack)
{
lean_object* v_codings_668_ = stack[0].m_obj;
uint8_t v_res_713_;
v_res_713_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_668_);
stack->m_num = v_res_713_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_Validate___boxed(lean_object* v_codings_714_){
_start:
{
uint8_t v_res_715_; lean_object* v_r_716_; 
v_res_715_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_714_);
lean_dec_ref(v_codings_714_);
v_r_716_ = lean_box(v_res_715_);
return v_r_716_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(lean_object* v___y_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = l_String_quote(v___y_717_);
v___x_719_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_x_722_){
_start:
{
if (lean_obj_tag(v_x_722_) == 0)
{
lean_dec(v_x_720_);
return v_x_721_;
}
else
{
lean_object* v_head_723_; lean_object* v_tail_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_735_; 
v_head_723_ = lean_ctor_get(v_x_722_, 0);
v_tail_724_ = lean_ctor_get(v_x_722_, 1);
v_isSharedCheck_735_ = !lean_is_exclusive(v_x_722_);
if (v_isSharedCheck_735_ == 0)
{
v___x_726_ = v_x_722_;
v_isShared_727_ = v_isSharedCheck_735_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_tail_724_);
lean_inc(v_head_723_);
lean_dec(v_x_722_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_735_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
lean_inc(v_x_720_);
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 5);
lean_ctor_set(v___x_726_, 1, v_x_720_);
lean_ctor_set(v___x_726_, 0, v_x_721_);
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_x_721_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_x_720_);
v___x_729_ = v_reuseFailAlloc_734_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = l_String_quote(v_head_723_);
v___x_731_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_729_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v_x_721_ = v___x_732_;
v_x_722_ = v_tail_724_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_x_738_){
_start:
{
if (lean_obj_tag(v_x_738_) == 0)
{
lean_dec(v_x_736_);
return v_x_737_;
}
else
{
lean_object* v_head_739_; lean_object* v_tail_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_751_; 
v_head_739_ = lean_ctor_get(v_x_738_, 0);
v_tail_740_ = lean_ctor_get(v_x_738_, 1);
v_isSharedCheck_751_ = !lean_is_exclusive(v_x_738_);
if (v_isSharedCheck_751_ == 0)
{
v___x_742_ = v_x_738_;
v_isShared_743_ = v_isSharedCheck_751_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_tail_740_);
lean_inc(v_head_739_);
lean_dec(v_x_738_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_751_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
lean_inc(v_x_736_);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 5);
lean_ctor_set(v___x_742_, 1, v_x_736_);
lean_ctor_set(v___x_742_, 0, v_x_737_);
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_x_737_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_x_736_);
v___x_745_ = v_reuseFailAlloc_750_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_746_ = l_String_quote(v_head_739_);
v___x_747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
v___x_748_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_745_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(v_x_736_, v___x_748_, v_tail_740_);
return v___x_749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(lean_object* v_x_752_, lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_752_) == 0)
{
lean_object* v___x_754_; 
lean_dec(v_x_753_);
v___x_754_ = lean_box(0);
return v___x_754_;
}
else
{
lean_object* v_tail_755_; 
v_tail_755_ = lean_ctor_get(v_x_752_, 1);
if (lean_obj_tag(v_tail_755_) == 0)
{
lean_object* v_head_756_; lean_object* v___x_757_; 
lean_dec(v_x_753_);
v_head_756_ = lean_ctor_get(v_x_752_, 0);
lean_inc(v_head_756_);
lean_dec_ref_known(v_x_752_, 2);
v___x_757_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_756_);
return v___x_757_;
}
else
{
lean_object* v_head_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
lean_inc(v_tail_755_);
v_head_758_ = lean_ctor_get(v_x_752_, 0);
lean_inc(v_head_758_);
lean_dec_ref_known(v_x_752_, 2);
v___x_759_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_758_);
v___x_760_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(v_x_753_, v___x_759_, v_tail_755_);
return v___x_760_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0));
v___x_770_ = lean_string_length(v___x_769_);
return v___x_770_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5);
v___x_772_ = lean_nat_to_int(v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(lean_object* v_xs_780_){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_781_ = lean_array_get_size(v_xs_780_);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_nat_dec_eq(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_784_ = lean_array_to_list(v_xs_780_);
v___x_785_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3));
v___x_786_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(v___x_784_, v___x_785_);
v___x_787_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6);
v___x_788_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7));
v___x_789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_786_);
v___x_790_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8));
v___x_791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_787_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Std_Format_fill(v___x_792_);
return v___x_793_;
}
else
{
lean_object* v___x_794_; 
lean_dec_ref(v_xs_780_);
v___x_794_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10));
return v___x_794_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_unsigned_to_nat(11u);
v___x_805_ = lean_nat_to_int(v___x_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg(lean_object* v_x_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_813_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_814_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3));
v___x_815_ = lean_obj_once(&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4, &l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4);
v___x_816_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_812_);
v___x_817_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = 0;
v___x_819_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*1, v___x_818_);
v___x_820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_814_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_box(1);
v___x_824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6));
v___x_826_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v___x_813_);
v___x_828_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_829_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_831_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_832_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
lean_ctor_set(v___x_832_, 1, v___x_829_);
v___x_833_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_834_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_832_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_830_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
v___x_836_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set_uint8(v___x_836_, sizeof(void*)*1, v___x_818_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr(lean_object* v_x_837_, lean_object* v_prec_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg(v_x_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___boxed(lean_object* v_x_840_, lean_object* v_prec_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_Http_Header_instReprTransferEncoding_repr(v_x_840_, v_prec_841_);
lean_dec(v_prec_841_);
return v_res_842_;
}
}
uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object* v_te_845_){
_start:
{
lean_object* v___y_847_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_850_ = lean_array_get_size(v_te_845_);
v___x_851_ = lean_unsigned_to_nat(1u);
v___x_852_ = lean_nat_sub(v___x_850_, v___x_851_);
v___x_853_ = lean_nat_dec_lt(v___x_852_, v___x_850_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
lean_dec(v___x_852_);
v___x_854_ = lean_box(0);
v___y_847_ = v___x_854_;
goto v___jp_846_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_array_fget_borrowed(v_te_845_, v___x_852_);
lean_dec(v___x_852_);
lean_inc(v___x_855_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
v___y_847_ = v___x_856_;
goto v___jp_846_;
}
v___jp_846_:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v___x_849_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_847_, v___x_848_);
lean_dec(v___y_847_);
return v___x_849_;
}
}
}
LEAN_EXPORT void l_Std_Http_Header_TransferEncoding_isChunked_0interp(lean_interpreter_value* stack)
{
lean_object* v_te_845_ = stack[0].m_obj;
uint8_t v_res_857_;
v_res_857_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_845_);
stack->m_num = v_res_857_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_isChunked___boxed(lean_object* v_te_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_858_);
lean_dec_ref(v_te_858_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object* v_v_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v___x_863_; 
v___x_863_ = lean_box(0);
return v___x_863_;
}
else
{
lean_object* v_val_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_873_; 
v_val_864_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_873_ == 0)
{
v___x_866_ = v___x_862_;
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_val_864_);
lean_dec(v___x_862_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_873_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___x_868_; 
v___x_868_ = l_Std_Http_Header_TransferEncoding_Validate(v_val_864_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_del_object(v___x_866_);
lean_dec(v_val_864_);
v___x_869_ = lean_box(0);
return v___x_869_;
}
else
{
lean_object* v___x_871_; 
if (v_isShared_867_ == 0)
{
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_val_864_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_serialize(lean_object* v_te_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v_value_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_875_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_876_ = lean_array_to_list(v_te_874_);
v_value_877_ = l_String_intercalate(v___x_875_, v___x_876_);
v___x_878_ = l_Std_Http_Header_Name_transferEncoding;
v___x_879_ = l_Std_Http_Header_Value_ofString_x21(v_value_877_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___redArg(lean_object* v_x_899_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_900_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_901_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__3));
v___x_902_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_903_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_899_);
v___x_904_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = 0;
v___x_906_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set_uint8(v___x_906_, sizeof(void*)*1, v___x_905_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_901_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_box(1);
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__5));
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_900_);
v___x_915_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_918_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v___x_916_);
v___x_920_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_917_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*1, v___x_905_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr(lean_object* v_x_924_, lean_object* v_prec_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Std_Http_Header_instReprConnection_repr___redArg(v_x_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___boxed(lean_object* v_x_927_, lean_object* v_prec_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_Http_Header_instReprConnection_repr(v_x_927_, v_prec_928_);
lean_dec(v_prec_928_);
return v_res_929_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(lean_object* v_token_932_, lean_object* v_as_933_, size_t v_i_934_, size_t v_stop_935_){
_start:
{
uint8_t v___x_936_; 
v___x_936_ = lean_usize_dec_eq(v_i_934_, v_stop_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; uint8_t v___x_938_; 
v___x_937_ = lean_array_uget_borrowed(v_as_933_, v_i_934_);
v___x_938_ = lean_string_dec_eq(v___x_937_, v_token_932_);
if (v___x_938_ == 0)
{
size_t v___x_939_; size_t v___x_940_; 
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_add(v_i_934_, v___x_939_);
v_i_934_ = v___x_940_;
goto _start;
}
else
{
return v___x_938_;
}
}
else
{
uint8_t v___x_942_; 
v___x_942_ = 0;
return v___x_942_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_token_932_ = stack[0].m_obj;
lean_object* v_as_933_ = stack[1].m_obj;
size_t v_i_934_ = stack[2].m_num;
size_t v_stop_935_ = stack[3].m_num;
uint8_t v_res_943_;
v_res_943_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_932_, v_as_933_, v_i_934_, v_stop_935_);
stack->m_num = v_res_943_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(lean_object* v_token_944_, lean_object* v_as_945_, lean_object* v_i_946_, lean_object* v_stop_947_){
_start:
{
size_t v_i_boxed_948_; size_t v_stop_boxed_949_; uint8_t v_res_950_; lean_object* v_r_951_; 
v_i_boxed_948_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_stop_boxed_949_ = lean_unbox_usize(v_stop_947_);
lean_dec(v_stop_947_);
v_res_950_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_944_, v_as_945_, v_i_boxed_948_, v_stop_boxed_949_);
lean_dec_ref(v_as_945_);
lean_dec_ref(v_token_944_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
uint8_t l_Std_Http_Header_Connection_containsToken(lean_object* v_connection_952_, lean_object* v_token_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_array_get_size(v_connection_952_);
v___x_956_ = lean_nat_dec_lt(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_dec_ref(v_token_953_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; 
v___x_957_ = lean_string_utf8_byte_size(v_token_953_);
if (v___x_956_ == 0)
{
lean_dec_ref(v_token_953_);
return v___x_956_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v_token_961_; size_t v___x_962_; size_t v___x_963_; uint8_t v___x_964_; 
v___x_958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_958_, 0, v_token_953_);
lean_ctor_set(v___x_958_, 1, v___x_954_);
lean_ctor_set(v___x_958_, 2, v___x_957_);
v___x_959_ = l_String_Slice_trimAscii(v___x_958_);
v___x_960_ = l_String_Slice_toString(v___x_959_);
lean_dec_ref(v___x_959_);
v_token_961_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_960_, v___x_954_);
v___x_962_ = ((size_t)0ULL);
v___x_963_ = lean_usize_of_nat(v___x_955_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_961_, v_connection_952_, v___x_962_, v___x_963_);
lean_dec_ref(v_token_961_);
return v___x_964_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Header_Connection_containsToken_0interp(lean_interpreter_value* stack)
{
lean_object* v_connection_952_ = stack[0].m_obj;
lean_object* v_token_953_ = stack[1].m_obj;
uint8_t v_res_965_;
v_res_965_ = l_Std_Http_Header_Connection_containsToken(v_connection_952_, v_token_953_);
stack->m_num = v_res_965_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_containsToken___boxed(lean_object* v_connection_966_, lean_object* v_token_967_){
_start:
{
uint8_t v_res_968_; lean_object* v_r_969_; 
v_res_968_ = l_Std_Http_Header_Connection_containsToken(v_connection_966_, v_token_967_);
lean_dec_ref(v_connection_966_);
v_r_969_ = lean_box(v_res_968_);
return v_r_969_;
}
}
uint8_t l_Std_Http_Header_Connection_shouldClose(lean_object* v_connection_971_){
_start:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = ((lean_object*)(l_Std_Http_Header_Connection_shouldClose___closed__0));
v___x_973_ = l_Std_Http_Header_Connection_containsToken(v_connection_971_, v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT void l_Std_Http_Header_Connection_shouldClose_0interp(lean_interpreter_value* stack)
{
lean_object* v_connection_971_ = stack[0].m_obj;
uint8_t v_res_974_;
v_res_974_ = l_Std_Http_Header_Connection_shouldClose(v_connection_971_);
stack->m_num = v_res_974_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_shouldClose___boxed(lean_object* v_connection_975_){
_start:
{
uint8_t v_res_976_; lean_object* v_r_977_; 
v_res_976_ = l_Std_Http_Header_Connection_shouldClose(v_connection_975_);
lean_dec_ref(v_connection_975_);
v_r_977_ = lean_box(v_res_976_);
return v_r_977_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(lean_object* v_as_978_, size_t v_i_979_, size_t v_stop_980_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_eq(v_i_979_, v_stop_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; uint8_t v___x_983_; 
v___x_982_ = lean_array_uget_borrowed(v_as_978_, v_i_979_);
lean_inc(v___x_982_);
v___x_983_ = l_Std_Http_Internal_isToken(v___x_982_);
if (v___x_983_ == 0)
{
uint8_t v___x_984_; 
v___x_984_ = 1;
return v___x_984_;
}
else
{
size_t v___x_985_; size_t v___x_986_; 
v___x_985_ = ((size_t)1ULL);
v___x_986_ = lean_usize_add(v_i_979_, v___x_985_);
v_i_979_ = v___x_986_;
goto _start;
}
}
else
{
uint8_t v___x_988_; 
v___x_988_ = 0;
return v___x_988_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_978_ = stack[0].m_obj;
size_t v_i_979_ = stack[1].m_num;
size_t v_stop_980_ = stack[2].m_num;
uint8_t v_res_989_;
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_978_, v_i_979_, v_stop_980_);
stack->m_num = v_res_989_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(lean_object* v_as_990_, lean_object* v_i_991_, lean_object* v_stop_992_){
_start:
{
size_t v_i_boxed_993_; size_t v_stop_boxed_994_; uint8_t v_res_995_; lean_object* v_r_996_; 
v_i_boxed_993_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_stop_boxed_994_ = lean_unbox_usize(v_stop_992_);
lean_dec(v_stop_992_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_990_, v_i_boxed_993_, v_stop_boxed_994_);
lean_dec_ref(v_as_990_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_parse(lean_object* v_v_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_997_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v___x_999_; 
v___x_999_ = lean_box(0);
return v___x_999_;
}
else
{
lean_object* v_val_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1020_; 
v_val_1000_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1002_ = v___x_998_;
v_isShared_1003_ = v_isSharedCheck_1020_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_val_1000_);
lean_dec(v___x_998_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1020_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_array_get_size(v_val_1000_);
v___x_1006_ = lean_nat_dec_lt(v___x_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1008_; 
if (v_isShared_1003_ == 0)
{
v___x_1008_ = v___x_1002_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_val_1000_);
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
if (v___x_1006_ == 0)
{
lean_object* v___x_1011_; 
if (v_isShared_1003_ == 0)
{
v___x_1011_ = v___x_1002_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_val_1000_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
size_t v___x_1013_; size_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1013_ = ((size_t)0ULL);
v___x_1014_ = lean_usize_of_nat(v___x_1005_);
v___x_1015_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_val_1000_, v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1017_; 
if (v_isShared_1003_ == 0)
{
v___x_1017_ = v___x_1002_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_val_1000_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
else
{
lean_object* v___x_1019_; 
lean_del_object(v___x_1002_);
lean_dec(v_val_1000_);
v___x_1019_ = lean_box(0);
return v___x_1019_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_serialize(lean_object* v_connection_1021_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_value_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1022_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_1023_ = lean_array_to_list(v_connection_1021_);
v_value_1024_ = l_String_intercalate(v___x_1022_, v___x_1023_);
v___x_1025_ = l_Std_Http_Header_Name_connection;
v___x_1026_ = l_Std_Http_Header_Value_ofString_x21(v_value_1024_);
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_unsigned_to_nat(8u);
v___x_1044_ = lean_nat_to_int(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_unsigned_to_nat(2u);
v___x_1046_ = lean_nat_to_int(v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___redArg(lean_object* v_x_1054_){
_start:
{
lean_object* v_host_1055_; lean_object* v_port_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1130_; 
v_host_1055_ = lean_ctor_get(v_x_1054_, 0);
v_port_1056_ = lean_ctor_get(v_x_1054_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_x_1054_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1058_ = v_x_1054_;
v_isShared_1059_ = v_isSharedCheck_1130_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_port_1056_);
lean_inc(v_host_1055_);
lean_dec(v_x_1054_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1130_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_ctr_1066_; lean_object* v_a_1067_; 
v___x_1060_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_1061_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__3));
v___x_1062_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__4, &l_Std_Http_Header_instReprHost_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4);
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__5, &l_Std_Http_Header_instReprHost_repr___redArg___closed__5_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5);
switch(lean_obj_tag(v_host_1055_))
{
case 0:
{
lean_object* v_name_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1109_; 
v_name_1100_ = lean_ctor_get(v_host_1055_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_host_1055_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1102_ = v_host_1055_;
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_name_1100_);
lean_dec(v_host_1055_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1104_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__9));
v___x_1105_ = l_String_quote(v_name_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set_tag(v___x_1102_, 3);
lean_ctor_set(v___x_1102_, 0, v___x_1105_);
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1105_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
v_ctr_1066_ = v___x_1104_;
v_a_1067_ = v___x_1107_;
goto v___jp_1065_;
}
}
}
case 1:
{
lean_object* v_ipv4_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1119_; 
v_ipv4_1110_ = lean_ctor_get(v_host_1055_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_host_1055_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1112_ = v_host_1055_;
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_ipv4_1110_);
lean_dec(v_host_1055_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1119_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v___x_1114_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__10));
v___x_1115_ = lean_uv_ntop_v4(v_ipv4_1110_);
lean_dec_ref(v_ipv4_1110_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 3);
lean_ctor_set(v___x_1112_, 0, v___x_1115_);
v___x_1117_ = v___x_1112_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
v_ctr_1066_ = v___x_1114_;
v_a_1067_ = v___x_1117_;
goto v___jp_1065_;
}
}
}
default: 
{
lean_object* v_ipv6_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1129_; 
v_ipv6_1120_ = lean_ctor_get(v_host_1055_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v_host_1055_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1122_ = v_host_1055_;
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_ipv6_1120_);
lean_dec(v_host_1055_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1129_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1124_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__11));
v___x_1125_ = lean_uv_ntop_v6(v_ipv6_1120_);
lean_dec_ref(v_ipv6_1120_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set_tag(v___x_1122_, 3);
lean_ctor_set(v___x_1122_, 0, v___x_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
v_ctr_1066_ = v___x_1124_;
v_a_1067_ = v___x_1127_;
goto v___jp_1065_;
}
}
}
}
v___jp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1068_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__6));
v___x_1069_ = lean_string_append(v___x_1068_, v_ctr_1066_);
v___x_1070_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
v___x_1071_ = lean_box(1);
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 5);
lean_ctor_set(v___x_1058_, 1, v___x_1071_);
lean_ctor_set(v___x_1058_, 0, v___x_1070_);
v___x_1073_ = v___x_1058_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1074_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_a_1067_);
v___x_1075_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1064_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = 0;
v___x_1077_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set_uint8(v___x_1077_, sizeof(void*)*1, v___x_1076_);
v___x_1078_ = l_Repr_addAppParen(v___x_1077_, v___x_1063_);
v___x_1079_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1062_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*1, v___x_1076_);
v___x_1081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1061_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_1083_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v___x_1071_);
v___x_1085_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__8));
v___x_1086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v___x_1060_);
v___x_1088_ = l_Std_Http_URI_instReprPort_repr(v_port_1056_, v___x_1063_);
lean_dec(v_port_1056_);
v___x_1089_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1062_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*1, v___x_1076_);
v___x_1091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1087_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1093_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_1094_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v___x_1091_);
v___x_1095_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_1096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1092_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set_uint8(v___x_1098_, sizeof(void*)*1, v___x_1076_);
return v___x_1098_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr(lean_object* v_x_1131_, lean_object* v_prec_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Std_Http_Header_instReprHost_repr___redArg(v_x_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___boxed(lean_object* v_x_1134_, lean_object* v_prec_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Std_Http_Header_instReprHost_repr(v_x_1134_, v_prec_1135_);
lean_dec(v_prec_1135_);
return v_res_1136_;
}
}
uint8_t l_Std_Http_Header_instBEqHost_beq(lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
lean_object* v_host_1141_; lean_object* v_port_1142_; lean_object* v_host_1143_; lean_object* v_port_1144_; uint8_t v___x_1145_; 
v_host_1141_ = lean_ctor_get(v_x_1139_, 0);
v_port_1142_ = lean_ctor_get(v_x_1139_, 1);
v_host_1143_ = lean_ctor_get(v_x_1140_, 0);
v_port_1144_ = lean_ctor_get(v_x_1140_, 1);
v___x_1145_ = l_Std_Http_URI_instBEqHost_beq(v_host_1141_, v_host_1143_);
if (v___x_1145_ == 0)
{
return v___x_1145_;
}
else
{
uint8_t v___x_1146_; 
v___x_1146_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1142_, v_port_1144_);
return v___x_1146_;
}
}
}
LEAN_EXPORT void l_Std_Http_Header_instBEqHost_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1139_ = stack[0].m_obj;
lean_object* v_x_1140_ = stack[1].m_obj;
uint8_t v_res_1147_;
v_res_1147_ = l_Std_Http_Header_instBEqHost_beq(v_x_1139_, v_x_1140_);
stack->m_num = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqHost_beq___boxed(lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
uint8_t v_res_1150_; lean_object* v_r_1151_; 
v_res_1150_ = l_Std_Http_Header_instBEqHost_beq(v_x_1148_, v_x_1149_);
lean_dec_ref(v_x_1149_);
lean_dec_ref(v_x_1148_);
v_r_1151_ = lean_box(v_res_1150_);
return v_r_1151_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0(lean_object* v___x_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Std_Http_URI_Parser_parseHostHeader(v___x_1157_, v___y_1158_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_pos_1160_; lean_object* v_array_1161_; lean_object* v_idx_1162_; lean_object* v___x_1163_; uint8_t v___x_1164_; 
v_pos_1160_ = lean_ctor_get(v___x_1159_, 0);
v_array_1161_ = lean_ctor_get(v_pos_1160_, 0);
v_idx_1162_ = lean_ctor_get(v_pos_1160_, 1);
v___x_1163_ = lean_byte_array_size(v_array_1161_);
v___x_1164_ = lean_nat_dec_lt(v_idx_1162_, v___x_1163_);
if (v___x_1164_ == 0)
{
return v___x_1159_;
}
else
{
lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1172_; 
lean_inc(v_pos_1160_);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; 
v_unused_1173_ = lean_ctor_get(v___x_1159_, 1);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v___x_1159_, 0);
lean_dec(v_unused_1174_);
v___x_1166_ = v___x_1159_;
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
else
{
lean_dec(v___x_1159_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1172_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
v___x_1168_ = ((lean_object*)(l_Std_Http_Header_Host_parse___lam__0___closed__1));
if (v_isShared_1167_ == 0)
{
lean_ctor_set_tag(v___x_1166_, 1);
lean_ctor_set(v___x_1166_, 1, v___x_1168_);
v___x_1170_ = v___x_1166_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_pos_1160_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0___boxed(lean_object* v___x_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Std_Http_Header_Host_parse___lam__0(v___x_1175_, v___y_1176_);
lean_dec_ref(v___x_1175_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse(lean_object* v_v_1188_){
_start:
{
lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v_parsed_1191_; 
v___f_1189_ = ((lean_object*)(l_Std_Http_Header_Host_parse___closed__1));
v___x_1190_ = lean_string_to_utf8(v_v_1188_);
v_parsed_1191_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1189_, v___x_1190_);
if (lean_obj_tag(v_parsed_1191_) == 0)
{
lean_object* v___x_1192_; 
lean_dec_ref_known(v_parsed_1191_, 1);
v___x_1192_ = lean_box(0);
return v___x_1192_;
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1209_; 
v_a_1193_ = lean_ctor_get(v_parsed_1191_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_parsed_1191_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1195_ = v_parsed_1191_;
v_isShared_1196_ = v_isSharedCheck_1209_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v_parsed_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1209_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_fst_1197_; lean_object* v_snd_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1208_; 
v_fst_1197_ = lean_ctor_get(v_a_1193_, 0);
v_snd_1198_ = lean_ctor_get(v_a_1193_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_a_1193_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1200_ = v_a_1193_;
v_isShared_1201_ = v_isSharedCheck_1208_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_snd_1198_);
lean_inc(v_fst_1197_);
lean_dec(v_a_1193_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1208_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_fst_1197_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_snd_1198_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1205_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1203_);
v___x_1205_ = v___x_1195_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___boxed(lean_object* v_v_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_Http_Header_Host_parse(v_v_1210_);
lean_dec_ref(v_v_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_serialize(lean_object* v_host_1214_){
_start:
{
lean_object* v___y_1216_; lean_object* v___y_1220_; lean_object* v_port_1224_; 
v_port_1224_ = lean_ctor_get(v_host_1214_, 1);
switch(lean_obj_tag(v_port_1224_))
{
case 0:
{
lean_object* v_host_1225_; 
v_host_1225_ = lean_ctor_get(v_host_1214_, 0);
lean_inc_ref(v_host_1225_);
lean_dec_ref(v_host_1214_);
switch(lean_obj_tag(v_host_1225_))
{
case 0:
{
lean_object* v_name_1226_; lean_object* v___x_1227_; 
v_name_1226_ = lean_ctor_get(v_host_1225_, 0);
lean_inc_ref(v_name_1226_);
lean_dec_ref_known(v_host_1225_, 1);
v___x_1227_ = l_Std_Http_Header_Value_ofString_x21(v_name_1226_);
v___y_1216_ = v___x_1227_;
goto v___jp_1215_;
}
case 1:
{
lean_object* v_ipv4_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v_ipv4_1228_ = lean_ctor_get(v_host_1225_, 0);
lean_inc_ref(v_ipv4_1228_);
lean_dec_ref_known(v_host_1225_, 1);
v___x_1229_ = lean_uv_ntop_v4(v_ipv4_1228_);
lean_dec_ref(v_ipv4_1228_);
v___x_1230_ = l_Std_Http_Header_Value_ofString_x21(v___x_1229_);
v___y_1216_ = v___x_1230_;
goto v___jp_1215_;
}
default: 
{
lean_object* v_ipv6_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v_ipv6_1231_ = lean_ctor_get(v_host_1225_, 0);
lean_inc_ref(v_ipv6_1231_);
lean_dec_ref_known(v_host_1225_, 1);
v___x_1232_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1233_ = lean_uv_ntop_v6(v_ipv6_1231_);
lean_dec_ref(v_ipv6_1231_);
v___x_1234_ = lean_string_append(v___x_1232_, v___x_1233_);
lean_dec_ref(v___x_1233_);
v___x_1235_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1236_ = lean_string_append(v___x_1234_, v___x_1235_);
v___x_1237_ = l_Std_Http_Header_Value_ofString_x21(v___x_1236_);
v___y_1216_ = v___x_1237_;
goto v___jp_1215_;
}
}
}
case 1:
{
lean_object* v_host_1238_; 
v_host_1238_ = lean_ctor_get(v_host_1214_, 0);
lean_inc_ref(v_host_1238_);
lean_dec_ref(v_host_1214_);
switch(lean_obj_tag(v_host_1238_))
{
case 0:
{
lean_object* v_name_1239_; 
v_name_1239_ = lean_ctor_get(v_host_1238_, 0);
lean_inc_ref(v_name_1239_);
lean_dec_ref_known(v_host_1238_, 1);
v___y_1220_ = v_name_1239_;
goto v___jp_1219_;
}
case 1:
{
lean_object* v_ipv4_1240_; lean_object* v___x_1241_; 
v_ipv4_1240_ = lean_ctor_get(v_host_1238_, 0);
lean_inc_ref(v_ipv4_1240_);
lean_dec_ref_known(v_host_1238_, 1);
v___x_1241_ = lean_uv_ntop_v4(v_ipv4_1240_);
lean_dec_ref(v_ipv4_1240_);
v___y_1220_ = v___x_1241_;
goto v___jp_1219_;
}
default: 
{
lean_object* v_ipv6_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_ipv6_1242_ = lean_ctor_get(v_host_1238_, 0);
lean_inc_ref(v_ipv6_1242_);
lean_dec_ref_known(v_host_1238_, 1);
v___x_1243_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1244_ = lean_uv_ntop_v6(v_ipv6_1242_);
lean_dec_ref(v_ipv6_1242_);
v___x_1245_ = lean_string_append(v___x_1243_, v___x_1244_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1247_ = lean_string_append(v___x_1245_, v___x_1246_);
v___y_1220_ = v___x_1247_;
goto v___jp_1219_;
}
}
}
default: 
{
lean_object* v_host_1248_; uint16_t v_port_1249_; lean_object* v___y_1251_; 
lean_inc_ref(v_port_1224_);
v_host_1248_ = lean_ctor_get(v_host_1214_, 0);
lean_inc_ref(v_host_1248_);
lean_dec_ref(v_host_1214_);
v_port_1249_ = lean_ctor_get_uint16(v_port_1224_, 0);
lean_dec_ref_known(v_port_1224_, 0);
switch(lean_obj_tag(v_host_1248_))
{
case 0:
{
lean_object* v_name_1258_; 
v_name_1258_ = lean_ctor_get(v_host_1248_, 0);
lean_inc_ref(v_name_1258_);
lean_dec_ref_known(v_host_1248_, 1);
v___y_1251_ = v_name_1258_;
goto v___jp_1250_;
}
case 1:
{
lean_object* v_ipv4_1259_; lean_object* v___x_1260_; 
v_ipv4_1259_ = lean_ctor_get(v_host_1248_, 0);
lean_inc_ref(v_ipv4_1259_);
lean_dec_ref_known(v_host_1248_, 1);
v___x_1260_ = lean_uv_ntop_v4(v_ipv4_1259_);
lean_dec_ref(v_ipv4_1259_);
v___y_1251_ = v___x_1260_;
goto v___jp_1250_;
}
default: 
{
lean_object* v_ipv6_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v_ipv6_1261_ = lean_ctor_get(v_host_1248_, 0);
lean_inc_ref(v_ipv6_1261_);
lean_dec_ref_known(v_host_1248_, 1);
v___x_1262_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1263_ = lean_uv_ntop_v6(v_ipv6_1261_);
lean_dec_ref(v_ipv6_1261_);
v___x_1264_ = lean_string_append(v___x_1262_, v___x_1263_);
lean_dec_ref(v___x_1263_);
v___x_1265_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1266_ = lean_string_append(v___x_1264_, v___x_1265_);
v___y_1251_ = v___x_1266_;
goto v___jp_1250_;
}
}
v___jp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1252_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1253_ = lean_string_append(v___y_1251_, v___x_1252_);
v___x_1254_ = lean_uint16_to_nat(v_port_1249_);
v___x_1255_ = l_Nat_reprFast(v___x_1254_);
v___x_1256_ = lean_string_append(v___x_1253_, v___x_1255_);
lean_dec_ref(v___x_1255_);
v___x_1257_ = l_Std_Http_Header_Value_ofString_x21(v___x_1256_);
v___y_1216_ = v___x_1257_;
goto v___jp_1215_;
}
}
}
v___jp_1215_:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__0));
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
lean_ctor_set(v___x_1218_, 1, v___y_1216_);
return v___x_1218_;
}
v___jp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v___x_1221_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1222_ = lean_string_append(v___y_1220_, v___x_1221_);
v___x_1223_ = l_Std_Http_Header_Value_ofString_x21(v___x_1222_);
v___y_1216_ = v___x_1223_;
goto v___jp_1215_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = ((lean_object*)(l_Std_Http_Header_instReprExpect_repr___redArg___closed__1));
v___x_1280_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1281_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v___x_1279_);
return v___x_1281_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3(void){
_start:
{
uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = 0;
v___x_1283_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__2, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__2_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2);
v___x_1284_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*1, v___x_1282_);
return v___x_1284_;
}
}
lean_object* l_Std_Http_Header_instReprExpect_repr___redArg(){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__3, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__3_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3);
return v___x_1286_;
}
}
LEAN_EXPORT void l_Std_Http_Header_instReprExpect_repr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1287_;
v_res_1287_ = l_Std_Http_Header_instReprExpect_repr___redArg();
stack->m_obj
 = v_res_1287_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___boxed(lean_object* v___dummy_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v_res_1289_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___closed__0(void){
_start:
{
lean_object* v___x_1290_; 
v___x_1290_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr(lean_object* v_x_1291_, lean_object* v_prec_1292_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___closed__0, &l_Std_Http_Header_instReprExpect_repr___closed__0_once, _init_l_Std_Http_Header_instReprExpect_repr___closed__0);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___boxed(lean_object* v_x_1294_, lean_object* v_prec_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_Http_Header_instReprExpect_repr(v_x_1294_, v_prec_1295_);
lean_dec(v_prec_1295_);
return v_res_1296_;
}
}
uint8_t l_Std_Http_Header_instBEqExpect_beq___redArg(){
_start:
{
uint8_t v___x_1300_; 
v___x_1300_ = 1;
return v___x_1300_;
}
}
LEAN_EXPORT void l_Std_Http_Header_instBEqExpect_beq___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_res_1301_;
v_res_1301_ = l_Std_Http_Header_instBEqExpect_beq___redArg();
stack->m_num = v_res_1301_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___redArg___boxed(lean_object* v___dummy_1302_){
_start:
{
uint8_t v_res_1303_; lean_object* v_r_1304_; 
v_res_1303_ = l_Std_Http_Header_instBEqExpect_beq___redArg();
v_r_1304_ = lean_box(v_res_1303_);
return v_r_1304_;
}
}
uint8_t l_Std_Http_Header_instBEqExpect_beq(lean_object* v_x_1305_, lean_object* v_y_1306_){
_start:
{
uint8_t v___x_1307_; 
v___x_1307_ = 1;
return v___x_1307_;
}
}
LEAN_EXPORT void l_Std_Http_Header_instBEqExpect_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1305_ = stack[0].m_obj;
lean_object* v_y_1306_ = stack[1].m_obj;
uint8_t v_res_1308_;
v_res_1308_ = l_Std_Http_Header_instBEqExpect_beq(v_x_1305_, v_y_1306_);
stack->m_num = v_res_1308_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___boxed(lean_object* v_x_1309_, lean_object* v_y_1310_){
_start:
{
uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_res_1311_ = l_Std_Http_Header_instBEqExpect_beq(v_x_1309_, v_y_1310_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_parse(lean_object* v_v_1318_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_normalized_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = lean_string_utf8_byte_size(v_v_1318_);
v___x_1321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1321_, 0, v_v_1318_);
lean_ctor_set(v___x_1321_, 1, v___x_1319_);
lean_ctor_set(v___x_1321_, 2, v___x_1320_);
v___x_1322_ = l_String_Slice_trimAscii(v___x_1321_);
v___x_1323_ = l_String_Slice_toString(v___x_1322_);
lean_dec_ref(v___x_1322_);
v_normalized_1324_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_1323_, v___x_1319_);
v___x_1325_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1326_ = lean_string_dec_eq(v_normalized_1324_, v___x_1325_);
lean_dec_ref(v_normalized_1324_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
v___x_1327_ = lean_box(0);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; 
v___x_1328_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__1));
return v___x_1328_;
}
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1330_ = l_Std_Http_Header_Value_ofString_x21(v___x_1329_);
return v___x_1330_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1(void){
_start:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1331_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__0, &l_Std_Http_Header_Expect_serialize___redArg___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0);
v___x_1332_ = l_Std_Http_Header_Name_expect;
v___x_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v___x_1331_);
return v___x_1333_;
}
}
lean_object* l_Std_Http_Header_Expect_serialize___redArg(){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__1, &l_Std_Http_Header_Expect_serialize___redArg___closed__1_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1);
return v___x_1335_;
}
}
LEAN_EXPORT void l_Std_Http_Header_Expect_serialize___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1336_;
v_res_1336_ = l_Std_Http_Header_Expect_serialize___redArg();
stack->m_obj
 = v_res_1336_;
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg___boxed(lean_object* v___dummy_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_Http_Header_Expect_serialize___redArg();
return v_res_1338_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___closed__0(void){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Std_Http_Header_Expect_serialize___redArg();
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize(lean_object* v_x_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___closed__0, &l_Std_Http_Header_Expect_serialize___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___closed__0);
return v___x_1341_;
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

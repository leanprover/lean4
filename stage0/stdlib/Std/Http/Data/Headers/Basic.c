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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
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
static const lean_string_object l_Std_Http_Header_Host_serialize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Std_Http_Header_Host_serialize___closed__0 = (const lean_object*)&l_Std_Http_Header_Host_serialize___closed__0_value;
static const lean_string_object l_Std_Http_Header_Host_serialize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Std_Http_Header_Host_serialize___closed__1 = (const lean_object*)&l_Std_Http_Header_Host_serialize___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_serialize(lean_object*);
static const lean_closure_object l_Std_Http_Header_Host_inst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Host_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* v___y_147_; lean_object* v___y_148_; uint32_t v___y_152_; lean_object* v___x_164_; uint8_t v_decide_165_; 
v___x_164_ = lean_string_utf8_byte_size(v_s_144_);
v_decide_165_ = lean_nat_dec_eq(v_p_145_, v___x_164_);
if (v_decide_165_ == 0)
{
uint32_t v___x_166_; uint32_t v___x_167_; uint8_t v___x_168_; 
v___x_166_ = lean_string_utf8_get_fast(v_s_144_, v_p_145_);
v___x_167_ = 65;
v___x_168_ = lean_uint32_dec_le(v___x_167_, v___x_166_);
if (v___x_168_ == 0)
{
v___y_152_ = v___x_166_;
goto v___jp_151_;
}
else
{
uint32_t v___x_169_; uint8_t v___x_170_; 
v___x_169_ = 90;
v___x_170_ = lean_uint32_dec_le(v___x_166_, v___x_169_);
if (v___x_170_ == 0)
{
v___y_152_ = v___x_166_;
goto v___jp_151_;
}
else
{
uint32_t v___x_171_; uint32_t v___x_172_; 
v___x_171_ = 32;
v___x_172_ = lean_uint32_add(v___x_166_, v___x_171_);
v___y_152_ = v___x_172_;
goto v___jp_151_;
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
lean_object* v___x_149_; 
v___x_149_ = lean_nat_add(v_p_145_, v___y_148_);
lean_dec(v_p_145_);
v_s_144_ = v___y_147_;
v_p_145_ = v___x_149_;
goto _start;
}
v___jp_151_:
{
lean_object* v___x_153_; uint32_t v___x_154_; uint8_t v___x_155_; 
lean_inc(v_p_145_);
v___x_153_ = lean_string_utf8_set(v_s_144_, v_p_145_, v___y_152_);
v___x_154_ = 127;
v___x_155_ = lean_uint32_dec_le(v___y_152_, v___x_154_);
if (v___x_155_ == 0)
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 2047;
v___x_157_ = lean_uint32_dec_le(v___y_152_, v___x_156_);
if (v___x_157_ == 0)
{
uint32_t v___x_158_; uint8_t v___x_159_; 
v___x_158_ = 65535;
v___x_159_ = lean_uint32_dec_le(v___y_152_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_unsigned_to_nat(4u);
v___y_147_ = v___x_153_;
v___y_148_ = v___x_160_;
goto v___jp_146_;
}
else
{
lean_object* v___x_161_; 
v___x_161_ = lean_unsigned_to_nat(3u);
v___y_147_ = v___x_153_;
v___y_148_ = v___x_161_;
goto v___jp_146_;
}
}
else
{
lean_object* v___x_162_; 
v___x_162_ = lean_unsigned_to_nat(2u);
v___y_147_ = v___x_153_;
v___y_148_ = v___x_162_;
goto v___jp_146_;
}
}
else
{
lean_object* v___x_163_; 
v___x_163_ = lean_unsigned_to_nat(1u);
v___y_147_ = v___x_153_;
v___y_148_ = v___x_163_;
goto v___jp_146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t v_sz_173_, size_t v_i_174_, lean_object* v_bs_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = lean_usize_dec_lt(v_i_174_, v_sz_173_);
if (v___x_176_ == 0)
{
return v_bs_175_;
}
else
{
lean_object* v_v_177_; lean_object* v___x_178_; lean_object* v_bs_x27_179_; lean_object* v___x_180_; lean_object* v___x_181_; size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v_v_177_ = lean_array_uget(v_bs_175_, v_i_174_);
v___x_178_ = lean_unsigned_to_nat(0u);
v_bs_x27_179_ = lean_array_uset(v_bs_175_, v_i_174_, v___x_178_);
v___x_180_ = l_String_Slice_toString(v_v_177_);
lean_dec(v_v_177_);
v___x_181_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_180_, v___x_178_);
v___x_182_ = ((size_t)1ULL);
v___x_183_ = lean_usize_add(v_i_174_, v___x_182_);
v___x_184_ = lean_array_uset(v_bs_x27_179_, v_i_174_, v___x_181_);
v_i_174_ = v___x_183_;
v_bs_175_ = v___x_184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(lean_object* v_sz_186_, lean_object* v_i_187_, lean_object* v_bs_188_){
_start:
{
size_t v_sz_boxed_189_; size_t v_i_boxed_190_; lean_object* v_res_191_; 
v_sz_boxed_189_ = lean_unbox_usize(v_sz_186_);
lean_dec(v_sz_186_);
v_i_boxed_190_ = lean_unbox_usize(v_i_187_);
lean_dec(v_i_187_);
v_res_191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_boxed_189_, v_i_boxed_190_, v_bs_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(lean_object* v___x_192_, lean_object* v___x_193_, lean_object* v___x_194_, lean_object* v_a_195_, lean_object* v_b_196_){
_start:
{
lean_object* v_it_198_; lean_object* v_startInclusive_199_; lean_object* v_endExclusive_200_; 
if (lean_obj_tag(v_a_195_) == 0)
{
lean_object* v_currPos_205_; lean_object* v_searcher_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_235_; 
v_currPos_205_ = lean_ctor_get(v_a_195_, 0);
v_searcher_206_ = lean_ctor_get(v_a_195_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v_a_195_);
if (v_isSharedCheck_235_ == 0)
{
v___x_208_ = v_a_195_;
v_isShared_209_ = v_isSharedCheck_235_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_searcher_206_);
lean_inc(v_currPos_205_);
lean_dec(v_a_195_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_235_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_str_210_; lean_object* v_startInclusive_211_; lean_object* v_endExclusive_212_; lean_object* v___x_213_; uint8_t v_decide_214_; 
v_str_210_ = lean_ctor_get(v___x_193_, 0);
v_startInclusive_211_ = lean_ctor_get(v___x_193_, 1);
v_endExclusive_212_ = lean_ctor_get(v___x_193_, 2);
v___x_213_ = lean_nat_sub(v_endExclusive_212_, v_startInclusive_211_);
v_decide_214_ = lean_nat_dec_eq(v_searcher_206_, v___x_213_);
lean_dec(v___x_213_);
if (v_decide_214_ == 0)
{
lean_object* v___x_215_; uint32_t v___x_216_; uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_215_ = lean_nat_add(v_startInclusive_211_, v_searcher_206_);
v___x_216_ = lean_string_utf8_get_fast(v_str_210_, v___x_215_);
v___x_217_ = 44;
v___x_218_ = lean_uint32_dec_eq(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
lean_dec(v_searcher_206_);
v___x_219_ = lean_string_utf8_next_fast(v_str_210_, v___x_215_);
lean_dec(v___x_215_);
v___x_220_ = lean_nat_sub(v___x_219_, v_startInclusive_211_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_220_);
v___x_222_ = v___x_208_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_currPos_205_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v___x_220_);
v___x_222_ = v_reuseFailAlloc_224_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
v_a_195_ = v___x_222_;
goto _start;
}
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v_slice_228_; lean_object* v_nextIt_230_; 
v___x_225_ = lean_string_utf8_next_fast(v_str_210_, v___x_215_);
v___x_226_ = lean_nat_sub(v___x_225_, v___x_215_);
lean_dec(v___x_215_);
v___x_227_ = lean_nat_add(v_searcher_206_, v___x_226_);
lean_dec(v___x_226_);
v_slice_228_ = l_String_Slice_subslice_x21(v___x_193_, v_currPos_205_, v_searcher_206_);
lean_inc(v___x_227_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_227_);
lean_ctor_set(v___x_208_, 0, v___x_227_);
v_nextIt_230_ = v___x_208_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v___x_227_);
v_nextIt_230_ = v_reuseFailAlloc_233_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v_startInclusive_231_; lean_object* v_endExclusive_232_; 
v_startInclusive_231_ = lean_ctor_get(v_slice_228_, 0);
lean_inc(v_startInclusive_231_);
v_endExclusive_232_ = lean_ctor_get(v_slice_228_, 1);
lean_inc(v_endExclusive_232_);
lean_dec_ref(v_slice_228_);
v_it_198_ = v_nextIt_230_;
v_startInclusive_199_ = v_startInclusive_231_;
v_endExclusive_200_ = v_endExclusive_232_;
goto v___jp_197_;
}
}
}
else
{
lean_object* v___x_234_; 
lean_del_object(v___x_208_);
lean_dec(v_searcher_206_);
v___x_234_ = lean_box(1);
lean_inc(v___x_194_);
v_it_198_ = v___x_234_;
v_startInclusive_199_ = v_currPos_205_;
v_endExclusive_200_ = v___x_194_;
goto v___jp_197_;
}
}
}
else
{
lean_dec(v___x_194_);
lean_dec_ref(v___x_192_);
return v_b_196_;
}
v___jp_197_:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
lean_inc_ref(v___x_192_);
v___x_201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_201_, 0, v___x_192_);
lean_ctor_set(v___x_201_, 1, v_startInclusive_199_);
lean_ctor_set(v___x_201_, 2, v_endExclusive_200_);
v___x_202_ = l_String_Slice_trimAscii(v___x_201_);
v___x_203_ = lean_array_push(v_b_196_, v___x_202_);
v_a_195_ = v_it_198_;
v_b_196_ = v___x_203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(lean_object* v___x_236_, lean_object* v___x_237_, lean_object* v___x_238_, lean_object* v_a_239_, lean_object* v_b_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_236_, v___x_237_, v___x_238_, v_a_239_, v_b_240_);
lean_dec_ref(v___x_237_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(lean_object* v___x_242_, lean_object* v___x_243_, lean_object* v___x_244_, lean_object* v_a_245_, lean_object* v_b_246_){
_start:
{
lean_object* v_it_248_; lean_object* v_startInclusive_249_; lean_object* v_endExclusive_250_; 
if (lean_obj_tag(v_a_245_) == 0)
{
lean_object* v_currPos_255_; lean_object* v_searcher_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_285_; 
v_currPos_255_ = lean_ctor_get(v_a_245_, 0);
v_searcher_256_ = lean_ctor_get(v_a_245_, 1);
v_isSharedCheck_285_ = !lean_is_exclusive(v_a_245_);
if (v_isSharedCheck_285_ == 0)
{
v___x_258_ = v_a_245_;
v_isShared_259_ = v_isSharedCheck_285_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_searcher_256_);
lean_inc(v_currPos_255_);
lean_dec(v_a_245_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_285_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_str_260_; lean_object* v_startInclusive_261_; lean_object* v_endExclusive_262_; lean_object* v___x_263_; uint8_t v_decide_264_; 
v_str_260_ = lean_ctor_get(v___x_243_, 0);
v_startInclusive_261_ = lean_ctor_get(v___x_243_, 1);
v_endExclusive_262_ = lean_ctor_get(v___x_243_, 2);
v___x_263_ = lean_nat_sub(v_endExclusive_262_, v_startInclusive_261_);
v_decide_264_ = lean_nat_dec_eq(v_searcher_256_, v___x_263_);
lean_dec(v___x_263_);
if (v_decide_264_ == 0)
{
lean_object* v___x_265_; uint32_t v___x_266_; uint32_t v___x_267_; uint8_t v___x_268_; 
v___x_265_ = lean_nat_add(v_startInclusive_261_, v_searcher_256_);
v___x_266_ = lean_string_utf8_get_fast(v_str_260_, v___x_265_);
v___x_267_ = 44;
v___x_268_ = lean_uint32_dec_eq(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
lean_dec(v_searcher_256_);
v___x_269_ = lean_string_utf8_next_fast(v_str_260_, v___x_265_);
lean_dec(v___x_265_);
v___x_270_ = lean_nat_sub(v___x_269_, v_startInclusive_261_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_270_);
v___x_272_ = v___x_258_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_currPos_255_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_270_);
v___x_272_ = v_reuseFailAlloc_274_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; 
v___x_273_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_242_, v___x_243_, v___x_244_, v___x_272_, v_b_246_);
return v___x_273_;
}
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v_slice_278_; lean_object* v_nextIt_280_; 
v___x_275_ = lean_string_utf8_next_fast(v_str_260_, v___x_265_);
v___x_276_ = lean_nat_sub(v___x_275_, v___x_265_);
lean_dec(v___x_265_);
v___x_277_ = lean_nat_add(v_searcher_256_, v___x_276_);
lean_dec(v___x_276_);
v_slice_278_ = l_String_Slice_subslice_x21(v___x_243_, v_currPos_255_, v_searcher_256_);
lean_inc(v___x_277_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v___x_277_);
lean_ctor_set(v___x_258_, 0, v___x_277_);
v_nextIt_280_ = v___x_258_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_277_);
v_nextIt_280_ = v_reuseFailAlloc_283_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v_startInclusive_281_; lean_object* v_endExclusive_282_; 
v_startInclusive_281_ = lean_ctor_get(v_slice_278_, 0);
lean_inc(v_startInclusive_281_);
v_endExclusive_282_ = lean_ctor_get(v_slice_278_, 1);
lean_inc(v_endExclusive_282_);
lean_dec_ref(v_slice_278_);
v_it_248_ = v_nextIt_280_;
v_startInclusive_249_ = v_startInclusive_281_;
v_endExclusive_250_ = v_endExclusive_282_;
goto v___jp_247_;
}
}
}
else
{
lean_object* v___x_284_; 
lean_del_object(v___x_258_);
lean_dec(v_searcher_256_);
v___x_284_ = lean_box(1);
lean_inc(v___x_244_);
v_it_248_ = v___x_284_;
v_startInclusive_249_ = v_currPos_255_;
v_endExclusive_250_ = v___x_244_;
goto v___jp_247_;
}
}
}
else
{
lean_dec(v___x_244_);
lean_dec_ref(v___x_242_);
return v_b_246_;
}
v___jp_247_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
lean_inc_ref(v___x_242_);
v___x_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_251_, 0, v___x_242_);
lean_ctor_set(v___x_251_, 1, v_startInclusive_249_);
lean_ctor_set(v___x_251_, 2, v_endExclusive_250_);
v___x_252_ = l_String_Slice_trimAscii(v___x_251_);
v___x_253_ = lean_array_push(v_b_246_, v___x_252_);
v___x_254_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_242_, v___x_243_, v___x_244_, v_it_248_, v___x_253_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(lean_object* v___x_286_, lean_object* v___x_287_, lean_object* v___x_288_, lean_object* v_a_289_, lean_object* v_b_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_286_, v___x_287_, v___x_288_, v_a_289_, v_b_290_);
lean_dec_ref(v___x_287_);
return v_res_291_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object* v___x_292_, lean_object* v___x_293_, lean_object* v___x_294_, lean_object* v_a_295_, uint8_t v_b_296_){
_start:
{
if (lean_obj_tag(v_a_295_) == 0)
{
lean_object* v_currPos_297_; lean_object* v_searcher_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_341_; 
v_currPos_297_ = lean_ctor_get(v_a_295_, 0);
v_searcher_298_ = lean_ctor_get(v_a_295_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_a_295_);
if (v_isSharedCheck_341_ == 0)
{
v___x_300_ = v_a_295_;
v_isShared_301_ = v_isSharedCheck_341_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_searcher_298_);
lean_inc(v_currPos_297_);
lean_dec(v_a_295_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_341_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_str_302_; lean_object* v_startInclusive_303_; lean_object* v_endExclusive_304_; uint8_t v___x_305_; lean_object* v_it_307_; lean_object* v_startInclusive_308_; lean_object* v_endExclusive_309_; lean_object* v___x_319_; uint8_t v_decide_320_; 
v_str_302_ = lean_ctor_get(v___x_293_, 0);
v_startInclusive_303_ = lean_ctor_get(v___x_293_, 1);
v_endExclusive_304_ = lean_ctor_get(v___x_293_, 2);
v___x_305_ = 1;
v___x_319_ = lean_nat_sub(v_endExclusive_304_, v_startInclusive_303_);
v_decide_320_ = lean_nat_dec_eq(v_searcher_298_, v___x_319_);
lean_dec(v___x_319_);
if (v_decide_320_ == 0)
{
lean_object* v___x_321_; uint32_t v___x_322_; uint32_t v___x_323_; uint8_t v___x_324_; 
v___x_321_ = lean_nat_add(v_startInclusive_303_, v_searcher_298_);
v___x_322_ = lean_string_utf8_get_fast(v_str_302_, v___x_321_);
v___x_323_ = 44;
v___x_324_ = lean_uint32_dec_eq(v___x_322_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
lean_dec(v_searcher_298_);
v___x_325_ = lean_string_utf8_next_fast(v_str_302_, v___x_321_);
lean_dec(v___x_321_);
v___x_326_ = lean_nat_sub(v___x_325_, v_startInclusive_303_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v___x_326_);
v___x_328_ = v___x_300_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_currPos_297_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v_a_295_ = v___x_328_;
goto _start;
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_slice_334_; lean_object* v_nextIt_336_; 
v___x_331_ = lean_string_utf8_next_fast(v_str_302_, v___x_321_);
v___x_332_ = lean_nat_sub(v___x_331_, v___x_321_);
lean_dec(v___x_321_);
v___x_333_ = lean_nat_add(v_searcher_298_, v___x_332_);
lean_dec(v___x_332_);
v_slice_334_ = l_String_Slice_subslice_x21(v___x_293_, v_currPos_297_, v_searcher_298_);
lean_inc(v___x_333_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v___x_333_);
lean_ctor_set(v___x_300_, 0, v___x_333_);
v_nextIt_336_ = v___x_300_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_333_);
v_nextIt_336_ = v_reuseFailAlloc_339_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v_startInclusive_337_; lean_object* v_endExclusive_338_; 
v_startInclusive_337_ = lean_ctor_get(v_slice_334_, 0);
lean_inc(v_startInclusive_337_);
v_endExclusive_338_ = lean_ctor_get(v_slice_334_, 1);
lean_inc(v_endExclusive_338_);
lean_dec_ref(v_slice_334_);
v_it_307_ = v_nextIt_336_;
v_startInclusive_308_ = v_startInclusive_337_;
v_endExclusive_309_ = v_endExclusive_338_;
goto v___jp_306_;
}
}
}
else
{
lean_object* v___x_340_; 
lean_del_object(v___x_300_);
lean_dec(v_searcher_298_);
v___x_340_ = lean_box(1);
lean_inc(v___x_294_);
v_it_307_ = v___x_340_;
v_startInclusive_308_ = v_currPos_297_;
v_endExclusive_309_ = v___x_294_;
goto v___jp_306_;
}
v___jp_306_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_startInclusive_312_; lean_object* v_endExclusive_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
lean_inc_ref(v___x_292_);
v___x_310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_310_, 0, v___x_292_);
lean_ctor_set(v___x_310_, 1, v_startInclusive_308_);
lean_ctor_set(v___x_310_, 2, v_endExclusive_309_);
v___x_311_ = l_String_Slice_trimAscii(v___x_310_);
v_startInclusive_312_ = lean_ctor_get(v___x_311_, 1);
lean_inc(v_startInclusive_312_);
v_endExclusive_313_ = lean_ctor_get(v___x_311_, 2);
lean_inc(v_endExclusive_313_);
lean_dec_ref(v___x_311_);
v___x_314_ = lean_nat_sub(v_endExclusive_313_, v_startInclusive_312_);
lean_dec(v_startInclusive_312_);
lean_dec(v_endExclusive_313_);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_nat_dec_eq(v___x_314_, v___x_315_);
lean_dec(v___x_314_);
if (v___x_316_ == 0)
{
v_a_295_ = v_it_307_;
v_b_296_ = v___x_305_;
goto _start;
}
else
{
uint8_t v___x_318_; 
lean_dec(v_it_307_);
lean_dec(v___x_294_);
lean_dec_ref(v___x_292_);
v___x_318_ = 0;
return v___x_318_;
}
}
}
}
else
{
lean_dec(v___x_294_);
lean_dec_ref(v___x_292_);
return v_b_296_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object* v___x_342_, lean_object* v___x_343_, lean_object* v___x_344_, lean_object* v_a_345_, lean_object* v_b_346_){
_start:
{
uint8_t v_b_boxed_347_; uint8_t v_res_348_; lean_object* v_r_349_; 
v_b_boxed_347_ = lean_unbox(v_b_346_);
v_res_348_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_342_, v___x_343_, v___x_344_, v_a_345_, v_b_boxed_347_);
lean_dec_ref(v___x_343_);
v_r_349_ = lean_box(v_res_348_);
return v_r_349_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object* v___x_350_, lean_object* v___x_351_, lean_object* v___x_352_, lean_object* v_a_353_, uint8_t v_b_354_){
_start:
{
if (lean_obj_tag(v_a_353_) == 0)
{
lean_object* v_currPos_355_; lean_object* v_searcher_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_399_; 
v_currPos_355_ = lean_ctor_get(v_a_353_, 0);
v_searcher_356_ = lean_ctor_get(v_a_353_, 1);
v_isSharedCheck_399_ = !lean_is_exclusive(v_a_353_);
if (v_isSharedCheck_399_ == 0)
{
v___x_358_ = v_a_353_;
v_isShared_359_ = v_isSharedCheck_399_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_searcher_356_);
lean_inc(v_currPos_355_);
lean_dec(v_a_353_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_399_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v_str_360_; lean_object* v_startInclusive_361_; lean_object* v_endExclusive_362_; uint8_t v___x_363_; lean_object* v_it_365_; lean_object* v_startInclusive_366_; lean_object* v_endExclusive_367_; lean_object* v___x_377_; uint8_t v_decide_378_; 
v_str_360_ = lean_ctor_get(v___x_351_, 0);
v_startInclusive_361_ = lean_ctor_get(v___x_351_, 1);
v_endExclusive_362_ = lean_ctor_get(v___x_351_, 2);
v___x_363_ = 1;
v___x_377_ = lean_nat_sub(v_endExclusive_362_, v_startInclusive_361_);
v_decide_378_ = lean_nat_dec_eq(v_searcher_356_, v___x_377_);
lean_dec(v___x_377_);
if (v_decide_378_ == 0)
{
lean_object* v___x_379_; uint32_t v___x_380_; uint32_t v___x_381_; uint8_t v___x_382_; 
v___x_379_ = lean_nat_add(v_startInclusive_361_, v_searcher_356_);
v___x_380_ = lean_string_utf8_get_fast(v_str_360_, v___x_379_);
v___x_381_ = 44;
v___x_382_ = lean_uint32_dec_eq(v___x_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
lean_dec(v_searcher_356_);
v___x_383_ = lean_string_utf8_next_fast(v_str_360_, v___x_379_);
lean_dec(v___x_379_);
v___x_384_ = lean_nat_sub(v___x_383_, v_startInclusive_361_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v___x_384_);
v___x_386_ = v___x_358_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_currPos_355_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_388_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
uint8_t v___x_387_; 
v___x_387_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_350_, v___x_351_, v___x_352_, v___x_386_, v_b_354_);
return v___x_387_;
}
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_slice_392_; lean_object* v_nextIt_394_; 
v___x_389_ = lean_string_utf8_next_fast(v_str_360_, v___x_379_);
v___x_390_ = lean_nat_sub(v___x_389_, v___x_379_);
lean_dec(v___x_379_);
v___x_391_ = lean_nat_add(v_searcher_356_, v___x_390_);
lean_dec(v___x_390_);
v_slice_392_ = l_String_Slice_subslice_x21(v___x_351_, v_currPos_355_, v_searcher_356_);
lean_inc(v___x_391_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v___x_391_);
lean_ctor_set(v___x_358_, 0, v___x_391_);
v_nextIt_394_ = v___x_358_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_391_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v___x_391_);
v_nextIt_394_ = v_reuseFailAlloc_397_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v_startInclusive_395_; lean_object* v_endExclusive_396_; 
v_startInclusive_395_ = lean_ctor_get(v_slice_392_, 0);
lean_inc(v_startInclusive_395_);
v_endExclusive_396_ = lean_ctor_get(v_slice_392_, 1);
lean_inc(v_endExclusive_396_);
lean_dec_ref(v_slice_392_);
v_it_365_ = v_nextIt_394_;
v_startInclusive_366_ = v_startInclusive_395_;
v_endExclusive_367_ = v_endExclusive_396_;
goto v___jp_364_;
}
}
}
else
{
lean_object* v___x_398_; 
lean_del_object(v___x_358_);
lean_dec(v_searcher_356_);
v___x_398_ = lean_box(1);
lean_inc(v___x_352_);
v_it_365_ = v___x_398_;
v_startInclusive_366_ = v_currPos_355_;
v_endExclusive_367_ = v___x_352_;
goto v___jp_364_;
}
v___jp_364_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_startInclusive_370_; lean_object* v_endExclusive_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
lean_inc_ref(v___x_350_);
v___x_368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_368_, 0, v___x_350_);
lean_ctor_set(v___x_368_, 1, v_startInclusive_366_);
lean_ctor_set(v___x_368_, 2, v_endExclusive_367_);
v___x_369_ = l_String_Slice_trimAscii(v___x_368_);
v_startInclusive_370_ = lean_ctor_get(v___x_369_, 1);
lean_inc(v_startInclusive_370_);
v_endExclusive_371_ = lean_ctor_get(v___x_369_, 2);
lean_inc(v_endExclusive_371_);
lean_dec_ref(v___x_369_);
v___x_372_ = lean_nat_sub(v_endExclusive_371_, v_startInclusive_370_);
lean_dec(v_startInclusive_370_);
lean_dec(v_endExclusive_371_);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_nat_dec_eq(v___x_372_, v___x_373_);
lean_dec(v___x_372_);
if (v___x_374_ == 0)
{
uint8_t v___x_375_; 
v___x_375_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_350_, v___x_351_, v___x_352_, v_it_365_, v___x_363_);
return v___x_375_;
}
else
{
uint8_t v___x_376_; 
lean_dec(v_it_365_);
lean_dec(v___x_352_);
lean_dec_ref(v___x_350_);
v___x_376_ = 0;
return v___x_376_;
}
}
}
}
else
{
lean_dec(v___x_352_);
lean_dec_ref(v___x_350_);
return v_b_354_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object* v___x_400_, lean_object* v___x_401_, lean_object* v___x_402_, lean_object* v_a_403_, lean_object* v_b_404_){
_start:
{
uint8_t v_b_boxed_405_; uint8_t v_res_406_; lean_object* v_r_407_; 
v_b_boxed_405_ = lean_unbox(v_b_404_);
v_res_406_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_400_, v___x_401_, v___x_402_, v_a_403_, v_b_boxed_405_);
lean_dec_ref(v___x_401_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object* v_v_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v_parts_414_; uint8_t v___x_415_; uint8_t v___x_416_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_string_utf8_byte_size(v_v_410_);
lean_inc_ref_n(v_v_410_, 2);
v___x_413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_413_, 0, v_v_410_);
lean_ctor_set(v___x_413_, 1, v___x_411_);
lean_ctor_set(v___x_413_, 2, v___x_412_);
v_parts_414_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
v___x_415_ = 1;
v___x_416_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_410_, v___x_413_, v___x_412_, v_parts_414_, v___x_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
lean_dec_ref_known(v___x_413_, 3);
lean_dec_ref(v_v_410_);
v___x_417_ = lean_box(0);
return v___x_417_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; size_t v_sz_420_; size_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_418_ = ((lean_object*)(l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0));
v___x_419_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v_v_410_, v___x_413_, v___x_412_, v_parts_414_, v___x_418_);
lean_dec_ref_known(v___x_413_, 3);
v_sz_420_ = lean_array_size(v___x_419_);
v___x_421_ = ((size_t)0ULL);
v___x_422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_420_, v___x_421_, v___x_419_);
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v___x_426_, lean_object* v_inst_427_, lean_object* v_R_428_, lean_object* v_a_429_, uint8_t v_b_430_, lean_object* v_c_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_424_, v___x_425_, v___x_426_, v_a_429_, v_b_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object* v___x_433_, lean_object* v___x_434_, lean_object* v___x_435_, lean_object* v_inst_436_, lean_object* v_R_437_, lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v_c_440_){
_start:
{
uint8_t v_b_boxed_441_; uint8_t v_res_442_; lean_object* v_r_443_; 
v_b_boxed_441_ = lean_unbox(v_b_439_);
v_res_442_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_433_, v___x_434_, v___x_435_, v_inst_436_, v_R_437_, v_a_438_, v_b_boxed_441_, v_c_440_);
lean_dec_ref(v___x_434_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object* v___x_444_, lean_object* v___x_445_, lean_object* v___x_446_, lean_object* v_inst_447_, lean_object* v_R_448_, lean_object* v_a_449_, lean_object* v_b_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_444_, v___x_445_, v___x_446_, v_a_449_, v_b_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object* v___x_452_, lean_object* v___x_453_, lean_object* v___x_454_, lean_object* v_inst_455_, lean_object* v_R_456_, lean_object* v_a_457_, lean_object* v_b_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_452_, v___x_453_, v___x_454_, v_inst_455_, v_R_456_, v_a_457_, v_b_458_);
lean_dec_ref(v___x_453_);
return v_res_459_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v_inst_463_, lean_object* v_R_464_, lean_object* v_a_465_, uint8_t v_b_466_, lean_object* v_c_467_){
_start:
{
uint8_t v___x_468_; 
v___x_468_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_460_, v___x_461_, v___x_462_, v_a_465_, v_b_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object* v___x_469_, lean_object* v___x_470_, lean_object* v___x_471_, lean_object* v_inst_472_, lean_object* v_R_473_, lean_object* v_a_474_, lean_object* v_b_475_, lean_object* v_c_476_){
_start:
{
uint8_t v_b_boxed_477_; uint8_t v_res_478_; lean_object* v_r_479_; 
v_b_boxed_477_ = lean_unbox(v_b_475_);
v_res_478_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_469_, v___x_470_, v___x_471_, v_inst_472_, v_R_473_, v_a_474_, v_b_boxed_477_, v_c_476_);
lean_dec_ref(v___x_470_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v_inst_483_, lean_object* v_R_484_, lean_object* v_a_485_, lean_object* v_b_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_480_, v___x_481_, v___x_482_, v_a_485_, v_b_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object* v___x_488_, lean_object* v___x_489_, lean_object* v___x_490_, lean_object* v_inst_491_, lean_object* v_R_492_, lean_object* v_a_493_, lean_object* v_b_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(v___x_488_, v___x_489_, v___x_490_, v_inst_491_, v_R_492_, v_a_493_, v_b_494_);
lean_dec_ref(v___x_489_);
return v_res_495_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqContentLength_beq(lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
uint8_t v___x_498_; 
v___x_498_ = lean_nat_dec_eq(v_x_496_, v_x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqContentLength_beq___boxed(lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
uint8_t v_res_501_; lean_object* v_r_502_; 
v_res_501_ = l_Std_Http_Header_instBEqContentLength_beq(v_x_499_, v_x_500_);
lean_dec(v_x_500_);
lean_dec(v_x_499_);
v_r_502_ = lean_box(v_res_501_);
return v_r_502_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprContentLength_repr_spec__0(lean_object* v_a_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = lean_nat_to_int(v_a_505_);
return v___x_506_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_unsigned_to_nat(10u);
v___x_521_ = lean_nat_to_int(v___x_520_);
return v___x_521_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0));
v___x_524_ = lean_string_length(v___x_523_);
return v___x_524_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9);
v___x_526_ = lean_nat_to_int(v___x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg(lean_object* v_x_531_){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_532_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6));
v___x_533_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_534_ = l_Nat_reprFast(v_x_531_);
v___x_535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
v___x_536_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = 0;
v___x_538_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_538_, 0, v___x_536_);
lean_ctor_set_uint8(v___x_538_, sizeof(void*)*1, v___x_537_);
v___x_539_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_532_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_541_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_542_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v___x_539_);
v___x_543_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_544_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_540_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set_uint8(v___x_546_, sizeof(void*)*1, v___x_537_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr(lean_object* v_x_547_, lean_object* v_prec_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Std_Http_Header_instReprContentLength_repr___redArg(v_x_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___boxed(lean_object* v_x_550_, lean_object* v_prec_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_Http_Header_instReprContentLength_repr(v_x_550_, v_prec_551_);
lean_dec(v_prec_551_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(lean_object* v_s_555_, lean_object* v_pos_556_){
_start:
{
lean_object* v_str_557_; lean_object* v_startInclusive_558_; lean_object* v_endExclusive_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v_decide_563_; 
v_str_557_ = lean_ctor_get(v_s_555_, 0);
v_startInclusive_558_ = lean_ctor_get(v_s_555_, 1);
v_endExclusive_559_ = lean_ctor_get(v_s_555_, 2);
v___x_560_ = lean_nat_add(v_startInclusive_558_, v_pos_556_);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_nat_sub(v_endExclusive_559_, v___x_560_);
v_decide_563_ = lean_nat_dec_eq(v___x_561_, v___x_562_);
lean_dec(v___x_562_);
if (v_decide_563_ == 0)
{
uint32_t v___x_564_; uint32_t v___x_565_; uint8_t v___x_566_; 
v___x_564_ = lean_string_utf8_get_fast(v_str_557_, v___x_560_);
v___x_565_ = 48;
v___x_566_ = lean_uint32_dec_le(v___x_565_, v___x_564_);
if (v___x_566_ == 0)
{
lean_dec(v___x_560_);
return v_pos_556_;
}
else
{
uint32_t v___x_567_; uint8_t v___x_568_; 
v___x_567_ = 57;
v___x_568_ = lean_uint32_dec_le(v___x_564_, v___x_567_);
if (v___x_568_ == 0)
{
lean_dec(v___x_560_);
return v_pos_556_;
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_569_ = lean_string_utf8_next_fast(v_str_557_, v___x_560_);
v___x_570_ = lean_nat_sub(v___x_569_, v___x_560_);
lean_dec(v___x_560_);
v___x_571_ = lean_nat_add(v_pos_556_, v___x_570_);
lean_dec(v___x_570_);
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = lean_nat_add(v_pos_556_, v___x_572_);
v___x_574_ = lean_nat_dec_le(v___x_573_, v___x_571_);
lean_dec(v___x_573_);
if (v___x_574_ == 0)
{
lean_dec(v___x_571_);
return v_pos_556_;
}
else
{
lean_dec(v_pos_556_);
v_pos_556_ = v___x_571_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_560_);
return v_pos_556_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0___boxed(lean_object* v_s_576_, lean_object* v_pos_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v_s_576_, v_pos_577_);
lean_dec_ref(v_s_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_parse(lean_object* v_v_579_){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_string_utf8_byte_size(v_v_579_);
v___x_581_ = lean_unsigned_to_nat(0u);
v___x_582_ = lean_nat_dec_eq(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v_decide_585_; 
v___x_583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_583_, 0, v_v_579_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
lean_ctor_set(v___x_583_, 2, v___x_580_);
v___x_584_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v___x_583_, v___x_581_);
v_decide_585_ = lean_nat_dec_eq(v___x_584_, v___x_580_);
lean_dec(v___x_584_);
if (v_decide_585_ == 0)
{
lean_object* v___x_586_; 
lean_dec_ref_known(v___x_583_, 3);
v___x_586_ = lean_box(0);
return v___x_586_;
}
else
{
lean_object* v___x_587_; 
v___x_587_ = l_String_Slice_toNat_x3f(v___x_583_);
lean_dec_ref_known(v___x_583_, 3);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_box(0);
return v___x_588_;
}
else
{
lean_object* v_val_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_val_589_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_587_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_val_589_);
lean_dec(v___x_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_val_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
else
{
lean_object* v___x_597_; 
lean_dec_ref(v_v_579_);
v___x_597_ = lean_box(0);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_serialize(lean_object* v_h_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_599_ = l_Std_Http_Header_Name_contentLength;
v___x_600_ = l_Nat_reprFast(v_h_598_);
v___x_601_ = l_Std_Http_Header_Value_ofString_x21(v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_599_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
if (lean_obj_tag(v_x_609_) == 0)
{
if (lean_obj_tag(v_x_610_) == 0)
{
uint8_t v___x_611_; 
v___x_611_ = 1;
return v___x_611_;
}
else
{
uint8_t v___x_612_; 
v___x_612_ = 0;
return v___x_612_;
}
}
else
{
if (lean_obj_tag(v_x_610_) == 0)
{
uint8_t v___x_613_; 
v___x_613_ = 0;
return v___x_613_;
}
else
{
lean_object* v_val_614_; lean_object* v_val_615_; uint8_t v___x_616_; 
v_val_614_ = lean_ctor_get(v_x_609_, 0);
v_val_615_ = lean_ctor_get(v_x_610_, 0);
v___x_616_ = lean_string_dec_eq(v_val_614_, v_val_615_);
return v___x_616_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_617_, v_x_618_);
lean_dec(v_x_618_);
lean_dec(v_x_617_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object* v_as_622_, size_t v_i_623_, size_t v_stop_624_, lean_object* v_b_625_){
_start:
{
lean_object* v___y_627_; uint8_t v___x_631_; 
v___x_631_ = lean_usize_dec_eq(v_i_623_, v_stop_624_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_array_uget_borrowed(v_as_622_, v_i_623_);
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_634_ = lean_string_dec_eq(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
v___y_627_ = v_b_625_;
goto v___jp_626_;
}
else
{
lean_object* v___x_635_; 
lean_inc(v___x_632_);
v___x_635_ = lean_array_push(v_b_625_, v___x_632_);
v___y_627_ = v___x_635_;
goto v___jp_626_;
}
}
else
{
return v_b_625_;
}
v___jp_626_:
{
size_t v___x_628_; size_t v___x_629_; 
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_add(v_i_623_, v___x_628_);
v_i_623_ = v___x_629_;
v_b_625_ = v___y_627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object* v_as_636_, lean_object* v_i_637_, lean_object* v_stop_638_, lean_object* v_b_639_){
_start:
{
size_t v_i_boxed_640_; size_t v_stop_boxed_641_; lean_object* v_res_642_; 
v_i_boxed_640_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_stop_boxed_641_ = lean_unbox_usize(v_stop_638_);
lean_dec(v_stop_638_);
v_res_642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_636_, v_i_boxed_640_, v_stop_boxed_641_, v_b_639_);
lean_dec_ref(v_as_636_);
return v_res_642_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object* v___x_643_, lean_object* v_as_644_, size_t v_i_645_, size_t v_stop_646_){
_start:
{
uint8_t v___x_647_; 
v___x_647_ = lean_usize_dec_eq(v_i_645_, v_stop_646_);
if (v___x_647_ == 0)
{
uint8_t v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_648_ = 1;
v___x_649_ = lean_array_uget_borrowed(v_as_644_, v_i_645_);
lean_inc(v___x_649_);
v___x_650_ = l_Std_Http_Internal_isToken(v___x_649_);
if (v___x_650_ == 0)
{
return v___x_648_;
}
else
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_nat_dec_eq(v___x_643_, v___x_651_);
if (v___x_652_ == 0)
{
size_t v___x_653_; size_t v___x_654_; 
v___x_653_ = ((size_t)1ULL);
v___x_654_ = lean_usize_add(v_i_645_, v___x_653_);
v_i_645_ = v___x_654_;
goto _start;
}
else
{
return v___x_648_;
}
}
}
else
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object* v___x_657_, lean_object* v_as_658_, lean_object* v_i_659_, lean_object* v_stop_660_){
_start:
{
size_t v_i_boxed_661_; size_t v_stop_boxed_662_; uint8_t v_res_663_; lean_object* v_r_664_; 
v_i_boxed_661_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_stop_boxed_662_ = lean_unbox_usize(v_stop_660_);
lean_dec(v_stop_660_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_657_, v_as_658_, v_i_boxed_661_, v_stop_boxed_662_);
lean_dec_ref(v_as_658_);
lean_dec(v___x_657_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object* v_codings_669_){
_start:
{
uint8_t v___y_671_; uint8_t v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; uint8_t v___y_681_; uint8_t v___y_682_; lean_object* v___y_683_; uint8_t v___y_693_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_array_get_size(v_codings_669_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_nat_dec_eq(v___x_702_, v___x_703_);
if (v___x_704_ == 0)
{
uint8_t v___x_705_; 
v___x_705_ = lean_nat_dec_lt(v___x_703_, v___x_702_);
if (v___x_705_ == 0)
{
v___y_693_ = v___x_705_;
goto v___jp_692_;
}
else
{
if (v___x_705_ == 0)
{
v___y_693_ = v___x_705_;
goto v___jp_692_;
}
else
{
size_t v___x_706_; size_t v___x_707_; uint8_t v___x_708_; 
v___x_706_ = ((size_t)0ULL);
v___x_707_ = lean_usize_of_nat(v___x_702_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_702_, v_codings_669_, v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
v___y_693_ = v___x_708_;
goto v___jp_692_;
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
v___jp_670_:
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(1u);
v___x_676_ = lean_nat_dec_lt(v___x_675_, v___y_673_);
if (v___x_676_ == 0)
{
uint8_t v___x_677_; 
v___x_677_ = lean_nat_dec_eq(v___y_673_, v___x_675_);
lean_dec(v___y_673_);
if (v___x_677_ == 0)
{
lean_dec(v___y_674_);
return v___y_671_;
}
else
{
lean_object* v___x_678_; uint8_t v_lastIsChunked_679_; 
v___x_678_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v_lastIsChunked_679_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_674_, v___x_678_);
lean_dec(v___y_674_);
if (v_lastIsChunked_679_ == 0)
{
return v___x_676_;
}
else
{
return v___y_671_;
}
}
}
else
{
lean_dec(v___y_674_);
lean_dec(v___y_673_);
return v___y_672_;
}
}
v___jp_680_:
{
lean_object* v_chunkedCount_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_chunkedCount_684_ = lean_array_get_size(v___y_683_);
lean_dec_ref(v___y_683_);
v___x_685_ = lean_array_get_size(v_codings_669_);
v___x_686_ = lean_unsigned_to_nat(1u);
v___x_687_ = lean_nat_sub(v___x_685_, v___x_686_);
v___x_688_ = lean_nat_dec_lt(v___x_687_, v___x_685_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec(v___x_687_);
v___x_689_ = lean_box(0);
v___y_671_ = v___y_681_;
v___y_672_ = v___y_682_;
v___y_673_ = v_chunkedCount_684_;
v___y_674_ = v___x_689_;
goto v___jp_670_;
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_array_fget_borrowed(v_codings_669_, v___x_687_);
lean_dec(v___x_687_);
lean_inc(v___x_690_);
v___x_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
v___y_671_ = v___y_681_;
v___y_672_ = v___y_682_;
v___y_673_ = v_chunkedCount_684_;
v___y_674_ = v___x_691_;
goto v___jp_670_;
}
}
v___jp_692_:
{
uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_694_ = 1;
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_array_get_size(v_codings_669_);
v___x_697_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__1));
v___x_698_ = lean_nat_dec_lt(v___x_695_, v___x_696_);
if (v___x_698_ == 0)
{
v___y_681_ = v___x_694_;
v___y_682_ = v___y_693_;
v___y_683_ = v___x_697_;
goto v___jp_680_;
}
else
{
size_t v___x_699_; size_t v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((size_t)0ULL);
v___x_700_ = lean_usize_of_nat(v___x_696_);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_669_, v___x_699_, v___x_700_, v___x_697_);
v___y_681_ = v___x_694_;
v___y_682_ = v___y_693_;
v___y_683_ = v___x_701_;
goto v___jp_680_;
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
v___x_845_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_843_, v___x_844_);
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
v_array_1151_ = lean_ctor_get(v_pos_1150_, 0);
v_idx_1152_ = lean_ctor_get(v_pos_1150_, 1);
v___x_1153_ = lean_byte_array_size(v_array_1151_);
v___x_1154_ = lean_nat_dec_lt(v_idx_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
return v___x_1149_;
}
else
{
lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1162_; 
lean_inc(v_pos_1150_);
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
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_serialize(lean_object* v_host_1202_){
_start:
{
lean_object* v___y_1204_; lean_object* v___y_1208_; lean_object* v_port_1212_; 
v_port_1212_ = lean_ctor_get(v_host_1202_, 1);
switch(lean_obj_tag(v_port_1212_))
{
case 0:
{
lean_object* v_host_1213_; 
v_host_1213_ = lean_ctor_get(v_host_1202_, 0);
lean_inc_ref(v_host_1213_);
lean_dec_ref(v_host_1202_);
switch(lean_obj_tag(v_host_1213_))
{
case 0:
{
lean_object* v_name_1214_; lean_object* v___x_1215_; 
v_name_1214_ = lean_ctor_get(v_host_1213_, 0);
lean_inc_ref(v_name_1214_);
lean_dec_ref_known(v_host_1213_, 1);
v___x_1215_ = l_Std_Http_Header_Value_ofString_x21(v_name_1214_);
v___y_1204_ = v___x_1215_;
goto v___jp_1203_;
}
case 1:
{
lean_object* v_ipv4_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_ipv4_1216_ = lean_ctor_get(v_host_1213_, 0);
lean_inc_ref(v_ipv4_1216_);
lean_dec_ref_known(v_host_1213_, 1);
v___x_1217_ = lean_uv_ntop_v4(v_ipv4_1216_);
lean_dec_ref(v_ipv4_1216_);
v___x_1218_ = l_Std_Http_Header_Value_ofString_x21(v___x_1217_);
v___y_1204_ = v___x_1218_;
goto v___jp_1203_;
}
default: 
{
lean_object* v_ipv6_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_ipv6_1219_ = lean_ctor_get(v_host_1213_, 0);
lean_inc_ref(v_ipv6_1219_);
lean_dec_ref_known(v_host_1213_, 1);
v___x_1220_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1221_ = lean_uv_ntop_v6(v_ipv6_1219_);
lean_dec_ref(v_ipv6_1219_);
v___x_1222_ = lean_string_append(v___x_1220_, v___x_1221_);
lean_dec_ref(v___x_1221_);
v___x_1223_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1224_ = lean_string_append(v___x_1222_, v___x_1223_);
v___x_1225_ = l_Std_Http_Header_Value_ofString_x21(v___x_1224_);
v___y_1204_ = v___x_1225_;
goto v___jp_1203_;
}
}
}
case 1:
{
lean_object* v_host_1226_; 
v_host_1226_ = lean_ctor_get(v_host_1202_, 0);
lean_inc_ref(v_host_1226_);
lean_dec_ref(v_host_1202_);
switch(lean_obj_tag(v_host_1226_))
{
case 0:
{
lean_object* v_name_1227_; 
v_name_1227_ = lean_ctor_get(v_host_1226_, 0);
lean_inc_ref(v_name_1227_);
lean_dec_ref_known(v_host_1226_, 1);
v___y_1208_ = v_name_1227_;
goto v___jp_1207_;
}
case 1:
{
lean_object* v_ipv4_1228_; lean_object* v___x_1229_; 
v_ipv4_1228_ = lean_ctor_get(v_host_1226_, 0);
lean_inc_ref(v_ipv4_1228_);
lean_dec_ref_known(v_host_1226_, 1);
v___x_1229_ = lean_uv_ntop_v4(v_ipv4_1228_);
lean_dec_ref(v_ipv4_1228_);
v___y_1208_ = v___x_1229_;
goto v___jp_1207_;
}
default: 
{
lean_object* v_ipv6_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_ipv6_1230_ = lean_ctor_get(v_host_1226_, 0);
lean_inc_ref(v_ipv6_1230_);
lean_dec_ref_known(v_host_1226_, 1);
v___x_1231_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1232_ = lean_uv_ntop_v6(v_ipv6_1230_);
lean_dec_ref(v_ipv6_1230_);
v___x_1233_ = lean_string_append(v___x_1231_, v___x_1232_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1235_ = lean_string_append(v___x_1233_, v___x_1234_);
v___y_1208_ = v___x_1235_;
goto v___jp_1207_;
}
}
}
default: 
{
lean_object* v_host_1236_; uint16_t v_port_1237_; lean_object* v___y_1239_; 
lean_inc_ref(v_port_1212_);
v_host_1236_ = lean_ctor_get(v_host_1202_, 0);
lean_inc_ref(v_host_1236_);
lean_dec_ref(v_host_1202_);
v_port_1237_ = lean_ctor_get_uint16(v_port_1212_, 0);
lean_dec_ref_known(v_port_1212_, 0);
switch(lean_obj_tag(v_host_1236_))
{
case 0:
{
lean_object* v_name_1246_; 
v_name_1246_ = lean_ctor_get(v_host_1236_, 0);
lean_inc_ref(v_name_1246_);
lean_dec_ref_known(v_host_1236_, 1);
v___y_1239_ = v_name_1246_;
goto v___jp_1238_;
}
case 1:
{
lean_object* v_ipv4_1247_; lean_object* v___x_1248_; 
v_ipv4_1247_ = lean_ctor_get(v_host_1236_, 0);
lean_inc_ref(v_ipv4_1247_);
lean_dec_ref_known(v_host_1236_, 1);
v___x_1248_ = lean_uv_ntop_v4(v_ipv4_1247_);
lean_dec_ref(v_ipv4_1247_);
v___y_1239_ = v___x_1248_;
goto v___jp_1238_;
}
default: 
{
lean_object* v_ipv6_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_ipv6_1249_ = lean_ctor_get(v_host_1236_, 0);
lean_inc_ref(v_ipv6_1249_);
lean_dec_ref_known(v_host_1236_, 1);
v___x_1250_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1251_ = lean_uv_ntop_v6(v_ipv6_1249_);
lean_dec_ref(v_ipv6_1249_);
v___x_1252_ = lean_string_append(v___x_1250_, v___x_1251_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1254_ = lean_string_append(v___x_1252_, v___x_1253_);
v___y_1239_ = v___x_1254_;
goto v___jp_1238_;
}
}
v___jp_1238_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1240_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1241_ = lean_string_append(v___y_1239_, v___x_1240_);
v___x_1242_ = lean_uint16_to_nat(v_port_1237_);
v___x_1243_ = l_Nat_reprFast(v___x_1242_);
v___x_1244_ = lean_string_append(v___x_1241_, v___x_1243_);
lean_dec_ref(v___x_1243_);
v___x_1245_ = l_Std_Http_Header_Value_ofString_x21(v___x_1244_);
v___y_1204_ = v___x_1245_;
goto v___jp_1203_;
}
}
}
v___jp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__0));
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___y_1204_);
return v___x_1206_;
}
v___jp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1210_ = lean_string_append(v___y_1208_, v___x_1209_);
v___x_1211_ = l_Std_Http_Header_Value_ofString_x21(v___x_1210_);
v___y_1204_ = v___x_1211_;
goto v___jp_1203_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = ((lean_object*)(l_Std_Http_Header_instReprExpect_repr___redArg___closed__1));
v___x_1268_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1269_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3(void){
_start:
{
uint8_t v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = 0;
v___x_1271_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__2, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__2_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2);
v___x_1272_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
lean_ctor_set_uint8(v___x_1272_, sizeof(void*)*1, v___x_1270_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg(){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__3, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__3_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___boxed(lean_object* v___dummy_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v_res_1276_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___closed__0(void){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr(lean_object* v_x_1278_, lean_object* v_prec_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___closed__0, &l_Std_Http_Header_instReprExpect_repr___closed__0_once, _init_l_Std_Http_Header_instReprExpect_repr___closed__0);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___boxed(lean_object* v_x_1281_, lean_object* v_prec_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Std_Http_Header_instReprExpect_repr(v_x_1281_, v_prec_1282_);
lean_dec(v_prec_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq___redArg(){
_start:
{
uint8_t v___x_1287_; 
v___x_1287_ = 1;
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___redArg___boxed(lean_object* v___dummy_1288_){
_start:
{
uint8_t v_res_1289_; lean_object* v_r_1290_; 
v_res_1289_ = l_Std_Http_Header_instBEqExpect_beq___redArg();
v_r_1290_ = lean_box(v_res_1289_);
return v_r_1290_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq(lean_object* v_x_1291_, lean_object* v_y_1292_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = 1;
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___boxed(lean_object* v_x_1294_, lean_object* v_y_1295_){
_start:
{
uint8_t v_res_1296_; lean_object* v_r_1297_; 
v_res_1296_ = l_Std_Http_Header_instBEqExpect_beq(v_x_1294_, v_y_1295_);
v_r_1297_ = lean_box(v_res_1296_);
return v_r_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_parse(lean_object* v_v_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v_normalized_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_string_utf8_byte_size(v_v_1303_);
v___x_1306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1306_, 0, v_v_1303_);
lean_ctor_set(v___x_1306_, 1, v___x_1304_);
lean_ctor_set(v___x_1306_, 2, v___x_1305_);
v___x_1307_ = l_String_Slice_trimAscii(v___x_1306_);
v___x_1308_ = l_String_Slice_toString(v___x_1307_);
lean_dec_ref(v___x_1307_);
v_normalized_1309_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_1308_, v___x_1304_);
v___x_1310_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1311_ = lean_string_dec_eq(v_normalized_1309_, v___x_1310_);
lean_dec_ref(v_normalized_1309_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_box(0);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; 
v___x_1313_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__1));
return v___x_1313_;
}
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1315_ = l_Std_Http_Header_Value_ofString_x21(v___x_1314_);
return v___x_1315_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1(void){
_start:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__0, &l_Std_Http_Header_Expect_serialize___redArg___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0);
v___x_1317_ = l_Std_Http_Header_Name_expect;
v___x_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
lean_ctor_set(v___x_1318_, 1, v___x_1316_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg(){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__1, &l_Std_Http_Header_Expect_serialize___redArg___closed__1_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg___boxed(lean_object* v___dummy_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_Http_Header_Expect_serialize___redArg();
return v_res_1322_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___closed__0(void){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Std_Http_Header_Expect_serialize___redArg();
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize(lean_object* v_x_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___closed__0, &l_Std_Http_Header_Expect_serialize___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___closed__0);
return v___x_1325_;
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

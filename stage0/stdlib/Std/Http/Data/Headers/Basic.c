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
lean_object* l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(lean_object*);
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
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_value;
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
static const lean_ctor_object l_Std_Http_Header_instReprExpect_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Http_Header_instReprExpect_repr___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprExpect_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_Header_instReprExpect_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Header_instReprExpect_repr___closed__0_value),((lean_object*)&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12_value)}};
static const lean_object* l_Std_Http_Header_instReprExpect_repr___closed__1 = (const lean_object*)&l_Std_Http_Header_instReprExpect_repr___closed__1_value;
static lean_once_cell_t l_Std_Http_Header_instReprExpect_repr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprExpect_repr___closed__2;
static lean_once_cell_t l_Std_Http_Header_instReprExpect_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_instReprExpect_repr___closed__3;
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Header_instReprExpect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_instReprExpect_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Header_instReprExpect___closed__0 = (const lean_object*)&l_Std_Http_Header_instReprExpect___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Header_instReprExpect = (const lean_object*)&l_Std_Http_Header_instReprExpect___closed__0_value;
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
static lean_once_cell_t l_Std_Http_Header_Expect_serialize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Expect_serialize___closed__0;
static lean_once_cell_t l_Std_Http_Header_Expect_serialize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Header_Expect_serialize___closed__1;
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
lean_object* v_it_13_; lean_object* v_out_14_; lean_object* v___y_30_; lean_object* v___y_31_; uint32_t v___y_32_; uint8_t v___y_33_; lean_object* v_it_39_; lean_object* v_startInclusive_40_; lean_object* v_endExclusive_41_; 
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
v___x_34_ = lean_string_utf8_set(v___y_30_, v___x_2_, v___y_32_);
v_it_13_ = v___y_31_;
v_out_14_ = v___x_34_;
goto v___jp_12_;
}
else
{
uint32_t v___x_35_; uint32_t v___x_36_; lean_object* v___x_37_; 
v___x_35_ = 4294967264;
v___x_36_ = lean_uint32_add(v___y_32_, v___x_35_);
v___x_37_ = lean_string_utf8_set(v___y_30_, v___x_2_, v___x_36_);
v_it_13_ = v___y_31_;
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
v___y_31_ = v_it_39_;
v___y_32_ = v___x_43_;
v___y_33_ = v___x_45_;
goto v___jp_29_;
}
else
{
uint32_t v___x_46_; uint8_t v___x_47_; 
v___x_46_ = 122;
v___x_47_ = lean_uint32_dec_le(v___x_43_, v___x_46_);
v___y_30_ = v___x_42_;
v___y_31_ = v_it_39_;
v___y_32_ = v___x_43_;
v___y_33_ = v___x_47_;
goto v___jp_29_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0___boxed(lean_object* v___x_72_, lean_object* v___x_73_, lean_object* v___x_74_, lean_object* v_fst_75_, lean_object* v___x_76_, lean_object* v___x_77_, lean_object* v___x_78_, lean_object* v_it_79_, lean_object* v_acc_80_, lean_object* v_hP_81_, lean_object* v_recur_82_){
_start:
{
uint32_t v___x_1421__boxed_83_; lean_object* v_res_84_; 
v___x_1421__boxed_83_ = lean_unbox_uint32(v___x_77_);
lean_dec(v___x_77_);
v_res_84_ = l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(v___x_72_, v___x_73_, v___x_74_, v_fst_75_, v___x_76_, v___x_1421__boxed_83_, v___x_78_, v_it_79_, v_acc_80_, v_hP_81_, v_recur_82_);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(lean_object* v_s_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0));
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(lean_object* v_s_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v_s_143_);
lean_dec_ref(v_s_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(lean_object* v_s_145_, lean_object* v_p_146_){
_start:
{
uint32_t v___y_148_; lean_object* v___x_153_; uint8_t v_decide_154_; 
v___x_153_ = lean_string_utf8_byte_size(v_s_145_);
v_decide_154_ = lean_nat_dec_eq(v_p_146_, v___x_153_);
if (v_decide_154_ == 0)
{
uint32_t v___x_155_; uint8_t v___y_157_; uint32_t v___x_160_; uint8_t v___x_161_; 
v___x_155_ = lean_string_utf8_get_fast(v_s_145_, v_p_146_);
v___x_160_ = 65;
v___x_161_ = lean_uint32_dec_le(v___x_160_, v___x_155_);
if (v___x_161_ == 0)
{
v___y_157_ = v___x_161_;
goto v___jp_156_;
}
else
{
uint32_t v___x_162_; uint8_t v___x_163_; 
v___x_162_ = 90;
v___x_163_ = lean_uint32_dec_le(v___x_155_, v___x_162_);
v___y_157_ = v___x_163_;
goto v___jp_156_;
}
v___jp_156_:
{
if (v___y_157_ == 0)
{
v___y_148_ = v___x_155_;
goto v___jp_147_;
}
else
{
uint32_t v___x_158_; uint32_t v___x_159_; 
v___x_158_ = 32;
v___x_159_ = lean_uint32_add(v___x_155_, v___x_158_);
v___y_148_ = v___x_159_;
goto v___jp_147_;
}
}
}
else
{
lean_dec(v_p_146_);
return v_s_145_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
lean_inc(v_p_146_);
v___x_149_ = lean_string_utf8_set(v_s_145_, v_p_146_, v___y_148_);
v___x_150_ = l_Char_utf8Size(v___y_148_);
v___x_151_ = lean_nat_add(v_p_146_, v___x_150_);
lean_dec(v___x_150_);
lean_dec(v_p_146_);
v_s_145_ = v___x_149_;
v_p_146_ = v___x_151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t v_sz_164_, size_t v_i_165_, lean_object* v_bs_166_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = lean_usize_dec_lt(v_i_165_, v_sz_164_);
if (v___x_167_ == 0)
{
return v_bs_166_;
}
else
{
lean_object* v_v_168_; lean_object* v___x_169_; lean_object* v_bs_x27_170_; lean_object* v___x_171_; lean_object* v___x_172_; size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; 
v_v_168_ = lean_array_uget(v_bs_166_, v_i_165_);
v___x_169_ = lean_unsigned_to_nat(0u);
v_bs_x27_170_ = lean_array_uset(v_bs_166_, v_i_165_, v___x_169_);
v___x_171_ = l_String_Slice_toString(v_v_168_);
lean_dec(v_v_168_);
v___x_172_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_171_, v___x_169_);
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_add(v_i_165_, v___x_173_);
v___x_175_ = lean_array_uset(v_bs_x27_170_, v_i_165_, v___x_172_);
v_i_165_ = v___x_174_;
v_bs_166_ = v___x_175_;
goto _start;
}
}
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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object* v___x_283_, lean_object* v___x_284_, lean_object* v___x_285_, lean_object* v_a_286_, uint8_t v_b_287_){
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object* v___x_333_, lean_object* v___x_334_, lean_object* v___x_335_, lean_object* v_a_336_, lean_object* v_b_337_){
_start:
{
uint8_t v_b_boxed_338_; uint8_t v_res_339_; lean_object* v_r_340_; 
v_b_boxed_338_ = lean_unbox(v_b_337_);
v_res_339_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_333_, v___x_334_, v___x_335_, v_a_336_, v_b_boxed_338_);
lean_dec_ref(v___x_334_);
v_r_340_ = lean_box(v_res_339_);
return v_r_340_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object* v___x_341_, lean_object* v___x_342_, lean_object* v___x_343_, lean_object* v_a_344_, uint8_t v_b_345_){
_start:
{
if (lean_obj_tag(v_a_344_) == 0)
{
lean_object* v_currPos_346_; lean_object* v_searcher_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_390_; 
v_currPos_346_ = lean_ctor_get(v_a_344_, 0);
v_searcher_347_ = lean_ctor_get(v_a_344_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_a_344_);
if (v_isSharedCheck_390_ == 0)
{
v___x_349_ = v_a_344_;
v_isShared_350_ = v_isSharedCheck_390_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_searcher_347_);
lean_inc(v_currPos_346_);
lean_dec(v_a_344_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_390_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v_str_351_; lean_object* v_startInclusive_352_; lean_object* v_endExclusive_353_; uint8_t v___x_354_; lean_object* v_it_356_; lean_object* v_startInclusive_357_; lean_object* v_endExclusive_358_; lean_object* v___x_368_; uint8_t v_decide_369_; 
v_str_351_ = lean_ctor_get(v___x_342_, 0);
v_startInclusive_352_ = lean_ctor_get(v___x_342_, 1);
v_endExclusive_353_ = lean_ctor_get(v___x_342_, 2);
v___x_354_ = 1;
v___x_368_ = lean_nat_sub(v_endExclusive_353_, v_startInclusive_352_);
v_decide_369_ = lean_nat_dec_eq(v_searcher_347_, v___x_368_);
lean_dec(v___x_368_);
if (v_decide_369_ == 0)
{
lean_object* v___x_370_; uint32_t v___x_371_; uint32_t v___x_372_; uint8_t v___x_373_; 
v___x_370_ = lean_nat_add(v_startInclusive_352_, v_searcher_347_);
v___x_371_ = lean_string_utf8_get_fast(v_str_351_, v___x_370_);
v___x_372_ = 44;
v___x_373_ = lean_uint32_dec_eq(v___x_371_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
lean_dec(v_searcher_347_);
v___x_374_ = lean_string_utf8_next_fast(v_str_351_, v___x_370_);
lean_dec(v___x_370_);
v___x_375_ = lean_nat_sub(v___x_374_, v_startInclusive_352_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v___x_375_);
v___x_377_ = v___x_349_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_currPos_346_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
uint8_t v___x_378_; 
v___x_378_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_341_, v___x_342_, v___x_343_, v___x_377_, v_b_345_);
return v___x_378_;
}
}
else
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v_slice_383_; lean_object* v_nextIt_385_; 
v___x_380_ = lean_string_utf8_next_fast(v_str_351_, v___x_370_);
v___x_381_ = lean_nat_sub(v___x_380_, v___x_370_);
lean_dec(v___x_370_);
v___x_382_ = lean_nat_add(v_searcher_347_, v___x_381_);
lean_dec(v___x_381_);
v_slice_383_ = l_String_Slice_subslice_x21(v___x_342_, v_currPos_346_, v_searcher_347_);
lean_inc(v___x_382_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v___x_382_);
lean_ctor_set(v___x_349_, 0, v___x_382_);
v_nextIt_385_ = v___x_349_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___x_382_);
v_nextIt_385_ = v_reuseFailAlloc_388_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v_startInclusive_386_; lean_object* v_endExclusive_387_; 
v_startInclusive_386_ = lean_ctor_get(v_slice_383_, 0);
lean_inc(v_startInclusive_386_);
v_endExclusive_387_ = lean_ctor_get(v_slice_383_, 1);
lean_inc(v_endExclusive_387_);
lean_dec_ref(v_slice_383_);
v_it_356_ = v_nextIt_385_;
v_startInclusive_357_ = v_startInclusive_386_;
v_endExclusive_358_ = v_endExclusive_387_;
goto v___jp_355_;
}
}
}
else
{
lean_object* v___x_389_; 
lean_del_object(v___x_349_);
lean_dec(v_searcher_347_);
v___x_389_ = lean_box(1);
lean_inc(v___x_343_);
v_it_356_ = v___x_389_;
v_startInclusive_357_ = v_currPos_346_;
v_endExclusive_358_ = v___x_343_;
goto v___jp_355_;
}
v___jp_355_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_startInclusive_361_; lean_object* v_endExclusive_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
lean_inc_ref(v___x_341_);
v___x_359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_359_, 0, v___x_341_);
lean_ctor_set(v___x_359_, 1, v_startInclusive_357_);
lean_ctor_set(v___x_359_, 2, v_endExclusive_358_);
v___x_360_ = l_String_Slice_trimAscii(v___x_359_);
v_startInclusive_361_ = lean_ctor_get(v___x_360_, 1);
lean_inc(v_startInclusive_361_);
v_endExclusive_362_ = lean_ctor_get(v___x_360_, 2);
lean_inc(v_endExclusive_362_);
lean_dec_ref(v___x_360_);
v___x_363_ = lean_nat_sub(v_endExclusive_362_, v_startInclusive_361_);
lean_dec(v_startInclusive_361_);
lean_dec(v_endExclusive_362_);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_nat_dec_eq(v___x_363_, v___x_364_);
lean_dec(v___x_363_);
if (v___x_365_ == 0)
{
uint8_t v___x_366_; 
v___x_366_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_341_, v___x_342_, v___x_343_, v_it_356_, v___x_354_);
return v___x_366_;
}
else
{
uint8_t v___x_367_; 
lean_dec(v_it_356_);
lean_dec(v___x_343_);
lean_dec_ref(v___x_341_);
v___x_367_ = 0;
return v___x_367_;
}
}
}
}
else
{
lean_dec(v___x_343_);
lean_dec_ref(v___x_341_);
return v_b_345_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object* v___x_391_, lean_object* v___x_392_, lean_object* v___x_393_, lean_object* v_a_394_, lean_object* v_b_395_){
_start:
{
uint8_t v_b_boxed_396_; uint8_t v_res_397_; lean_object* v_r_398_; 
v_b_boxed_396_ = lean_unbox(v_b_395_);
v_res_397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_391_, v___x_392_, v___x_393_, v_a_394_, v_b_boxed_396_);
lean_dec_ref(v___x_392_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object* v_v_401_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v_parts_405_; uint8_t v___x_406_; uint8_t v___x_407_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = lean_string_utf8_byte_size(v_v_401_);
lean_inc_ref_n(v_v_401_, 2);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v_v_401_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set(v___x_404_, 2, v___x_403_);
v_parts_405_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v___x_404_);
v___x_406_ = 1;
lean_inc(v_parts_405_);
v___x_407_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_401_, v___x_404_, v___x_403_, v_parts_405_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_dec(v_parts_405_);
lean_dec_ref_known(v___x_404_, 3);
lean_dec_ref(v_v_401_);
v___x_408_ = lean_box(0);
return v___x_408_;
}
else
{
lean_object* v___x_409_; lean_object* v___x_410_; size_t v_sz_411_; size_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_409_ = ((lean_object*)(l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0));
v___x_410_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v_v_401_, v___x_404_, v___x_403_, v_parts_405_, v___x_409_);
lean_dec_ref_known(v___x_404_, 3);
v_sz_411_ = lean_array_size(v___x_410_);
v___x_412_ = ((size_t)0ULL);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_411_, v___x_412_, v___x_410_);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object* v___x_415_, lean_object* v___x_416_, lean_object* v___x_417_, lean_object* v_inst_418_, lean_object* v_R_419_, lean_object* v_a_420_, uint8_t v_b_421_, lean_object* v_c_422_){
_start:
{
uint8_t v___x_423_; 
v___x_423_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_415_, v___x_416_, v___x_417_, v_a_420_, v_b_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v___x_426_, lean_object* v_inst_427_, lean_object* v_R_428_, lean_object* v_a_429_, lean_object* v_b_430_, lean_object* v_c_431_){
_start:
{
uint8_t v_b_boxed_432_; uint8_t v_res_433_; lean_object* v_r_434_; 
v_b_boxed_432_ = lean_unbox(v_b_430_);
v_res_433_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_424_, v___x_425_, v___x_426_, v_inst_427_, v_R_428_, v_a_429_, v_b_boxed_432_, v_c_431_);
lean_dec_ref(v___x_425_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object* v___x_435_, lean_object* v___x_436_, lean_object* v___x_437_, lean_object* v_inst_438_, lean_object* v_R_439_, lean_object* v_a_440_, lean_object* v_b_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_435_, v___x_436_, v___x_437_, v_a_440_, v_b_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object* v___x_443_, lean_object* v___x_444_, lean_object* v___x_445_, lean_object* v_inst_446_, lean_object* v_R_447_, lean_object* v_a_448_, lean_object* v_b_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_443_, v___x_444_, v___x_445_, v_inst_446_, v_R_447_, v_a_448_, v_b_449_);
lean_dec_ref(v___x_444_);
return v_res_450_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object* v___x_451_, lean_object* v___x_452_, lean_object* v___x_453_, lean_object* v_inst_454_, lean_object* v_R_455_, lean_object* v_a_456_, uint8_t v_b_457_, lean_object* v_c_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_451_, v___x_452_, v___x_453_, v_a_456_, v_b_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v_inst_463_, lean_object* v_R_464_, lean_object* v_a_465_, lean_object* v_b_466_, lean_object* v_c_467_){
_start:
{
uint8_t v_b_boxed_468_; uint8_t v_res_469_; lean_object* v_r_470_; 
v_b_boxed_468_ = lean_unbox(v_b_466_);
v_res_469_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_460_, v___x_461_, v___x_462_, v_inst_463_, v_R_464_, v_a_465_, v_b_boxed_468_, v_c_467_);
lean_dec_ref(v___x_461_);
v_r_470_ = lean_box(v_res_469_);
return v_r_470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object* v___x_471_, lean_object* v___x_472_, lean_object* v___x_473_, lean_object* v_inst_474_, lean_object* v_R_475_, lean_object* v_a_476_, lean_object* v_b_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_471_, v___x_472_, v___x_473_, v_a_476_, v_b_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object* v___x_479_, lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v_inst_482_, lean_object* v_R_483_, lean_object* v_a_484_, lean_object* v_b_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(v___x_479_, v___x_480_, v___x_481_, v_inst_482_, v_R_483_, v_a_484_, v_b_485_);
lean_dec_ref(v___x_480_);
return v_res_486_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqContentLength_beq(lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
uint8_t v___x_489_; 
v___x_489_ = lean_nat_dec_eq(v_x_487_, v_x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqContentLength_beq___boxed(lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
uint8_t v_res_492_; lean_object* v_r_493_; 
v_res_492_ = l_Std_Http_Header_instBEqContentLength_beq(v_x_490_, v_x_491_);
lean_dec(v_x_491_);
lean_dec(v_x_490_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprContentLength_repr_spec__0(lean_object* v_a_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = lean_nat_to_int(v_a_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_unsigned_to_nat(10u);
v___x_512_ = lean_nat_to_int(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0));
v___x_515_ = lean_string_length(v___x_514_);
return v___x_515_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9);
v___x_517_ = lean_nat_to_int(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg(lean_object* v_x_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_523_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6));
v___x_524_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_525_ = l_Nat_reprFast(v_x_522_);
v___x_526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
v___x_527_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_524_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = 0;
v___x_529_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set_uint8(v___x_529_, sizeof(void*)*1, v___x_528_);
v___x_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_523_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_532_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_530_);
v___x_534_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_531_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set_uint8(v___x_537_, sizeof(void*)*1, v___x_528_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr(lean_object* v_x_538_, lean_object* v_prec_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_Http_Header_instReprContentLength_repr___redArg(v_x_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___boxed(lean_object* v_x_541_, lean_object* v_prec_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_Http_Header_instReprContentLength_repr(v_x_541_, v_prec_542_);
lean_dec(v_prec_542_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(lean_object* v_s_546_, lean_object* v_pos_547_){
_start:
{
lean_object* v_str_548_; lean_object* v_startInclusive_549_; lean_object* v_endExclusive_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v_decide_554_; 
v_str_548_ = lean_ctor_get(v_s_546_, 0);
v_startInclusive_549_ = lean_ctor_get(v_s_546_, 1);
v_endExclusive_550_ = lean_ctor_get(v_s_546_, 2);
v___x_551_ = lean_nat_add(v_startInclusive_549_, v_pos_547_);
v___x_552_ = lean_unsigned_to_nat(0u);
v___x_553_ = lean_nat_sub(v_endExclusive_550_, v___x_551_);
v_decide_554_ = lean_nat_dec_eq(v___x_552_, v___x_553_);
lean_dec(v___x_553_);
if (v_decide_554_ == 0)
{
uint32_t v___x_555_; uint32_t v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_string_utf8_get_fast(v_str_548_, v___x_551_);
v___x_556_ = 48;
v___x_557_ = lean_uint32_dec_le(v___x_556_, v___x_555_);
if (v___x_557_ == 0)
{
lean_dec(v___x_551_);
return v_pos_547_;
}
else
{
uint32_t v___x_558_; uint8_t v___x_559_; 
v___x_558_ = 57;
v___x_559_ = lean_uint32_dec_le(v___x_555_, v___x_558_);
if (v___x_559_ == 0)
{
lean_dec(v___x_551_);
return v_pos_547_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_560_ = lean_string_utf8_next_fast(v_str_548_, v___x_551_);
v___x_561_ = lean_nat_sub(v___x_560_, v___x_551_);
lean_dec(v___x_551_);
v___x_562_ = lean_nat_add(v_pos_547_, v___x_561_);
lean_dec(v___x_561_);
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_add(v_pos_547_, v___x_563_);
v___x_565_ = lean_nat_dec_le(v___x_564_, v___x_562_);
lean_dec(v___x_564_);
if (v___x_565_ == 0)
{
lean_dec(v___x_562_);
return v_pos_547_;
}
else
{
lean_dec(v_pos_547_);
v_pos_547_ = v___x_562_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_551_);
return v_pos_547_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0___boxed(lean_object* v_s_567_, lean_object* v_pos_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v_s_567_, v_pos_568_);
lean_dec_ref(v_s_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_parse(lean_object* v_v_570_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_string_utf8_byte_size(v_v_570_);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = lean_nat_dec_eq(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v_decide_576_; 
v___x_574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_574_, 0, v_v_570_);
lean_ctor_set(v___x_574_, 1, v___x_572_);
lean_ctor_set(v___x_574_, 2, v___x_571_);
v___x_575_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v___x_574_, v___x_572_);
v_decide_576_ = lean_nat_dec_eq(v___x_575_, v___x_571_);
lean_dec(v___x_575_);
if (v_decide_576_ == 0)
{
lean_object* v___x_577_; 
lean_dec_ref_known(v___x_574_, 3);
v___x_577_ = lean_box(0);
return v___x_577_;
}
else
{
lean_object* v___x_578_; 
v___x_578_ = l_String_Slice_toNat_x3f(v___x_574_);
lean_dec_ref_known(v___x_574_, 3);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v___x_579_; 
v___x_579_ = lean_box(0);
return v___x_579_;
}
else
{
lean_object* v_val_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
v_val_580_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_578_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_val_580_);
lean_dec(v___x_578_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_val_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
lean_object* v___x_588_; 
lean_dec_ref(v_v_570_);
v___x_588_ = lean_box(0);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_serialize(lean_object* v_h_589_){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_590_ = l_Std_Http_Header_Name_contentLength;
v___x_591_ = l_Nat_reprFast(v_h_589_);
v___x_592_ = l_Std_Http_Header_Value_ofString_x21(v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_590_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
if (lean_obj_tag(v_x_601_) == 0)
{
uint8_t v___x_602_; 
v___x_602_ = 1;
return v___x_602_;
}
else
{
uint8_t v___x_603_; 
v___x_603_ = 0;
return v___x_603_;
}
}
else
{
if (lean_obj_tag(v_x_601_) == 0)
{
uint8_t v___x_604_; 
v___x_604_ = 0;
return v___x_604_;
}
else
{
lean_object* v_val_605_; lean_object* v_val_606_; uint8_t v___x_607_; 
v_val_605_ = lean_ctor_get(v_x_600_, 0);
v_val_606_ = lean_ctor_get(v_x_601_, 0);
v___x_607_ = lean_string_dec_eq(v_val_605_, v_val_606_);
return v___x_607_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_608_, v_x_609_);
lean_dec(v_x_609_);
lean_dec(v_x_608_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object* v_as_613_, size_t v_i_614_, size_t v_stop_615_, lean_object* v_b_616_){
_start:
{
lean_object* v___y_618_; uint8_t v___x_622_; 
v___x_622_ = lean_usize_dec_eq(v_i_614_, v_stop_615_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_623_ = lean_array_uget_borrowed(v_as_613_, v_i_614_);
v___x_624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_625_ = lean_string_dec_eq(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
v___y_618_ = v_b_616_;
goto v___jp_617_;
}
else
{
lean_object* v___x_626_; 
lean_inc(v___x_623_);
v___x_626_ = lean_array_push(v_b_616_, v___x_623_);
v___y_618_ = v___x_626_;
goto v___jp_617_;
}
}
else
{
return v_b_616_;
}
v___jp_617_:
{
size_t v___x_619_; size_t v___x_620_; 
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_add(v_i_614_, v___x_619_);
v_i_614_ = v___x_620_;
v_b_616_ = v___y_618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object* v_as_627_, lean_object* v_i_628_, lean_object* v_stop_629_, lean_object* v_b_630_){
_start:
{
size_t v_i_boxed_631_; size_t v_stop_boxed_632_; lean_object* v_res_633_; 
v_i_boxed_631_ = lean_unbox_usize(v_i_628_);
lean_dec(v_i_628_);
v_stop_boxed_632_ = lean_unbox_usize(v_stop_629_);
lean_dec(v_stop_629_);
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_627_, v_i_boxed_631_, v_stop_boxed_632_, v_b_630_);
lean_dec_ref(v_as_627_);
return v_res_633_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object* v___x_634_, lean_object* v_as_635_, size_t v_i_636_, size_t v_stop_637_){
_start:
{
uint8_t v___x_638_; 
v___x_638_ = lean_usize_dec_eq(v_i_636_, v_stop_637_);
if (v___x_638_ == 0)
{
uint8_t v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_639_ = 1;
v___x_640_ = lean_array_uget_borrowed(v_as_635_, v_i_636_);
lean_inc(v___x_640_);
v___x_641_ = l_Std_Http_Internal_isToken(v___x_640_);
if (v___x_641_ == 0)
{
return v___x_639_;
}
else
{
lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_nat_dec_eq(v___x_634_, v___x_642_);
if (v___x_643_ == 0)
{
size_t v___x_644_; size_t v___x_645_; 
v___x_644_ = ((size_t)1ULL);
v___x_645_ = lean_usize_add(v_i_636_, v___x_644_);
v_i_636_ = v___x_645_;
goto _start;
}
else
{
return v___x_639_;
}
}
}
else
{
uint8_t v___x_647_; 
v___x_647_ = 0;
return v___x_647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object* v___x_648_, lean_object* v_as_649_, lean_object* v_i_650_, lean_object* v_stop_651_){
_start:
{
size_t v_i_boxed_652_; size_t v_stop_boxed_653_; uint8_t v_res_654_; lean_object* v_r_655_; 
v_i_boxed_652_ = lean_unbox_usize(v_i_650_);
lean_dec(v_i_650_);
v_stop_boxed_653_ = lean_unbox_usize(v_stop_651_);
lean_dec(v_stop_651_);
v_res_654_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_648_, v_as_649_, v_i_boxed_652_, v_stop_boxed_653_);
lean_dec_ref(v_as_649_);
lean_dec(v___x_648_);
v_r_655_ = lean_box(v_res_654_);
return v_r_655_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object* v_codings_660_){
_start:
{
uint8_t v___y_662_; uint8_t v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; uint8_t v___y_672_; uint8_t v___y_673_; lean_object* v___y_674_; uint8_t v___y_684_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = lean_array_get_size(v_codings_660_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_dec_eq(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; 
v___x_700_ = lean_nat_dec_lt(v___x_698_, v___x_697_);
if (v___x_700_ == 0)
{
v___y_684_ = v___x_700_;
goto v___jp_683_;
}
else
{
if (v___x_700_ == 0)
{
v___y_684_ = v___x_700_;
goto v___jp_683_;
}
else
{
size_t v___x_701_; size_t v___x_702_; uint8_t v___x_703_; 
v___x_701_ = ((size_t)0ULL);
v___x_702_ = lean_usize_of_nat(v___x_697_);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_697_, v_codings_660_, v___x_701_, v___x_702_);
if (v___x_703_ == 0)
{
v___y_684_ = v___x_703_;
goto v___jp_683_;
}
else
{
return v___x_699_;
}
}
}
}
else
{
uint8_t v___x_704_; 
v___x_704_ = 0;
return v___x_704_;
}
v___jp_661_:
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(1u);
v___x_667_ = lean_nat_dec_lt(v___x_666_, v___y_664_);
if (v___x_667_ == 0)
{
uint8_t v___x_668_; 
v___x_668_ = lean_nat_dec_eq(v___y_664_, v___x_666_);
lean_dec(v___y_664_);
if (v___x_668_ == 0)
{
lean_dec(v___y_665_);
return v___y_662_;
}
else
{
lean_object* v___x_669_; uint8_t v_lastIsChunked_670_; 
v___x_669_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v_lastIsChunked_670_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_665_, v___x_669_);
lean_dec(v___y_665_);
if (v_lastIsChunked_670_ == 0)
{
return v___x_667_;
}
else
{
return v___y_662_;
}
}
}
else
{
lean_dec(v___y_665_);
lean_dec(v___y_664_);
return v___y_663_;
}
}
v___jp_671_:
{
lean_object* v_chunkedCount_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; uint8_t v___x_679_; 
v_chunkedCount_675_ = lean_array_get_size(v___y_674_);
lean_dec_ref(v___y_674_);
v___x_676_ = lean_array_get_size(v_codings_660_);
v___x_677_ = lean_unsigned_to_nat(1u);
v___x_678_ = lean_nat_sub(v___x_676_, v___x_677_);
v___x_679_ = lean_nat_dec_lt(v___x_678_, v___x_676_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
lean_dec(v___x_678_);
v___x_680_ = lean_box(0);
v___y_662_ = v___y_672_;
v___y_663_ = v___y_673_;
v___y_664_ = v_chunkedCount_675_;
v___y_665_ = v___x_680_;
goto v___jp_661_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_array_fget_borrowed(v_codings_660_, v___x_678_);
lean_dec(v___x_678_);
lean_inc(v___x_681_);
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
v___y_662_ = v___y_672_;
v___y_663_ = v___y_673_;
v___y_664_ = v_chunkedCount_675_;
v___y_665_ = v___x_682_;
goto v___jp_661_;
}
}
v___jp_683_:
{
uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_685_ = 1;
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_array_get_size(v_codings_660_);
v___x_688_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__1));
v___x_689_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
if (v___x_689_ == 0)
{
v___y_672_ = v___x_685_;
v___y_673_ = v___y_684_;
v___y_674_ = v___x_688_;
goto v___jp_671_;
}
else
{
uint8_t v___x_690_; 
v___x_690_ = lean_nat_dec_le(v___x_687_, v___x_687_);
if (v___x_690_ == 0)
{
if (v___x_689_ == 0)
{
v___y_672_ = v___x_685_;
v___y_673_ = v___y_684_;
v___y_674_ = v___x_688_;
goto v___jp_671_;
}
else
{
size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_691_ = ((size_t)0ULL);
v___x_692_ = lean_usize_of_nat(v___x_687_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_660_, v___x_691_, v___x_692_, v___x_688_);
v___y_672_ = v___x_685_;
v___y_673_ = v___y_684_;
v___y_674_ = v___x_693_;
goto v___jp_671_;
}
}
else
{
size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((size_t)0ULL);
v___x_695_ = lean_usize_of_nat(v___x_687_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_660_, v___x_694_, v___x_695_, v___x_688_);
v___y_672_ = v___x_685_;
v___y_673_ = v___y_684_;
v___y_674_ = v___x_696_;
goto v___jp_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_Validate___boxed(lean_object* v_codings_705_){
_start:
{
uint8_t v_res_706_; lean_object* v_r_707_; 
v_res_706_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_705_);
lean_dec_ref(v_codings_705_);
v_r_707_ = lean_box(v_res_706_);
return v_r_707_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(lean_object* v___y_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = l_String_quote(v___y_708_);
v___x_710_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_x_713_){
_start:
{
if (lean_obj_tag(v_x_713_) == 0)
{
lean_dec(v_x_711_);
return v_x_712_;
}
else
{
lean_object* v_head_714_; lean_object* v_tail_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_726_; 
v_head_714_ = lean_ctor_get(v_x_713_, 0);
v_tail_715_ = lean_ctor_get(v_x_713_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_x_713_);
if (v_isSharedCheck_726_ == 0)
{
v___x_717_ = v_x_713_;
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_tail_715_);
lean_inc(v_head_714_);
lean_dec(v_x_713_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
lean_inc(v_x_711_);
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 5);
lean_ctor_set(v___x_717_, 1, v_x_711_);
lean_ctor_set(v___x_717_, 0, v_x_712_);
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_x_712_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_x_711_);
v___x_720_ = v_reuseFailAlloc_725_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_721_ = l_String_quote(v_head_714_);
v___x_722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_720_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
v_x_712_ = v___x_723_;
v_x_713_ = v_tail_715_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
if (lean_obj_tag(v_x_729_) == 0)
{
lean_dec(v_x_727_);
return v_x_728_;
}
else
{
lean_object* v_head_730_; lean_object* v_tail_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_742_; 
v_head_730_ = lean_ctor_get(v_x_729_, 0);
v_tail_731_ = lean_ctor_get(v_x_729_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_x_729_);
if (v_isSharedCheck_742_ == 0)
{
v___x_733_ = v_x_729_;
v_isShared_734_ = v_isSharedCheck_742_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_tail_731_);
lean_inc(v_head_730_);
lean_dec(v_x_729_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_742_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
lean_inc(v_x_727_);
if (v_isShared_734_ == 0)
{
lean_ctor_set_tag(v___x_733_, 5);
lean_ctor_set(v___x_733_, 1, v_x_727_);
lean_ctor_set(v___x_733_, 0, v_x_728_);
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_x_728_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_x_727_);
v___x_736_ = v_reuseFailAlloc_741_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_737_ = l_String_quote(v_head_730_);
v___x_738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
v___x_739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_736_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(v_x_727_, v___x_739_, v_tail_731_);
return v___x_740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_743_) == 0)
{
lean_object* v___x_745_; 
lean_dec(v_x_744_);
v___x_745_ = lean_box(0);
return v___x_745_;
}
else
{
lean_object* v_tail_746_; 
v_tail_746_ = lean_ctor_get(v_x_743_, 1);
if (lean_obj_tag(v_tail_746_) == 0)
{
lean_object* v_head_747_; lean_object* v___x_748_; 
lean_dec(v_x_744_);
v_head_747_ = lean_ctor_get(v_x_743_, 0);
lean_inc(v_head_747_);
lean_dec_ref_known(v_x_743_, 2);
v___x_748_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_747_);
return v___x_748_;
}
else
{
lean_object* v_head_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_inc(v_tail_746_);
v_head_749_ = lean_ctor_get(v_x_743_, 0);
lean_inc(v_head_749_);
lean_dec_ref_known(v_x_743_, 2);
v___x_750_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_749_);
v___x_751_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(v_x_744_, v___x_750_, v_tail_746_);
return v___x_751_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0));
v___x_761_ = lean_string_length(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5);
v___x_763_ = lean_nat_to_int(v___x_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(lean_object* v_xs_771_){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_772_ = lean_array_get_size(v_xs_771_);
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_nat_dec_eq(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_775_ = lean_array_to_list(v_xs_771_);
v___x_776_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3));
v___x_777_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(v___x_775_, v___x_776_);
v___x_778_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6);
v___x_779_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7));
v___x_780_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v___x_777_);
v___x_781_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8));
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_778_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = l_Std_Format_fill(v___x_783_);
return v___x_784_;
}
else
{
lean_object* v___x_785_; 
lean_dec_ref(v_xs_771_);
v___x_785_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10));
return v___x_785_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_unsigned_to_nat(11u);
v___x_796_ = lean_nat_to_int(v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg(lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_804_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_805_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3));
v___x_806_ = lean_obj_once(&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4, &l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4);
v___x_807_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_803_);
v___x_808_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = 0;
v___x_810_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set_uint8(v___x_810_, sizeof(void*)*1, v___x_809_);
v___x_811_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_805_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_813_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_box(1);
v___x_815_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6));
v___x_817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v___x_804_);
v___x_819_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_820_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_822_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_823_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_822_);
lean_ctor_set(v___x_823_, 1, v___x_820_);
v___x_824_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_825_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_821_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*1, v___x_809_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr(lean_object* v_x_828_, lean_object* v_prec_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg(v_x_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___boxed(lean_object* v_x_831_, lean_object* v_prec_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_Http_Header_instReprTransferEncoding_repr(v_x_831_, v_prec_832_);
lean_dec(v_prec_832_);
return v_res_833_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object* v_te_836_){
_start:
{
lean_object* v___y_838_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_841_ = lean_array_get_size(v_te_836_);
v___x_842_ = lean_unsigned_to_nat(1u);
v___x_843_ = lean_nat_sub(v___x_841_, v___x_842_);
v___x_844_ = lean_nat_dec_lt(v___x_843_, v___x_841_);
if (v___x_844_ == 0)
{
lean_object* v___x_845_; 
lean_dec(v___x_843_);
v___x_845_ = lean_box(0);
v___y_838_ = v___x_845_;
goto v___jp_837_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_array_fget_borrowed(v_te_836_, v___x_843_);
lean_dec(v___x_843_);
lean_inc(v___x_846_);
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
v___y_838_ = v___x_847_;
goto v___jp_837_;
}
v___jp_837_:
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v___x_840_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_838_, v___x_839_);
lean_dec(v___y_838_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_isChunked___boxed(lean_object* v_te_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_848_);
lean_dec_ref(v_te_848_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object* v_v_851_){
_start:
{
lean_object* v___x_852_; 
v___x_852_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_853_; 
v___x_853_ = lean_box(0);
return v___x_853_;
}
else
{
lean_object* v_val_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_863_; 
v_val_854_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_863_ == 0)
{
v___x_856_ = v___x_852_;
v_isShared_857_ = v_isSharedCheck_863_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_val_854_);
lean_dec(v___x_852_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_863_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
uint8_t v___x_858_; 
v___x_858_ = l_Std_Http_Header_TransferEncoding_Validate(v_val_854_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
lean_del_object(v___x_856_);
lean_dec(v_val_854_);
v___x_859_ = lean_box(0);
return v___x_859_;
}
else
{
lean_object* v___x_861_; 
if (v_isShared_857_ == 0)
{
v___x_861_ = v___x_856_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_val_854_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_serialize(lean_object* v_te_864_){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v_value_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_865_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_866_ = lean_array_to_list(v_te_864_);
v_value_867_ = l_String_intercalate(v___x_865_, v___x_866_);
v___x_868_ = l_Std_Http_Header_Name_transferEncoding;
v___x_869_ = l_Std_Http_Header_Value_ofString_x21(v_value_867_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_868_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___redArg(lean_object* v_x_889_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_890_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_891_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__3));
v___x_892_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_893_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_889_);
v___x_894_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = 0;
v___x_896_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set_uint8(v___x_896_, sizeof(void*)*1, v___x_895_);
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_891_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_box(1);
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_899_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
v___x_902_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__5));
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_890_);
v___x_905_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_908_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_906_);
v___x_910_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_907_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set_uint8(v___x_913_, sizeof(void*)*1, v___x_895_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr(lean_object* v_x_914_, lean_object* v_prec_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Std_Http_Header_instReprConnection_repr___redArg(v_x_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___boxed(lean_object* v_x_917_, lean_object* v_prec_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_Http_Header_instReprConnection_repr(v_x_917_, v_prec_918_);
lean_dec(v_prec_918_);
return v_res_919_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(lean_object* v_token_922_, lean_object* v_as_923_, size_t v_i_924_, size_t v_stop_925_){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = lean_usize_dec_eq(v_i_924_, v_stop_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_927_ = lean_array_uget_borrowed(v_as_923_, v_i_924_);
v___x_928_ = lean_string_dec_eq(v___x_927_, v_token_922_);
if (v___x_928_ == 0)
{
size_t v___x_929_; size_t v___x_930_; 
v___x_929_ = ((size_t)1ULL);
v___x_930_ = lean_usize_add(v_i_924_, v___x_929_);
v_i_924_ = v___x_930_;
goto _start;
}
else
{
return v___x_928_;
}
}
else
{
uint8_t v___x_932_; 
v___x_932_ = 0;
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(lean_object* v_token_933_, lean_object* v_as_934_, lean_object* v_i_935_, lean_object* v_stop_936_){
_start:
{
size_t v_i_boxed_937_; size_t v_stop_boxed_938_; uint8_t v_res_939_; lean_object* v_r_940_; 
v_i_boxed_937_ = lean_unbox_usize(v_i_935_);
lean_dec(v_i_935_);
v_stop_boxed_938_ = lean_unbox_usize(v_stop_936_);
lean_dec(v_stop_936_);
v_res_939_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_933_, v_as_934_, v_i_boxed_937_, v_stop_boxed_938_);
lean_dec_ref(v_as_934_);
lean_dec_ref(v_token_933_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_containsToken(lean_object* v_connection_941_, lean_object* v_token_942_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = lean_array_get_size(v_connection_941_);
v___x_945_ = lean_nat_dec_lt(v___x_943_, v___x_944_);
if (v___x_945_ == 0)
{
lean_dec_ref(v_token_942_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; 
v___x_946_ = lean_string_utf8_byte_size(v_token_942_);
if (v___x_945_ == 0)
{
lean_dec_ref(v_token_942_);
return v___x_945_;
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_token_950_; size_t v___x_951_; size_t v___x_952_; uint8_t v___x_953_; 
v___x_947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_947_, 0, v_token_942_);
lean_ctor_set(v___x_947_, 1, v___x_943_);
lean_ctor_set(v___x_947_, 2, v___x_946_);
v___x_948_ = l_String_Slice_trimAscii(v___x_947_);
v___x_949_ = l_String_Slice_toString(v___x_948_);
lean_dec_ref(v___x_948_);
v_token_950_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_949_, v___x_943_);
v___x_951_ = ((size_t)0ULL);
v___x_952_ = lean_usize_of_nat(v___x_944_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_950_, v_connection_941_, v___x_951_, v___x_952_);
lean_dec_ref(v_token_950_);
return v___x_953_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_containsToken___boxed(lean_object* v_connection_954_, lean_object* v_token_955_){
_start:
{
uint8_t v_res_956_; lean_object* v_r_957_; 
v_res_956_ = l_Std_Http_Header_Connection_containsToken(v_connection_954_, v_token_955_);
lean_dec_ref(v_connection_954_);
v_r_957_ = lean_box(v_res_956_);
return v_r_957_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_shouldClose(lean_object* v_connection_959_){
_start:
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = ((lean_object*)(l_Std_Http_Header_Connection_shouldClose___closed__0));
v___x_961_ = l_Std_Http_Header_Connection_containsToken(v_connection_959_, v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_shouldClose___boxed(lean_object* v_connection_962_){
_start:
{
uint8_t v_res_963_; lean_object* v_r_964_; 
v_res_963_ = l_Std_Http_Header_Connection_shouldClose(v_connection_962_);
lean_dec_ref(v_connection_962_);
v_r_964_ = lean_box(v_res_963_);
return v_r_964_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(lean_object* v_as_965_, size_t v_i_966_, size_t v_stop_967_){
_start:
{
uint8_t v___x_968_; 
v___x_968_ = lean_usize_dec_eq(v_i_966_, v_stop_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = lean_array_uget_borrowed(v_as_965_, v_i_966_);
lean_inc(v___x_969_);
v___x_970_ = l_Std_Http_Internal_isToken(v___x_969_);
if (v___x_970_ == 0)
{
uint8_t v___x_971_; 
v___x_971_ = 1;
return v___x_971_;
}
else
{
size_t v___x_972_; size_t v___x_973_; 
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_966_, v___x_972_);
v_i_966_ = v___x_973_;
goto _start;
}
}
else
{
uint8_t v___x_975_; 
v___x_975_ = 0;
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(lean_object* v_as_976_, lean_object* v_i_977_, lean_object* v_stop_978_){
_start:
{
size_t v_i_boxed_979_; size_t v_stop_boxed_980_; uint8_t v_res_981_; lean_object* v_r_982_; 
v_i_boxed_979_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_stop_boxed_980_ = lean_unbox_usize(v_stop_978_);
lean_dec(v_stop_978_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_976_, v_i_boxed_979_, v_stop_boxed_980_);
lean_dec_ref(v_as_976_);
v_r_982_ = lean_box(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_parse(lean_object* v_v_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_983_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_box(0);
return v___x_985_;
}
else
{
lean_object* v_val_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1006_; 
v_val_986_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_988_ = v___x_984_;
v_isShared_989_ = v_isSharedCheck_1006_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_val_986_);
lean_dec(v___x_984_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1006_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_array_get_size(v_val_986_);
v___x_992_ = lean_nat_dec_lt(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_994_; 
if (v_isShared_989_ == 0)
{
v___x_994_ = v___x_988_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_val_986_);
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
if (v___x_992_ == 0)
{
lean_object* v___x_997_; 
if (v_isShared_989_ == 0)
{
v___x_997_ = v___x_988_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_val_986_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
else
{
size_t v___x_999_; size_t v___x_1000_; uint8_t v___x_1001_; 
v___x_999_ = ((size_t)0ULL);
v___x_1000_ = lean_usize_of_nat(v___x_991_);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_val_986_, v___x_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1003_; 
if (v_isShared_989_ == 0)
{
v___x_1003_ = v___x_988_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_val_986_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
else
{
lean_object* v___x_1005_; 
lean_del_object(v___x_988_);
lean_dec(v_val_986_);
v___x_1005_ = lean_box(0);
return v___x_1005_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_serialize(lean_object* v_connection_1007_){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_value_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1008_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_1009_ = lean_array_to_list(v_connection_1007_);
v_value_1010_ = l_String_intercalate(v___x_1008_, v___x_1009_);
v___x_1011_ = l_Std_Http_Header_Name_connection;
v___x_1012_ = l_Std_Http_Header_Value_ofString_x21(v_value_1010_);
v___x_1013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_unsigned_to_nat(8u);
v___x_1030_ = lean_nat_to_int(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_unsigned_to_nat(2u);
v___x_1032_ = lean_nat_to_int(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___redArg(lean_object* v_x_1040_){
_start:
{
lean_object* v_host_1041_; lean_object* v_port_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1116_; 
v_host_1041_ = lean_ctor_get(v_x_1040_, 0);
v_port_1042_ = lean_ctor_get(v_x_1040_, 1);
v_isSharedCheck_1116_ = !lean_is_exclusive(v_x_1040_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1044_ = v_x_1040_;
v_isShared_1045_ = v_isSharedCheck_1116_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_port_1042_);
lean_inc(v_host_1041_);
lean_dec(v_x_1040_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1116_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_ctr_1052_; lean_object* v_a_1053_; 
v___x_1046_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_1047_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__3));
v___x_1048_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__4, &l_Std_Http_Header_instReprHost_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4);
v___x_1049_ = lean_unsigned_to_nat(0u);
v___x_1050_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__5, &l_Std_Http_Header_instReprHost_repr___redArg___closed__5_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5);
switch(lean_obj_tag(v_host_1041_))
{
case 0:
{
lean_object* v_name_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1095_; 
v_name_1086_ = lean_ctor_get(v_host_1041_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v_host_1041_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1088_ = v_host_1041_;
v_isShared_1089_ = v_isSharedCheck_1095_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_name_1086_);
lean_dec(v_host_1041_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1095_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1090_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__9));
v___x_1091_ = l_String_quote(v_name_1086_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 3);
lean_ctor_set(v___x_1088_, 0, v___x_1091_);
v___x_1093_ = v___x_1088_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
v_ctr_1052_ = v___x_1090_;
v_a_1053_ = v___x_1093_;
goto v___jp_1051_;
}
}
}
case 1:
{
lean_object* v_ipv4_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1105_; 
v_ipv4_1096_ = lean_ctor_get(v_host_1041_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_host_1041_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1098_ = v_host_1041_;
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_ipv4_1096_);
lean_dec(v_host_1041_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1100_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__10));
v___x_1101_ = lean_uv_ntop_v4(v_ipv4_1096_);
lean_dec_ref(v_ipv4_1096_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set_tag(v___x_1098_, 3);
lean_ctor_set(v___x_1098_, 0, v___x_1101_);
v___x_1103_ = v___x_1098_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
v_ctr_1052_ = v___x_1100_;
v_a_1053_ = v___x_1103_;
goto v___jp_1051_;
}
}
}
default: 
{
lean_object* v_ipv6_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1115_; 
v_ipv6_1106_ = lean_ctor_get(v_host_1041_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_host_1041_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1108_ = v_host_1041_;
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_ipv6_1106_);
lean_dec(v_host_1041_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1110_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__11));
v___x_1111_ = lean_uv_ntop_v6(v_ipv6_1106_);
lean_dec_ref(v_ipv6_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set_tag(v___x_1108_, 3);
lean_ctor_set(v___x_1108_, 0, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
v_ctr_1052_ = v___x_1110_;
v_a_1053_ = v___x_1113_;
goto v___jp_1051_;
}
}
}
}
v___jp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1054_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__6));
v___x_1055_ = lean_string_append(v___x_1054_, v_ctr_1052_);
v___x_1056_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
v___x_1057_ = lean_box(1);
if (v_isShared_1045_ == 0)
{
lean_ctor_set_tag(v___x_1044_, 5);
lean_ctor_set(v___x_1044_, 1, v___x_1057_);
lean_ctor_set(v___x_1044_, 0, v___x_1056_);
v___x_1059_ = v___x_1044_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v_a_1053_);
v___x_1061_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1050_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = 0;
v___x_1063_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1063_, 0, v___x_1061_);
lean_ctor_set_uint8(v___x_1063_, sizeof(void*)*1, v___x_1062_);
v___x_1064_ = l_Repr_addAppParen(v___x_1063_, v___x_1049_);
v___x_1065_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1048_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set_uint8(v___x_1066_, sizeof(void*)*1, v___x_1062_);
v___x_1067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1047_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_1069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___x_1057_);
v___x_1071_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__8));
v___x_1072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1046_);
v___x_1074_ = l_Std_Http_URI_instReprPort_repr(v_port_1042_, v___x_1049_);
lean_dec(v_port_1042_);
v___x_1075_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1048_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*1, v___x_1062_);
v___x_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1073_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1079_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_1077_);
v___x_1081_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_1082_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1078_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*1, v___x_1062_);
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr(lean_object* v_x_1117_, lean_object* v_prec_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Std_Http_Header_instReprHost_repr___redArg(v_x_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___boxed(lean_object* v_x_1120_, lean_object* v_prec_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Std_Http_Header_instReprHost_repr(v_x_1120_, v_prec_1121_);
lean_dec(v_prec_1121_);
return v_res_1122_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqHost_beq(lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v_host_1127_; lean_object* v_port_1128_; lean_object* v_host_1129_; lean_object* v_port_1130_; uint8_t v___x_1131_; 
v_host_1127_ = lean_ctor_get(v_x_1125_, 0);
v_port_1128_ = lean_ctor_get(v_x_1125_, 1);
v_host_1129_ = lean_ctor_get(v_x_1126_, 0);
v_port_1130_ = lean_ctor_get(v_x_1126_, 1);
v___x_1131_ = l_Std_Http_URI_instBEqHost_beq(v_host_1127_, v_host_1129_);
if (v___x_1131_ == 0)
{
return v___x_1131_;
}
else
{
uint8_t v___x_1132_; 
v___x_1132_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1128_, v_port_1130_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqHost_beq___boxed(lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
uint8_t v_res_1135_; lean_object* v_r_1136_; 
v_res_1135_ = l_Std_Http_Header_instBEqHost_beq(v_x_1133_, v_x_1134_);
lean_dec_ref(v_x_1134_);
lean_dec_ref(v_x_1133_);
v_r_1136_ = lean_box(v_res_1135_);
return v_r_1136_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0(lean_object* v___x_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_Http_URI_Parser_parseHostHeader(v___x_1142_, v___y_1143_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_pos_1145_; lean_object* v_array_1146_; lean_object* v_idx_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_pos_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_pos_1145_);
v_array_1146_ = lean_ctor_get(v_pos_1145_, 0);
v_idx_1147_ = lean_ctor_get(v_pos_1145_, 1);
v___x_1148_ = lean_byte_array_size(v_array_1146_);
v___x_1149_ = lean_nat_dec_lt(v_idx_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_dec(v_pos_1145_);
return v___x_1144_;
}
else
{
lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1157_; 
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1157_ == 0)
{
lean_object* v_unused_1158_; lean_object* v_unused_1159_; 
v_unused_1158_ = lean_ctor_get(v___x_1144_, 1);
lean_dec(v_unused_1158_);
v_unused_1159_ = lean_ctor_get(v___x_1144_, 0);
lean_dec(v_unused_1159_);
v___x_1151_ = v___x_1144_;
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
else
{
lean_dec(v___x_1144_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = ((lean_object*)(l_Std_Http_Header_Host_parse___lam__0___closed__1));
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 1);
lean_ctor_set(v___x_1151_, 1, v___x_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_pos_1145_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
else
{
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0___boxed(lean_object* v___x_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_Http_Header_Host_parse___lam__0(v___x_1160_, v___y_1161_);
lean_dec_ref(v___x_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse(lean_object* v_v_1173_){
_start:
{
lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v_parsed_1176_; 
v___f_1174_ = ((lean_object*)(l_Std_Http_Header_Host_parse___closed__1));
v___x_1175_ = lean_string_to_utf8(v_v_1173_);
v_parsed_1176_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1174_, v___x_1175_);
if (lean_obj_tag(v_parsed_1176_) == 0)
{
lean_object* v___x_1177_; 
lean_dec_ref_known(v_parsed_1176_, 1);
v___x_1177_ = lean_box(0);
return v___x_1177_;
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1194_; 
v_a_1178_ = lean_ctor_get(v_parsed_1176_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_parsed_1176_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1180_ = v_parsed_1176_;
v_isShared_1181_ = v_isSharedCheck_1194_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v_parsed_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1194_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1193_; 
v_fst_1182_ = lean_ctor_get(v_a_1178_, 0);
v_snd_1183_ = lean_ctor_get(v_a_1178_, 1);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_a_1178_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1185_ = v_a_1178_;
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snd_1183_);
lean_inc(v_fst_1182_);
lean_dec(v_a_1178_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1193_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_fst_1182_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_snd_1183_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1188_);
v___x_1190_ = v___x_1180_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1188_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___boxed(lean_object* v_v_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Std_Http_Header_Host_parse(v_v_1195_);
lean_dec_ref(v_v_1195_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_serialize(lean_object* v_host_1199_){
_start:
{
lean_object* v___y_1201_; lean_object* v___y_1205_; lean_object* v_port_1209_; 
v_port_1209_ = lean_ctor_get(v_host_1199_, 1);
switch(lean_obj_tag(v_port_1209_))
{
case 0:
{
lean_object* v_host_1210_; 
v_host_1210_ = lean_ctor_get(v_host_1199_, 0);
lean_inc_ref(v_host_1210_);
lean_dec_ref(v_host_1199_);
switch(lean_obj_tag(v_host_1210_))
{
case 0:
{
lean_object* v_name_1211_; lean_object* v___x_1212_; 
v_name_1211_ = lean_ctor_get(v_host_1210_, 0);
lean_inc_ref(v_name_1211_);
lean_dec_ref_known(v_host_1210_, 1);
v___x_1212_ = l_Std_Http_Header_Value_ofString_x21(v_name_1211_);
v___y_1201_ = v___x_1212_;
goto v___jp_1200_;
}
case 1:
{
lean_object* v_ipv4_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_ipv4_1213_ = lean_ctor_get(v_host_1210_, 0);
lean_inc_ref(v_ipv4_1213_);
lean_dec_ref_known(v_host_1210_, 1);
v___x_1214_ = lean_uv_ntop_v4(v_ipv4_1213_);
lean_dec_ref(v_ipv4_1213_);
v___x_1215_ = l_Std_Http_Header_Value_ofString_x21(v___x_1214_);
v___y_1201_ = v___x_1215_;
goto v___jp_1200_;
}
default: 
{
lean_object* v_ipv6_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_ipv6_1216_ = lean_ctor_get(v_host_1210_, 0);
lean_inc_ref(v_ipv6_1216_);
lean_dec_ref_known(v_host_1210_, 1);
v___x_1217_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1218_ = lean_uv_ntop_v6(v_ipv6_1216_);
lean_dec_ref(v_ipv6_1216_);
v___x_1219_ = lean_string_append(v___x_1217_, v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1221_ = lean_string_append(v___x_1219_, v___x_1220_);
v___x_1222_ = l_Std_Http_Header_Value_ofString_x21(v___x_1221_);
v___y_1201_ = v___x_1222_;
goto v___jp_1200_;
}
}
}
case 1:
{
lean_object* v_host_1223_; 
v_host_1223_ = lean_ctor_get(v_host_1199_, 0);
lean_inc_ref(v_host_1223_);
lean_dec_ref(v_host_1199_);
switch(lean_obj_tag(v_host_1223_))
{
case 0:
{
lean_object* v_name_1224_; 
v_name_1224_ = lean_ctor_get(v_host_1223_, 0);
lean_inc_ref(v_name_1224_);
lean_dec_ref_known(v_host_1223_, 1);
v___y_1205_ = v_name_1224_;
goto v___jp_1204_;
}
case 1:
{
lean_object* v_ipv4_1225_; lean_object* v___x_1226_; 
v_ipv4_1225_ = lean_ctor_get(v_host_1223_, 0);
lean_inc_ref(v_ipv4_1225_);
lean_dec_ref_known(v_host_1223_, 1);
v___x_1226_ = lean_uv_ntop_v4(v_ipv4_1225_);
lean_dec_ref(v_ipv4_1225_);
v___y_1205_ = v___x_1226_;
goto v___jp_1204_;
}
default: 
{
lean_object* v_ipv6_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_ipv6_1227_ = lean_ctor_get(v_host_1223_, 0);
lean_inc_ref(v_ipv6_1227_);
lean_dec_ref_known(v_host_1223_, 1);
v___x_1228_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1229_ = lean_uv_ntop_v6(v_ipv6_1227_);
lean_dec_ref(v_ipv6_1227_);
v___x_1230_ = lean_string_append(v___x_1228_, v___x_1229_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1232_ = lean_string_append(v___x_1230_, v___x_1231_);
v___y_1205_ = v___x_1232_;
goto v___jp_1204_;
}
}
}
default: 
{
lean_object* v_host_1233_; uint16_t v_port_1234_; lean_object* v___y_1236_; 
lean_inc_ref(v_port_1209_);
v_host_1233_ = lean_ctor_get(v_host_1199_, 0);
lean_inc_ref(v_host_1233_);
lean_dec_ref(v_host_1199_);
v_port_1234_ = lean_ctor_get_uint16(v_port_1209_, 0);
lean_dec_ref_known(v_port_1209_, 0);
switch(lean_obj_tag(v_host_1233_))
{
case 0:
{
lean_object* v_name_1243_; 
v_name_1243_ = lean_ctor_get(v_host_1233_, 0);
lean_inc_ref(v_name_1243_);
lean_dec_ref_known(v_host_1233_, 1);
v___y_1236_ = v_name_1243_;
goto v___jp_1235_;
}
case 1:
{
lean_object* v_ipv4_1244_; lean_object* v___x_1245_; 
v_ipv4_1244_ = lean_ctor_get(v_host_1233_, 0);
lean_inc_ref(v_ipv4_1244_);
lean_dec_ref_known(v_host_1233_, 1);
v___x_1245_ = lean_uv_ntop_v4(v_ipv4_1244_);
lean_dec_ref(v_ipv4_1244_);
v___y_1236_ = v___x_1245_;
goto v___jp_1235_;
}
default: 
{
lean_object* v_ipv6_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v_ipv6_1246_ = lean_ctor_get(v_host_1233_, 0);
lean_inc_ref(v_ipv6_1246_);
lean_dec_ref_known(v_host_1233_, 1);
v___x_1247_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1248_ = lean_uv_ntop_v6(v_ipv6_1246_);
lean_dec_ref(v_ipv6_1246_);
v___x_1249_ = lean_string_append(v___x_1247_, v___x_1248_);
lean_dec_ref(v___x_1248_);
v___x_1250_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1251_ = lean_string_append(v___x_1249_, v___x_1250_);
v___y_1236_ = v___x_1251_;
goto v___jp_1235_;
}
}
v___jp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1237_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1238_ = lean_string_append(v___y_1236_, v___x_1237_);
v___x_1239_ = lean_uint16_to_nat(v_port_1234_);
v___x_1240_ = l_Nat_reprFast(v___x_1239_);
v___x_1241_ = lean_string_append(v___x_1238_, v___x_1240_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = l_Std_Http_Header_Value_ofString_x21(v___x_1241_);
v___y_1201_ = v___x_1242_;
goto v___jp_1200_;
}
}
}
v___jp_1200_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__0));
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1202_);
lean_ctor_set(v___x_1203_, 1, v___y_1201_);
return v___x_1203_;
}
v___jp_1204_:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1207_ = lean_string_append(v___y_1205_, v___x_1206_);
v___x_1208_ = l_Std_Http_Header_Value_ofString_x21(v___x_1207_);
v___y_1201_ = v___x_1208_;
goto v___jp_1200_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___closed__2(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = ((lean_object*)(l_Std_Http_Header_instReprExpect_repr___closed__1));
v___x_1265_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1266_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___x_1264_);
return v___x_1266_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___closed__3(void){
_start:
{
uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = 0;
v___x_1268_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___closed__2, &l_Std_Http_Header_instReprExpect_repr___closed__2_once, _init_l_Std_Http_Header_instReprExpect_repr___closed__2);
v___x_1269_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set_uint8(v___x_1269_, sizeof(void*)*1, v___x_1267_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr(lean_object* v_x_1270_, lean_object* v_prec_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___closed__3, &l_Std_Http_Header_instReprExpect_repr___closed__3_once, _init_l_Std_Http_Header_instReprExpect_repr___closed__3);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___boxed(lean_object* v_x_1273_, lean_object* v_prec_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Std_Http_Header_instReprExpect_repr(v_x_1273_, v_prec_1274_);
lean_dec(v_prec_1274_);
return v_res_1275_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq(lean_object* v_x_1278_, lean_object* v_y_1279_){
_start:
{
uint8_t v___x_1280_; 
v___x_1280_ = 1;
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___boxed(lean_object* v_x_1281_, lean_object* v_y_1282_){
_start:
{
uint8_t v_res_1283_; lean_object* v_r_1284_; 
v_res_1283_ = l_Std_Http_Header_instBEqExpect_beq(v_x_1281_, v_y_1282_);
v_r_1284_ = lean_box(v_res_1283_);
return v_r_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_parse(lean_object* v_v_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v_normalized_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_string_utf8_byte_size(v_v_1290_);
v___x_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1293_, 0, v_v_1290_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
lean_ctor_set(v___x_1293_, 2, v___x_1292_);
v___x_1294_ = l_String_Slice_trimAscii(v___x_1293_);
v___x_1295_ = l_String_Slice_toString(v___x_1294_);
lean_dec_ref(v___x_1294_);
v_normalized_1296_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_1295_, v___x_1291_);
v___x_1297_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1298_ = lean_string_dec_eq(v_normalized_1296_, v___x_1297_);
lean_dec_ref(v_normalized_1296_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_box(0);
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; 
v___x_1300_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__1));
return v___x_1300_;
}
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___closed__0(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1302_ = l_Std_Http_Header_Value_ofString_x21(v___x_1301_);
return v___x_1302_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___closed__1(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___closed__0, &l_Std_Http_Header_Expect_serialize___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___closed__0);
v___x_1304_ = l_Std_Http_Header_Name_expect;
v___x_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1304_);
lean_ctor_set(v___x_1305_, 1, v___x_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize(lean_object* v_x_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___closed__1, &l_Std_Http_Header_Expect_serialize___closed__1_once, _init_l_Std_Http_Header_Expect_serialize___closed__1);
return v___x_1307_;
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

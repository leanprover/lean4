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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_toCtorIdx(lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(lean_object* v_s_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0));
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(lean_object* v_s_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v_s_139_);
lean_dec_ref(v_s_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(lean_object* v_s_141_, lean_object* v_p_142_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t v_sz_158_, size_t v_i_159_, lean_object* v_bs_160_){
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
v___x_166_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_165_, v___x_163_);
v___x_167_ = ((size_t)1ULL);
v___x_168_ = lean_usize_add(v_i_159_, v___x_167_);
v___x_169_ = lean_array_uset(v_bs_x27_164_, v_i_159_, v___x_166_);
v_i_159_ = v___x_168_;
v_bs_160_ = v___x_169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(lean_object* v_sz_171_, lean_object* v_i_172_, lean_object* v_bs_173_){
_start:
{
size_t v_sz_boxed_174_; size_t v_i_boxed_175_; lean_object* v_res_176_; 
v_sz_boxed_174_ = lean_unbox_usize(v_sz_171_);
lean_dec(v_sz_171_);
v_i_boxed_175_ = lean_unbox_usize(v_i_172_);
lean_dec(v_i_172_);
v_res_176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_boxed_174_, v_i_boxed_175_, v_bs_173_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(lean_object* v___x_177_, lean_object* v___x_178_, lean_object* v___x_179_, lean_object* v_a_180_, lean_object* v_b_181_){
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(lean_object* v___x_221_, lean_object* v___x_222_, lean_object* v___x_223_, lean_object* v_a_224_, lean_object* v_b_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_221_, v___x_222_, v___x_223_, v_a_224_, v_b_225_);
lean_dec_ref(v___x_222_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(lean_object* v___x_227_, lean_object* v___x_228_, lean_object* v___x_229_, lean_object* v_a_230_, lean_object* v_b_231_){
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
v___x_258_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_227_, v___x_228_, v___x_229_, v___x_257_, v_b_231_);
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
v___x_239_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_227_, v___x_228_, v___x_229_, v_it_233_, v___x_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(lean_object* v___x_271_, lean_object* v___x_272_, lean_object* v___x_273_, lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_271_, v___x_272_, v___x_273_, v_a_274_, v_b_275_);
lean_dec_ref(v___x_272_);
return v_res_276_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object* v___x_277_, lean_object* v___x_278_, lean_object* v___x_279_, lean_object* v_a_280_, uint8_t v_b_281_){
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object* v___x_327_, lean_object* v___x_328_, lean_object* v___x_329_, lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
uint8_t v_b_boxed_332_; uint8_t v_res_333_; lean_object* v_r_334_; 
v_b_boxed_332_ = lean_unbox(v_b_331_);
v_res_333_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_327_, v___x_328_, v___x_329_, v_a_330_, v_b_boxed_332_);
lean_dec_ref(v___x_328_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object* v___x_335_, lean_object* v___x_336_, lean_object* v___x_337_, lean_object* v_a_338_, uint8_t v_b_339_){
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
v___x_372_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_335_, v___x_336_, v___x_337_, v___x_371_, v_b_339_);
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
v___x_360_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_335_, v___x_336_, v___x_337_, v_it_350_, v___x_348_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v___x_387_, lean_object* v_a_388_, lean_object* v_b_389_){
_start:
{
uint8_t v_b_boxed_390_; uint8_t v_res_391_; lean_object* v_r_392_; 
v_b_boxed_390_ = lean_unbox(v_b_389_);
v_res_391_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_385_, v___x_386_, v___x_387_, v_a_388_, v_b_boxed_390_);
lean_dec_ref(v___x_386_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object* v_v_395_){
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
v_parts_399_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v___x_398_);
v___x_400_ = 1;
lean_inc(v_parts_399_);
v___x_401_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_395_, v___x_398_, v___x_397_, v_parts_399_, v___x_400_);
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
v___x_403_ = ((lean_object*)(l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0));
v___x_404_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v_v_395_, v___x_398_, v___x_397_, v_parts_399_, v___x_403_);
lean_dec_ref(v___x_398_);
v_sz_405_ = lean_array_size(v___x_404_);
v___x_406_ = ((size_t)0ULL);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_405_, v___x_406_, v___x_404_);
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
return v___x_408_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object* v___x_409_, lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v_inst_412_, lean_object* v_R_413_, lean_object* v_a_414_, uint8_t v_b_415_, lean_object* v_c_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_409_, v___x_410_, v___x_411_, v_a_414_, v_b_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v_inst_421_, lean_object* v_R_422_, lean_object* v_a_423_, lean_object* v_b_424_, lean_object* v_c_425_){
_start:
{
uint8_t v_b_boxed_426_; uint8_t v_res_427_; lean_object* v_r_428_; 
v_b_boxed_426_ = lean_unbox(v_b_424_);
v_res_427_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_418_, v___x_419_, v___x_420_, v_inst_421_, v_R_422_, v_a_423_, v_b_boxed_426_, v_c_425_);
lean_dec_ref(v___x_419_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object* v___x_429_, lean_object* v___x_430_, lean_object* v___x_431_, lean_object* v_inst_432_, lean_object* v_R_433_, lean_object* v_a_434_, lean_object* v_b_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_429_, v___x_430_, v___x_431_, v_a_434_, v_b_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object* v___x_437_, lean_object* v___x_438_, lean_object* v___x_439_, lean_object* v_inst_440_, lean_object* v_R_441_, lean_object* v_a_442_, lean_object* v_b_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_437_, v___x_438_, v___x_439_, v_inst_440_, v_R_441_, v_a_442_, v_b_443_);
lean_dec_ref(v___x_438_);
return v_res_444_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object* v___x_445_, lean_object* v___x_446_, lean_object* v___x_447_, lean_object* v_inst_448_, lean_object* v_R_449_, lean_object* v_a_450_, uint8_t v_b_451_, lean_object* v_c_452_){
_start:
{
uint8_t v___x_453_; 
v___x_453_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_445_, v___x_446_, v___x_447_, v_a_450_, v_b_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object* v___x_454_, lean_object* v___x_455_, lean_object* v___x_456_, lean_object* v_inst_457_, lean_object* v_R_458_, lean_object* v_a_459_, lean_object* v_b_460_, lean_object* v_c_461_){
_start:
{
uint8_t v_b_boxed_462_; uint8_t v_res_463_; lean_object* v_r_464_; 
v_b_boxed_462_ = lean_unbox(v_b_460_);
v_res_463_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_454_, v___x_455_, v___x_456_, v_inst_457_, v_R_458_, v_a_459_, v_b_boxed_462_, v_c_461_);
lean_dec_ref(v___x_455_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object* v___x_465_, lean_object* v___x_466_, lean_object* v___x_467_, lean_object* v_inst_468_, lean_object* v_R_469_, lean_object* v_a_470_, lean_object* v_b_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_465_, v___x_466_, v___x_467_, v_a_470_, v_b_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object* v___x_473_, lean_object* v___x_474_, lean_object* v___x_475_, lean_object* v_inst_476_, lean_object* v_R_477_, lean_object* v_a_478_, lean_object* v_b_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(v___x_473_, v___x_474_, v___x_475_, v_inst_476_, v_R_477_, v_a_478_, v_b_479_);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(lean_object* v_s_540_, lean_object* v_pos_541_){
_start:
{
lean_object* v_str_542_; lean_object* v_startInclusive_543_; lean_object* v_endExclusive_544_; lean_object* v___x_545_; uint8_t v___y_547_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_str_542_ = lean_ctor_get(v_s_540_, 0);
v_startInclusive_543_ = lean_ctor_get(v_s_540_, 1);
v_endExclusive_544_ = lean_ctor_get(v_s_540_, 2);
v___x_545_ = lean_nat_add(v_startInclusive_543_, v_pos_541_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_nat_sub(v_endExclusive_544_, v___x_545_);
v___x_555_ = lean_nat_dec_eq(v___x_553_, v___x_554_);
lean_dec(v___x_554_);
if (v___x_555_ == 0)
{
uint32_t v___x_556_; uint32_t v___x_557_; uint8_t v___x_558_; 
v___x_556_ = lean_string_utf8_get_fast(v_str_542_, v___x_545_);
v___x_557_ = 48;
v___x_558_ = lean_uint32_dec_le(v___x_557_, v___x_556_);
if (v___x_558_ == 0)
{
v___y_547_ = v___x_558_;
goto v___jp_546_;
}
else
{
uint32_t v___x_559_; uint8_t v___x_560_; 
v___x_559_ = 57;
v___x_560_ = lean_uint32_dec_le(v___x_556_, v___x_559_);
v___y_547_ = v___x_560_;
goto v___jp_546_;
}
}
else
{
lean_dec(v___x_545_);
return v_pos_541_;
}
v___jp_546_:
{
if (v___y_547_ == 0)
{
lean_dec(v___x_545_);
return v_pos_541_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_548_ = lean_string_utf8_next_fast(v_str_542_, v___x_545_);
v___x_549_ = lean_nat_sub(v___x_548_, v___x_545_);
lean_dec(v___x_545_);
v___x_550_ = lean_nat_add(v_pos_541_, v___x_549_);
lean_dec(v___x_549_);
v___x_551_ = lean_nat_dec_lt(v_pos_541_, v___x_550_);
if (v___x_551_ == 0)
{
lean_dec(v___x_550_);
return v_pos_541_;
}
else
{
lean_dec(v_pos_541_);
v_pos_541_ = v___x_550_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0___boxed(lean_object* v_s_561_, lean_object* v_pos_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v_s_561_, v_pos_562_);
lean_dec_ref(v_s_561_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_parse(lean_object* v_v_564_){
_start:
{
uint8_t v___y_566_; lean_object* v___x_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v___x_581_ = lean_string_utf8_byte_size(v_v_564_);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_nat_dec_eq(v___x_581_, v___x_582_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
lean_inc_ref(v_v_564_);
v___x_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_584_, 0, v_v_564_);
lean_ctor_set(v___x_584_, 1, v___x_582_);
lean_ctor_set(v___x_584_, 2, v___x_581_);
v___x_585_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v___x_584_, v___x_582_);
lean_dec_ref(v___x_584_);
v___x_586_ = lean_nat_dec_eq(v___x_585_, v___x_581_);
lean_dec(v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
lean_dec_ref(v_v_564_);
v___x_587_ = lean_box(0);
return v___x_587_;
}
else
{
v___y_566_ = v___x_583_;
goto v___jp_565_;
}
}
else
{
v___y_566_ = v___x_583_;
goto v___jp_565_;
}
v___jp_565_:
{
if (v___y_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_string_utf8_byte_size(v_v_564_);
v___x_569_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_569_, 0, v_v_564_);
lean_ctor_set(v___x_569_, 1, v___x_567_);
lean_ctor_set(v___x_569_, 2, v___x_568_);
v___x_570_ = l_String_Slice_toNat_x3f(v___x_569_);
lean_dec_ref(v___x_569_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v___x_571_; 
v___x_571_ = lean_box(0);
return v___x_571_;
}
else
{
lean_object* v_val_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
v_val_572_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_570_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_val_572_);
lean_dec(v___x_570_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_val_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
else
{
lean_object* v___x_580_; 
lean_dec_ref(v_v_564_);
v___x_580_ = lean_box(0);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_serialize(lean_object* v_h_588_){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_589_ = l_Std_Http_Header_Name_contentLength;
v___x_590_ = l_Nat_reprFast(v_h_588_);
v___x_591_ = l_Std_Http_Header_Value_ofString_x21(v___x_590_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_589_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_599_) == 0)
{
if (lean_obj_tag(v_x_600_) == 0)
{
uint8_t v___x_601_; 
v___x_601_ = 1;
return v___x_601_;
}
else
{
uint8_t v___x_602_; 
v___x_602_ = 0;
return v___x_602_;
}
}
else
{
if (lean_obj_tag(v_x_600_) == 0)
{
uint8_t v___x_603_; 
v___x_603_ = 0;
return v___x_603_;
}
else
{
lean_object* v_val_604_; lean_object* v_val_605_; uint8_t v___x_606_; 
v_val_604_ = lean_ctor_get(v_x_599_, 0);
v_val_605_ = lean_ctor_get(v_x_600_, 0);
v___x_606_ = lean_string_dec_eq(v_val_604_, v_val_605_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
uint8_t v_res_609_; lean_object* v_r_610_; 
v_res_609_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_607_, v_x_608_);
lean_dec(v_x_608_);
lean_dec(v_x_607_);
v_r_610_ = lean_box(v_res_609_);
return v_r_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object* v_as_612_, size_t v_i_613_, size_t v_stop_614_, lean_object* v_b_615_){
_start:
{
lean_object* v___y_617_; uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_eq(v_i_613_, v_stop_614_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_array_uget_borrowed(v_as_612_, v_i_613_);
v___x_623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_624_ = lean_string_dec_eq(v___x_622_, v___x_623_);
if (v___x_624_ == 0)
{
v___y_617_ = v_b_615_;
goto v___jp_616_;
}
else
{
lean_object* v___x_625_; 
lean_inc(v___x_622_);
v___x_625_ = lean_array_push(v_b_615_, v___x_622_);
v___y_617_ = v___x_625_;
goto v___jp_616_;
}
}
else
{
return v_b_615_;
}
v___jp_616_:
{
size_t v___x_618_; size_t v___x_619_; 
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_add(v_i_613_, v___x_618_);
v_i_613_ = v___x_619_;
v_b_615_ = v___y_617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object* v_as_626_, lean_object* v_i_627_, lean_object* v_stop_628_, lean_object* v_b_629_){
_start:
{
size_t v_i_boxed_630_; size_t v_stop_boxed_631_; lean_object* v_res_632_; 
v_i_boxed_630_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_stop_boxed_631_ = lean_unbox_usize(v_stop_628_);
lean_dec(v_stop_628_);
v_res_632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_626_, v_i_boxed_630_, v_stop_boxed_631_, v_b_629_);
lean_dec_ref(v_as_626_);
return v_res_632_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object* v___x_633_, lean_object* v_as_634_, size_t v_i_635_, size_t v_stop_636_){
_start:
{
uint8_t v___x_637_; 
v___x_637_ = lean_usize_dec_eq(v_i_635_, v_stop_636_);
if (v___x_637_ == 0)
{
uint8_t v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = 1;
v___x_639_ = lean_array_uget_borrowed(v_as_634_, v_i_635_);
lean_inc(v___x_639_);
v___x_640_ = l_Std_Http_Internal_isToken(v___x_639_);
if (v___x_640_ == 0)
{
return v___x_638_;
}
else
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_nat_dec_eq(v___x_633_, v___x_641_);
if (v___x_642_ == 0)
{
size_t v___x_643_; size_t v___x_644_; 
v___x_643_ = ((size_t)1ULL);
v___x_644_ = lean_usize_add(v_i_635_, v___x_643_);
v_i_635_ = v___x_644_;
goto _start;
}
else
{
return v___x_638_;
}
}
}
else
{
uint8_t v___x_646_; 
v___x_646_ = 0;
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object* v___x_647_, lean_object* v_as_648_, lean_object* v_i_649_, lean_object* v_stop_650_){
_start:
{
size_t v_i_boxed_651_; size_t v_stop_boxed_652_; uint8_t v_res_653_; lean_object* v_r_654_; 
v_i_boxed_651_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_stop_boxed_652_ = lean_unbox_usize(v_stop_650_);
lean_dec(v_stop_650_);
v_res_653_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_647_, v_as_648_, v_i_boxed_651_, v_stop_boxed_652_);
lean_dec_ref(v_as_648_);
lean_dec(v___x_647_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object* v_codings_659_){
_start:
{
uint8_t v___y_661_; lean_object* v___y_662_; uint8_t v___y_663_; lean_object* v___y_664_; uint8_t v___y_671_; uint8_t v___y_672_; lean_object* v___y_673_; uint8_t v___y_683_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = lean_array_get_size(v_codings_659_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_nat_dec_eq(v___x_697_, v___x_698_);
if (v___x_699_ == 0)
{
uint8_t v___x_700_; 
v___x_700_ = lean_nat_dec_lt(v___x_698_, v___x_697_);
if (v___x_700_ == 0)
{
v___y_683_ = v___x_699_;
goto v___jp_682_;
}
else
{
if (v___x_700_ == 0)
{
v___y_683_ = v___x_699_;
goto v___jp_682_;
}
else
{
size_t v___x_701_; size_t v___x_702_; uint8_t v___x_703_; 
v___x_701_ = ((size_t)0ULL);
v___x_702_ = lean_usize_of_nat(v___x_697_);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_697_, v_codings_659_, v___x_701_, v___x_702_);
v___y_683_ = v___x_703_;
goto v___jp_682_;
}
}
}
else
{
v___y_683_ = v___x_699_;
goto v___jp_682_;
}
v___jp_660_:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_dec_lt(v___x_665_, v___y_662_);
if (v___x_666_ == 0)
{
uint8_t v___x_667_; 
v___x_667_ = lean_nat_dec_eq(v___y_662_, v___x_665_);
lean_dec(v___y_662_);
if (v___x_667_ == 0)
{
lean_dec(v___y_664_);
if (v___x_667_ == 0)
{
return v___y_663_;
}
else
{
return v___y_661_;
}
}
else
{
lean_object* v___x_668_; uint8_t v_lastIsChunked_669_; 
v___x_668_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v_lastIsChunked_669_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_664_, v___x_668_);
lean_dec(v___y_664_);
if (v_lastIsChunked_669_ == 0)
{
if (v___x_667_ == 0)
{
return v___y_663_;
}
else
{
return v___y_661_;
}
}
else
{
return v___y_663_;
}
}
}
else
{
lean_dec(v___y_664_);
lean_dec(v___y_662_);
return v___y_661_;
}
}
v___jp_670_:
{
lean_object* v_chunkedCount_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_chunkedCount_674_ = lean_array_get_size(v___y_673_);
lean_dec_ref(v___y_673_);
v___x_675_ = lean_array_get_size(v_codings_659_);
v___x_676_ = lean_unsigned_to_nat(1u);
v___x_677_ = lean_nat_sub(v___x_675_, v___x_676_);
v___x_678_ = lean_nat_dec_lt(v___x_677_, v___x_675_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_dec(v___x_677_);
v___x_679_ = lean_box(0);
v___y_661_ = v___y_671_;
v___y_662_ = v_chunkedCount_674_;
v___y_663_ = v___y_672_;
v___y_664_ = v___x_679_;
goto v___jp_660_;
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_array_fget_borrowed(v_codings_659_, v___x_677_);
lean_dec(v___x_677_);
lean_inc(v___x_680_);
v___x_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
v___y_661_ = v___y_671_;
v___y_662_ = v_chunkedCount_674_;
v___y_663_ = v___y_672_;
v___y_664_ = v___x_681_;
goto v___jp_660_;
}
}
v___jp_682_:
{
if (v___y_683_ == 0)
{
uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_684_ = 1;
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_array_get_size(v_codings_659_);
v___x_687_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__1));
v___x_688_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
if (v___x_688_ == 0)
{
v___y_671_ = v___y_683_;
v___y_672_ = v___x_684_;
v___y_673_ = v___x_687_;
goto v___jp_670_;
}
else
{
uint8_t v___x_689_; 
v___x_689_ = lean_nat_dec_le(v___x_686_, v___x_686_);
if (v___x_689_ == 0)
{
if (v___x_688_ == 0)
{
v___y_671_ = v___y_683_;
v___y_672_ = v___x_684_;
v___y_673_ = v___x_687_;
goto v___jp_670_;
}
else
{
size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((size_t)0ULL);
v___x_691_ = lean_usize_of_nat(v___x_686_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_659_, v___x_690_, v___x_691_, v___x_687_);
v___y_671_ = v___y_683_;
v___y_672_ = v___x_684_;
v___y_673_ = v___x_692_;
goto v___jp_670_;
}
}
else
{
size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
v___x_693_ = ((size_t)0ULL);
v___x_694_ = lean_usize_of_nat(v___x_686_);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_659_, v___x_693_, v___x_694_, v___x_687_);
v___y_671_ = v___y_683_;
v___y_672_ = v___x_684_;
v___y_673_ = v___x_695_;
goto v___jp_670_;
}
}
}
else
{
uint8_t v___x_696_; 
v___x_696_ = 0;
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_Validate___boxed(lean_object* v_codings_704_){
_start:
{
uint8_t v_res_705_; lean_object* v_r_706_; 
v_res_705_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_704_);
lean_dec_ref(v_codings_704_);
v_r_706_ = lean_box(v_res_705_);
return v_r_706_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(lean_object* v___y_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = l_String_quote(v___y_707_);
v___x_709_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
if (lean_obj_tag(v_x_712_) == 0)
{
lean_dec(v_x_710_);
return v_x_711_;
}
else
{
lean_object* v_head_713_; lean_object* v_tail_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_725_; 
v_head_713_ = lean_ctor_get(v_x_712_, 0);
v_tail_714_ = lean_ctor_get(v_x_712_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_x_712_);
if (v_isSharedCheck_725_ == 0)
{
v___x_716_ = v_x_712_;
v_isShared_717_ = v_isSharedCheck_725_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_tail_714_);
lean_inc(v_head_713_);
lean_dec(v_x_712_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_725_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
lean_inc(v_x_710_);
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 5);
lean_ctor_set(v___x_716_, 1, v_x_710_);
lean_ctor_set(v___x_716_, 0, v_x_711_);
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_x_711_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_x_710_);
v___x_719_ = v_reuseFailAlloc_724_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_720_ = l_String_quote(v_head_713_);
v___x_721_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
v___x_722_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_722_, 0, v___x_719_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
v_x_711_ = v___x_722_;
v_x_712_ = v_tail_714_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
if (lean_obj_tag(v_x_728_) == 0)
{
lean_dec(v_x_726_);
return v_x_727_;
}
else
{
lean_object* v_head_729_; lean_object* v_tail_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_741_; 
v_head_729_ = lean_ctor_get(v_x_728_, 0);
v_tail_730_ = lean_ctor_get(v_x_728_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_x_728_);
if (v_isSharedCheck_741_ == 0)
{
v___x_732_ = v_x_728_;
v_isShared_733_ = v_isSharedCheck_741_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_tail_730_);
lean_inc(v_head_729_);
lean_dec(v_x_728_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_741_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
lean_inc(v_x_726_);
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 5);
lean_ctor_set(v___x_732_, 1, v_x_726_);
lean_ctor_set(v___x_732_, 0, v_x_727_);
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_x_727_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_x_726_);
v___x_735_ = v_reuseFailAlloc_740_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_736_ = l_String_quote(v_head_729_);
v___x_737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
v___x_738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_735_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(v_x_726_, v___x_738_, v_tail_730_);
return v___x_739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
if (lean_obj_tag(v_x_742_) == 0)
{
lean_object* v___x_744_; 
lean_dec(v_x_743_);
v___x_744_ = lean_box(0);
return v___x_744_;
}
else
{
lean_object* v_tail_745_; 
v_tail_745_ = lean_ctor_get(v_x_742_, 1);
if (lean_obj_tag(v_tail_745_) == 0)
{
lean_object* v_head_746_; lean_object* v___x_747_; 
lean_dec(v_x_743_);
v_head_746_ = lean_ctor_get(v_x_742_, 0);
lean_inc(v_head_746_);
lean_dec_ref(v_x_742_);
v___x_747_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_746_);
return v___x_747_;
}
else
{
lean_object* v_head_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
lean_inc(v_tail_745_);
v_head_748_ = lean_ctor_get(v_x_742_, 0);
lean_inc(v_head_748_);
lean_dec_ref(v_x_742_);
v___x_749_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_748_);
v___x_750_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(v_x_743_, v___x_749_, v_tail_745_);
return v___x_750_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0));
v___x_760_ = lean_string_length(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5);
v___x_762_ = lean_nat_to_int(v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(lean_object* v_xs_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_array_get_size(v_xs_770_);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_nat_dec_eq(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_774_ = lean_array_to_list(v_xs_770_);
v___x_775_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3));
v___x_776_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(v___x_774_, v___x_775_);
v___x_777_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6);
v___x_778_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7));
v___x_779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v___x_776_);
v___x_780_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8));
v___x_781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_777_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Std_Format_fill(v___x_782_);
return v___x_783_;
}
else
{
lean_object* v___x_784_; 
lean_dec_ref(v_xs_770_);
v___x_784_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10));
return v___x_784_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_unsigned_to_nat(11u);
v___x_795_ = lean_nat_to_int(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg(lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_803_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_804_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3));
v___x_805_ = lean_obj_once(&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4, &l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4);
v___x_806_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_802_);
v___x_807_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = 0;
v___x_809_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set_uint8(v___x_809_, sizeof(void*)*1, v___x_808_);
v___x_810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_804_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_812_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v___x_813_ = lean_box(1);
v___x_814_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6));
v___x_816_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v___x_803_);
v___x_818_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_819_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_821_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_822_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_819_);
v___x_823_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_824_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_820_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set_uint8(v___x_826_, sizeof(void*)*1, v___x_808_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr(lean_object* v_x_827_, lean_object* v_prec_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg(v_x_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___boxed(lean_object* v_x_830_, lean_object* v_prec_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Std_Http_Header_instReprTransferEncoding_repr(v_x_830_, v_prec_831_);
lean_dec(v_prec_831_);
return v_res_832_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object* v_te_835_){
_start:
{
lean_object* v___y_837_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_840_ = lean_array_get_size(v_te_835_);
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_sub(v___x_840_, v___x_841_);
v___x_843_ = lean_nat_dec_lt(v___x_842_, v___x_840_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec(v___x_842_);
v___x_844_ = lean_box(0);
v___y_837_ = v___x_844_;
goto v___jp_836_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_array_fget_borrowed(v_te_835_, v___x_842_);
lean_dec(v___x_842_);
lean_inc(v___x_845_);
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
v___y_837_ = v___x_846_;
goto v___jp_836_;
}
v___jp_836_:
{
lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_838_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v___x_839_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_837_, v___x_838_);
lean_dec(v___y_837_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_isChunked___boxed(lean_object* v_te_847_){
_start:
{
uint8_t v_res_848_; lean_object* v_r_849_; 
v_res_848_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_847_);
lean_dec_ref(v_te_847_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object* v_v_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_850_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_852_; 
v___x_852_ = lean_box(0);
return v___x_852_;
}
else
{
lean_object* v_val_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_862_; 
v_val_853_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_862_ == 0)
{
v___x_855_ = v___x_851_;
v_isShared_856_ = v_isSharedCheck_862_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_val_853_);
lean_dec(v___x_851_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_862_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
uint8_t v___x_857_; 
v___x_857_ = l_Std_Http_Header_TransferEncoding_Validate(v_val_853_);
if (v___x_857_ == 0)
{
lean_object* v___x_858_; 
lean_del_object(v___x_855_);
lean_dec(v_val_853_);
v___x_858_ = lean_box(0);
return v___x_858_;
}
else
{
lean_object* v___x_860_; 
if (v_isShared_856_ == 0)
{
v___x_860_ = v___x_855_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_val_853_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_serialize(lean_object* v_te_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_value_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_864_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_865_ = lean_array_to_list(v_te_863_);
v_value_866_ = l_String_intercalate(v___x_864_, v___x_865_);
v___x_867_ = l_Std_Http_Header_Name_transferEncoding;
v___x_868_ = l_Std_Http_Header_Value_ofString_x21(v_value_866_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___redArg(lean_object* v_x_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_889_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_890_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__3));
v___x_891_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_892_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_888_);
v___x_893_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = 0;
v___x_895_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set_uint8(v___x_895_, sizeof(void*)*1, v___x_894_);
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_890_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = lean_box(1);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__5));
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_889_);
v___x_904_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_907_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_905_);
v___x_909_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_906_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set_uint8(v___x_912_, sizeof(void*)*1, v___x_894_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr(lean_object* v_x_913_, lean_object* v_prec_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Std_Http_Header_instReprConnection_repr___redArg(v_x_913_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___boxed(lean_object* v_x_916_, lean_object* v_prec_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Std_Http_Header_instReprConnection_repr(v_x_916_, v_prec_917_);
lean_dec(v_prec_917_);
return v_res_918_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(lean_object* v_token_921_, lean_object* v_as_922_, size_t v_i_923_, size_t v_stop_924_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_eq(v_i_923_, v_stop_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_926_ = lean_array_uget_borrowed(v_as_922_, v_i_923_);
v___x_927_ = lean_string_dec_eq(v___x_926_, v_token_921_);
if (v___x_927_ == 0)
{
size_t v___x_928_; size_t v___x_929_; 
v___x_928_ = ((size_t)1ULL);
v___x_929_ = lean_usize_add(v_i_923_, v___x_928_);
v_i_923_ = v___x_929_;
goto _start;
}
else
{
return v___x_927_;
}
}
else
{
uint8_t v___x_931_; 
v___x_931_ = 0;
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(lean_object* v_token_932_, lean_object* v_as_933_, lean_object* v_i_934_, lean_object* v_stop_935_){
_start:
{
size_t v_i_boxed_936_; size_t v_stop_boxed_937_; uint8_t v_res_938_; lean_object* v_r_939_; 
v_i_boxed_936_ = lean_unbox_usize(v_i_934_);
lean_dec(v_i_934_);
v_stop_boxed_937_ = lean_unbox_usize(v_stop_935_);
lean_dec(v_stop_935_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_932_, v_as_933_, v_i_boxed_936_, v_stop_boxed_937_);
lean_dec_ref(v_as_933_);
lean_dec_ref(v_token_932_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_containsToken(lean_object* v_connection_940_, lean_object* v_token_941_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_array_get_size(v_connection_940_);
v___x_944_ = lean_nat_dec_lt(v___x_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec_ref(v_token_941_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; 
v___x_945_ = lean_string_utf8_byte_size(v_token_941_);
if (v___x_944_ == 0)
{
lean_dec_ref(v_token_941_);
return v___x_944_;
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v_token_949_; size_t v___x_950_; size_t v___x_951_; uint8_t v___x_952_; 
v___x_946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_946_, 0, v_token_941_);
lean_ctor_set(v___x_946_, 1, v___x_942_);
lean_ctor_set(v___x_946_, 2, v___x_945_);
v___x_947_ = l_String_Slice_trimAscii(v___x_946_);
v___x_948_ = l_String_Slice_toString(v___x_947_);
lean_dec_ref(v___x_947_);
v_token_949_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_948_, v___x_942_);
v___x_950_ = ((size_t)0ULL);
v___x_951_ = lean_usize_of_nat(v___x_943_);
v___x_952_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_949_, v_connection_940_, v___x_950_, v___x_951_);
lean_dec_ref(v_token_949_);
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_containsToken___boxed(lean_object* v_connection_953_, lean_object* v_token_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Std_Http_Header_Connection_containsToken(v_connection_953_, v_token_954_);
lean_dec_ref(v_connection_953_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_shouldClose(lean_object* v_connection_958_){
_start:
{
lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = ((lean_object*)(l_Std_Http_Header_Connection_shouldClose___closed__0));
v___x_960_ = l_Std_Http_Header_Connection_containsToken(v_connection_958_, v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_shouldClose___boxed(lean_object* v_connection_961_){
_start:
{
uint8_t v_res_962_; lean_object* v_r_963_; 
v_res_962_ = l_Std_Http_Header_Connection_shouldClose(v_connection_961_);
lean_dec_ref(v_connection_961_);
v_r_963_ = lean_box(v_res_962_);
return v_r_963_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(lean_object* v_as_964_, size_t v_i_965_, size_t v_stop_966_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = lean_usize_dec_eq(v_i_965_, v_stop_966_);
if (v___x_967_ == 0)
{
uint8_t v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_968_ = 1;
v___x_969_ = lean_array_uget_borrowed(v_as_964_, v_i_965_);
lean_inc(v___x_969_);
v___x_970_ = l_Std_Http_Internal_isToken(v___x_969_);
if (v___x_970_ == 0)
{
return v___x_968_;
}
else
{
if (v___x_967_ == 0)
{
size_t v___x_971_; size_t v___x_972_; 
v___x_971_ = ((size_t)1ULL);
v___x_972_ = lean_usize_add(v_i_965_, v___x_971_);
v_i_965_ = v___x_972_;
goto _start;
}
else
{
return v___x_968_;
}
}
}
else
{
uint8_t v___x_974_; 
v___x_974_ = 0;
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(lean_object* v_as_975_, lean_object* v_i_976_, lean_object* v_stop_977_){
_start:
{
size_t v_i_boxed_978_; size_t v_stop_boxed_979_; uint8_t v_res_980_; lean_object* v_r_981_; 
v_i_boxed_978_ = lean_unbox_usize(v_i_976_);
lean_dec(v_i_976_);
v_stop_boxed_979_ = lean_unbox_usize(v_stop_977_);
lean_dec(v_stop_977_);
v_res_980_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_975_, v_i_boxed_978_, v_stop_boxed_979_);
lean_dec_ref(v_as_975_);
v_r_981_ = lean_box(v_res_980_);
return v_r_981_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_parse(lean_object* v_v_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v___x_984_; 
v___x_984_ = lean_box(0);
return v___x_984_;
}
else
{
lean_object* v_val_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1005_; 
v_val_985_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_987_ = v___x_983_;
v_isShared_988_ = v_isSharedCheck_1005_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_val_985_);
lean_dec(v___x_983_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1005_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_array_get_size(v_val_985_);
v___x_991_ = lean_nat_dec_lt(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_993_; 
if (v_isShared_988_ == 0)
{
v___x_993_ = v___x_987_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_val_985_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
if (v___x_991_ == 0)
{
lean_object* v___x_996_; 
if (v_isShared_988_ == 0)
{
v___x_996_ = v___x_987_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_val_985_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
size_t v___x_998_; size_t v___x_999_; uint8_t v___x_1000_; 
v___x_998_ = ((size_t)0ULL);
v___x_999_ = lean_usize_of_nat(v___x_990_);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_val_985_, v___x_998_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1002_; 
if (v_isShared_988_ == 0)
{
v___x_1002_ = v___x_987_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_val_985_);
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
lean_object* v___x_1004_; 
lean_del_object(v___x_987_);
lean_dec(v_val_985_);
v___x_1004_ = lean_box(0);
return v___x_1004_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_serialize(lean_object* v_connection_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_value_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1007_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_1008_ = lean_array_to_list(v_connection_1006_);
v_value_1009_ = l_String_intercalate(v___x_1007_, v___x_1008_);
v___x_1010_ = l_Std_Http_Header_Name_connection;
v___x_1011_ = l_Std_Http_Header_Value_ofString_x21(v_value_1009_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
return v___x_1012_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_unsigned_to_nat(8u);
v___x_1029_ = lean_nat_to_int(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_unsigned_to_nat(2u);
v___x_1031_ = lean_nat_to_int(v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___redArg(lean_object* v_x_1039_){
_start:
{
lean_object* v_host_1040_; lean_object* v_port_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1115_; 
v_host_1040_ = lean_ctor_get(v_x_1039_, 0);
v_port_1041_ = lean_ctor_get(v_x_1039_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_x_1039_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1043_ = v_x_1039_;
v_isShared_1044_ = v_isSharedCheck_1115_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_port_1041_);
lean_inc(v_host_1040_);
lean_dec(v_x_1039_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1115_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v_ctr_1051_; lean_object* v_a_1052_; 
v___x_1045_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_1046_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__3));
v___x_1047_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__4, &l_Std_Http_Header_instReprHost_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__5, &l_Std_Http_Header_instReprHost_repr___redArg___closed__5_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5);
switch(lean_obj_tag(v_host_1040_))
{
case 0:
{
lean_object* v_name_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1094_; 
v_name_1085_ = lean_ctor_get(v_host_1040_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_host_1040_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1087_ = v_host_1040_;
v_isShared_1088_ = v_isSharedCheck_1094_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_name_1085_);
lean_dec(v_host_1040_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1094_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1089_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__9));
v___x_1090_ = l_String_quote(v_name_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 3);
lean_ctor_set(v___x_1087_, 0, v___x_1090_);
v___x_1092_ = v___x_1087_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
v_ctr_1051_ = v___x_1089_;
v_a_1052_ = v___x_1092_;
goto v___jp_1050_;
}
}
}
case 1:
{
lean_object* v_ipv4_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1104_; 
v_ipv4_1095_ = lean_ctor_get(v_host_1040_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_host_1040_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1097_ = v_host_1040_;
v_isShared_1098_ = v_isSharedCheck_1104_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_ipv4_1095_);
lean_dec(v_host_1040_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1104_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1099_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__10));
v___x_1100_ = lean_uv_ntop_v4(v_ipv4_1095_);
lean_dec_ref(v_ipv4_1095_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set_tag(v___x_1097_, 3);
lean_ctor_set(v___x_1097_, 0, v___x_1100_);
v___x_1102_ = v___x_1097_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
v_ctr_1051_ = v___x_1099_;
v_a_1052_ = v___x_1102_;
goto v___jp_1050_;
}
}
}
default: 
{
lean_object* v_ipv6_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1114_; 
v_ipv6_1105_ = lean_ctor_get(v_host_1040_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_host_1040_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1107_ = v_host_1040_;
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_ipv6_1105_);
lean_dec(v_host_1040_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1114_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1109_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__11));
v___x_1110_ = lean_uv_ntop_v6(v_ipv6_1105_);
lean_dec_ref(v_ipv6_1105_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set_tag(v___x_1107_, 3);
lean_ctor_set(v___x_1107_, 0, v___x_1110_);
v___x_1112_ = v___x_1107_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
v_ctr_1051_ = v___x_1109_;
v_a_1052_ = v___x_1112_;
goto v___jp_1050_;
}
}
}
}
v___jp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1053_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__6));
v___x_1054_ = lean_string_append(v___x_1053_, v_ctr_1051_);
v___x_1055_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
v___x_1056_ = lean_box(1);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 5);
lean_ctor_set(v___x_1043_, 1, v___x_1056_);
lean_ctor_set(v___x_1043_, 0, v___x_1055_);
v___x_1058_ = v___x_1043_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v_a_1052_);
v___x_1060_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1049_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = 0;
v___x_1062_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set_uint8(v___x_1062_, sizeof(void*)*1, v___x_1061_);
v___x_1063_ = l_Repr_addAppParen(v___x_1062_, v___x_1048_);
v___x_1064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1047_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*1, v___x_1061_);
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1046_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1056_);
v___x_1070_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__8));
v___x_1071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___x_1045_);
v___x_1073_ = l_Std_Http_URI_instReprPort_repr(v_port_1041_, v___x_1048_);
lean_dec(v_port_1041_);
v___x_1074_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1047_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*1, v___x_1061_);
v___x_1076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1072_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1078_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1076_);
v___x_1080_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_1081_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1077_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*1, v___x_1061_);
return v___x_1083_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr(lean_object* v_x_1116_, lean_object* v_prec_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Std_Http_Header_instReprHost_repr___redArg(v_x_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___boxed(lean_object* v_x_1119_, lean_object* v_prec_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Std_Http_Header_instReprHost_repr(v_x_1119_, v_prec_1120_);
lean_dec(v_prec_1120_);
return v_res_1121_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqHost_beq(lean_object* v_x_1124_, lean_object* v_x_1125_){
_start:
{
lean_object* v_host_1126_; lean_object* v_port_1127_; lean_object* v_host_1128_; lean_object* v_port_1129_; uint8_t v___x_1130_; 
v_host_1126_ = lean_ctor_get(v_x_1124_, 0);
v_port_1127_ = lean_ctor_get(v_x_1124_, 1);
v_host_1128_ = lean_ctor_get(v_x_1125_, 0);
v_port_1129_ = lean_ctor_get(v_x_1125_, 1);
v___x_1130_ = l_Std_Http_URI_instBEqHost_beq(v_host_1126_, v_host_1128_);
if (v___x_1130_ == 0)
{
return v___x_1130_;
}
else
{
uint8_t v___x_1131_; 
v___x_1131_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1127_, v_port_1129_);
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqHost_beq___boxed(lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
uint8_t v_res_1134_; lean_object* v_r_1135_; 
v_res_1134_ = l_Std_Http_Header_instBEqHost_beq(v_x_1132_, v_x_1133_);
lean_dec_ref(v_x_1133_);
lean_dec_ref(v_x_1132_);
v_r_1135_ = lean_box(v_res_1134_);
return v_r_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0(lean_object* v___x_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Std_Http_URI_Parser_parseHostHeader(v___x_1141_, v___y_1142_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_pos_1144_; lean_object* v_array_1145_; lean_object* v_idx_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; 
v_pos_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_pos_1144_);
v_array_1145_ = lean_ctor_get(v_pos_1144_, 0);
v_idx_1146_ = lean_ctor_get(v_pos_1144_, 1);
v___x_1147_ = lean_byte_array_size(v_array_1145_);
v___x_1148_ = lean_nat_dec_lt(v_idx_1146_, v___x_1147_);
if (v___x_1148_ == 0)
{
lean_dec(v_pos_1144_);
return v___x_1143_;
}
else
{
lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1156_ == 0)
{
lean_object* v_unused_1157_; lean_object* v_unused_1158_; 
v_unused_1157_ = lean_ctor_get(v___x_1143_, 1);
lean_dec(v_unused_1157_);
v_unused_1158_ = lean_ctor_get(v___x_1143_, 0);
lean_dec(v_unused_1158_);
v___x_1150_ = v___x_1143_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_dec(v___x_1143_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = ((lean_object*)(l_Std_Http_Header_Host_parse___lam__0___closed__1));
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 1);
lean_ctor_set(v___x_1150_, 1, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_pos_1144_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0___boxed(lean_object* v___x_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Std_Http_Header_Host_parse___lam__0(v___x_1159_, v___y_1160_);
lean_dec_ref(v___x_1159_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse(lean_object* v_v_1172_){
_start:
{
lean_object* v___f_1173_; lean_object* v___x_1174_; lean_object* v_parsed_1175_; 
v___f_1173_ = ((lean_object*)(l_Std_Http_Header_Host_parse___closed__1));
v___x_1174_ = lean_string_to_utf8(v_v_1172_);
v_parsed_1175_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1173_, v___x_1174_);
if (lean_obj_tag(v_parsed_1175_) == 0)
{
lean_object* v___x_1176_; 
lean_dec_ref(v_parsed_1175_);
v___x_1176_ = lean_box(0);
return v___x_1176_;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1193_; 
v_a_1177_ = lean_ctor_get(v_parsed_1175_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_parsed_1175_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1179_ = v_parsed_1175_;
v_isShared_1180_ = v_isSharedCheck_1193_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v_parsed_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1193_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_fst_1181_; lean_object* v_snd_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1192_; 
v_fst_1181_ = lean_ctor_get(v_a_1177_, 0);
v_snd_1182_ = lean_ctor_get(v_a_1177_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_a_1177_);
if (v_isSharedCheck_1192_ == 0)
{
v___x_1184_ = v_a_1177_;
v_isShared_1185_ = v_isSharedCheck_1192_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_snd_1182_);
lean_inc(v_fst_1181_);
lean_dec(v_a_1177_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1192_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_fst_1181_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_snd_1182_);
v___x_1187_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1189_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1187_);
v___x_1189_ = v___x_1179_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___boxed(lean_object* v_v_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Std_Http_Header_Host_parse(v_v_1194_);
lean_dec_ref(v_v_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_serialize(lean_object* v_host_1198_){
_start:
{
lean_object* v___y_1200_; lean_object* v___y_1204_; lean_object* v_port_1208_; 
v_port_1208_ = lean_ctor_get(v_host_1198_, 1);
switch(lean_obj_tag(v_port_1208_))
{
case 0:
{
lean_object* v_host_1209_; 
v_host_1209_ = lean_ctor_get(v_host_1198_, 0);
lean_inc_ref(v_host_1209_);
lean_dec_ref(v_host_1198_);
switch(lean_obj_tag(v_host_1209_))
{
case 0:
{
lean_object* v_name_1210_; lean_object* v___x_1211_; 
v_name_1210_ = lean_ctor_get(v_host_1209_, 0);
lean_inc_ref(v_name_1210_);
lean_dec_ref(v_host_1209_);
v___x_1211_ = l_Std_Http_Header_Value_ofString_x21(v_name_1210_);
v___y_1200_ = v___x_1211_;
goto v___jp_1199_;
}
case 1:
{
lean_object* v_ipv4_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_ipv4_1212_ = lean_ctor_get(v_host_1209_, 0);
lean_inc_ref(v_ipv4_1212_);
lean_dec_ref(v_host_1209_);
v___x_1213_ = lean_uv_ntop_v4(v_ipv4_1212_);
lean_dec_ref(v_ipv4_1212_);
v___x_1214_ = l_Std_Http_Header_Value_ofString_x21(v___x_1213_);
v___y_1200_ = v___x_1214_;
goto v___jp_1199_;
}
default: 
{
lean_object* v_ipv6_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v_ipv6_1215_ = lean_ctor_get(v_host_1209_, 0);
lean_inc_ref(v_ipv6_1215_);
lean_dec_ref(v_host_1209_);
v___x_1216_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1217_ = lean_uv_ntop_v6(v_ipv6_1215_);
lean_dec_ref(v_ipv6_1215_);
v___x_1218_ = lean_string_append(v___x_1216_, v___x_1217_);
lean_dec_ref(v___x_1217_);
v___x_1219_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1220_ = lean_string_append(v___x_1218_, v___x_1219_);
v___x_1221_ = l_Std_Http_Header_Value_ofString_x21(v___x_1220_);
v___y_1200_ = v___x_1221_;
goto v___jp_1199_;
}
}
}
case 1:
{
lean_object* v_host_1222_; 
v_host_1222_ = lean_ctor_get(v_host_1198_, 0);
lean_inc_ref(v_host_1222_);
lean_dec_ref(v_host_1198_);
switch(lean_obj_tag(v_host_1222_))
{
case 0:
{
lean_object* v_name_1223_; 
v_name_1223_ = lean_ctor_get(v_host_1222_, 0);
lean_inc_ref(v_name_1223_);
lean_dec_ref(v_host_1222_);
v___y_1204_ = v_name_1223_;
goto v___jp_1203_;
}
case 1:
{
lean_object* v_ipv4_1224_; lean_object* v___x_1225_; 
v_ipv4_1224_ = lean_ctor_get(v_host_1222_, 0);
lean_inc_ref(v_ipv4_1224_);
lean_dec_ref(v_host_1222_);
v___x_1225_ = lean_uv_ntop_v4(v_ipv4_1224_);
lean_dec_ref(v_ipv4_1224_);
v___y_1204_ = v___x_1225_;
goto v___jp_1203_;
}
default: 
{
lean_object* v_ipv6_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_ipv6_1226_ = lean_ctor_get(v_host_1222_, 0);
lean_inc_ref(v_ipv6_1226_);
lean_dec_ref(v_host_1222_);
v___x_1227_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1228_ = lean_uv_ntop_v6(v_ipv6_1226_);
lean_dec_ref(v_ipv6_1226_);
v___x_1229_ = lean_string_append(v___x_1227_, v___x_1228_);
lean_dec_ref(v___x_1228_);
v___x_1230_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1231_ = lean_string_append(v___x_1229_, v___x_1230_);
v___y_1204_ = v___x_1231_;
goto v___jp_1203_;
}
}
}
default: 
{
lean_object* v_host_1232_; uint16_t v_port_1233_; lean_object* v___y_1235_; 
lean_inc_ref(v_port_1208_);
v_host_1232_ = lean_ctor_get(v_host_1198_, 0);
lean_inc_ref(v_host_1232_);
lean_dec_ref(v_host_1198_);
v_port_1233_ = lean_ctor_get_uint16(v_port_1208_, 0);
lean_dec_ref(v_port_1208_);
switch(lean_obj_tag(v_host_1232_))
{
case 0:
{
lean_object* v_name_1242_; 
v_name_1242_ = lean_ctor_get(v_host_1232_, 0);
lean_inc_ref(v_name_1242_);
lean_dec_ref(v_host_1232_);
v___y_1235_ = v_name_1242_;
goto v___jp_1234_;
}
case 1:
{
lean_object* v_ipv4_1243_; lean_object* v___x_1244_; 
v_ipv4_1243_ = lean_ctor_get(v_host_1232_, 0);
lean_inc_ref(v_ipv4_1243_);
lean_dec_ref(v_host_1232_);
v___x_1244_ = lean_uv_ntop_v4(v_ipv4_1243_);
lean_dec_ref(v_ipv4_1243_);
v___y_1235_ = v___x_1244_;
goto v___jp_1234_;
}
default: 
{
lean_object* v_ipv6_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_ipv6_1245_ = lean_ctor_get(v_host_1232_, 0);
lean_inc_ref(v_ipv6_1245_);
lean_dec_ref(v_host_1232_);
v___x_1246_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1247_ = lean_uv_ntop_v6(v_ipv6_1245_);
lean_dec_ref(v_ipv6_1245_);
v___x_1248_ = lean_string_append(v___x_1246_, v___x_1247_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1250_ = lean_string_append(v___x_1248_, v___x_1249_);
v___y_1235_ = v___x_1250_;
goto v___jp_1234_;
}
}
v___jp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1236_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1237_ = lean_string_append(v___y_1235_, v___x_1236_);
v___x_1238_ = lean_uint16_to_nat(v_port_1233_);
v___x_1239_ = l_Nat_reprFast(v___x_1238_);
v___x_1240_ = lean_string_append(v___x_1237_, v___x_1239_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = l_Std_Http_Header_Value_ofString_x21(v___x_1240_);
v___y_1200_ = v___x_1241_;
goto v___jp_1199_;
}
}
}
v___jp_1199_:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__0));
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1201_);
lean_ctor_set(v___x_1202_, 1, v___y_1200_);
return v___x_1202_;
}
v___jp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1206_ = lean_string_append(v___y_1204_, v___x_1205_);
v___x_1207_ = l_Std_Http_Header_Value_ofString_x21(v___x_1206_);
v___y_1200_ = v___x_1207_;
goto v___jp_1199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_toCtorIdx(lean_object* v_x_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_unsigned_to_nat(0u);
return v___x_1258_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___closed__2(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = ((lean_object*)(l_Std_Http_Header_instReprExpect_repr___closed__1));
v___x_1266_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1267_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___closed__3(void){
_start:
{
uint8_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = 0;
v___x_1269_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___closed__2, &l_Std_Http_Header_instReprExpect_repr___closed__2_once, _init_l_Std_Http_Header_instReprExpect_repr___closed__2);
v___x_1270_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
lean_ctor_set_uint8(v___x_1270_, sizeof(void*)*1, v___x_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr(lean_object* v_x_1271_, lean_object* v_prec_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___closed__3, &l_Std_Http_Header_instReprExpect_repr___closed__3_once, _init_l_Std_Http_Header_instReprExpect_repr___closed__3);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___boxed(lean_object* v_x_1274_, lean_object* v_prec_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_Http_Header_instReprExpect_repr(v_x_1274_, v_prec_1275_);
lean_dec(v_prec_1275_);
return v_res_1276_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq(lean_object* v_x_1279_, lean_object* v_y_1280_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = 1;
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___boxed(lean_object* v_x_1282_, lean_object* v_y_1283_){
_start:
{
uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_res_1284_ = l_Std_Http_Header_instBEqExpect_beq(v_x_1282_, v_y_1283_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_parse(lean_object* v_v_1291_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v_normalized_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_string_utf8_byte_size(v_v_1291_);
v___x_1294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1294_, 0, v_v_1291_);
lean_ctor_set(v___x_1294_, 1, v___x_1292_);
lean_ctor_set(v___x_1294_, 2, v___x_1293_);
v___x_1295_ = l_String_Slice_trimAscii(v___x_1294_);
v___x_1296_ = l_String_Slice_toString(v___x_1295_);
lean_dec_ref(v___x_1295_);
v_normalized_1297_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_1296_, v___x_1292_);
v___x_1298_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1299_ = lean_string_dec_eq(v_normalized_1297_, v___x_1298_);
lean_dec_ref(v_normalized_1297_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_box(0);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; 
v___x_1301_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__1));
return v___x_1301_;
}
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___closed__0(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1303_ = l_Std_Http_Header_Value_ofString_x21(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___closed__1(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___closed__0, &l_Std_Http_Header_Expect_serialize___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___closed__0);
v___x_1305_ = l_Std_Http_Header_Name_expect;
v___x_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1305_);
lean_ctor_set(v___x_1306_, 1, v___x_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize(lean_object* v_x_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___closed__1, &l_Std_Http_Header_Expect_serialize___closed__1_once, _init_l_Std_Http_Header_Expect_serialize___closed__1);
return v___x_1308_;
}
}
lean_object* runtime_initialize_Std_Http_Data_URI(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers_Name(uint8_t builtin);
lean_object* runtime_initialize_Std_Http_Data_Headers_Value(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Headers_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

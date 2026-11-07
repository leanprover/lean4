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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_Http_Header_Value_ofString_x21(lean_object*);
lean_object* lean_uv_ntop_v4(lean_object*);
lean_object* lean_uv_ntop_v6(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
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
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* l_Std_Http_Header_Name_instEncodeV11_go(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
extern lean_object* l_Std_Http_Header_Name_transferEncoding;
extern lean_object* l_Std_Http_Header_Name_contentLength;
extern lean_object* l_Std_Http_Header_Name_connection;
uint8_t l_Std_Http_URI_instBEqHost_beq(lean_object*, lean_object*);
uint8_t l_Std_Http_URI_instDecidableEqPort_decEq(lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Internal_appendFieldLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_Internal_appendFieldLine___closed__0 = (const lean_object*)&l_Std_Http_Internal_appendFieldLine___closed__0_value;
static lean_once_cell_t l_Std_Http_Internal_appendFieldLine___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_appendFieldLine___closed__1;
static lean_once_cell_t l_Std_Http_Internal_appendFieldLine___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_appendFieldLine___closed__2;
static const lean_string_object l_Std_Http_Internal_appendFieldLine___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_Internal_appendFieldLine___closed__3 = (const lean_object*)&l_Std_Http_Internal_appendFieldLine___closed__3_value;
static lean_once_cell_t l_Std_Http_Internal_appendFieldLine___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_appendFieldLine___closed__4;
static lean_once_cell_t l_Std_Http_Internal_appendFieldLine___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Internal_appendFieldLine___closed__5;
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendFieldLine(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendFieldLine___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Std_Http_Internal_appendFieldLine___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_Std_Http_Internal_appendFieldLine___closed__0));
v___x_3_ = lean_string_to_utf8(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Std_Http_Internal_appendFieldLine___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_Std_Http_Internal_appendFieldLine___closed__1, &l_Std_Http_Internal_appendFieldLine___closed__1_once, _init_l_Std_Http_Internal_appendFieldLine___closed__1);
v___x_5_ = lean_byte_array_size(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Std_Http_Internal_appendFieldLine___closed__4(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = ((lean_object*)(l_Std_Http_Internal_appendFieldLine___closed__3));
v___x_8_ = lean_string_to_utf8(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Std_Http_Internal_appendFieldLine___closed__5(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l_Std_Http_Internal_appendFieldLine___closed__4, &l_Std_Http_Internal_appendFieldLine___closed__4_once, _init_l_Std_Http_Internal_appendFieldLine___closed__4);
v___x_10_ = lean_byte_array_size(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendFieldLine(lean_object* v_out_11_, lean_object* v_name_12_, lean_object* v_value_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = 1;
v___x_16_ = l_Std_Http_Header_Name_instEncodeV11_go(v_name_12_, v___x_14_, v___x_15_, v_out_11_);
v___x_17_ = lean_obj_once(&l_Std_Http_Internal_appendFieldLine___closed__1, &l_Std_Http_Internal_appendFieldLine___closed__1_once, _init_l_Std_Http_Internal_appendFieldLine___closed__1);
v___x_18_ = lean_byte_array_size(v___x_16_);
v___x_19_ = lean_obj_once(&l_Std_Http_Internal_appendFieldLine___closed__2, &l_Std_Http_Internal_appendFieldLine___closed__2_once, _init_l_Std_Http_Internal_appendFieldLine___closed__2);
v___x_20_ = 0;
v___x_21_ = lean_byte_array_copy_slice(v___x_17_, v___x_14_, v___x_16_, v___x_18_, v___x_19_, v___x_20_);
v___x_22_ = lean_string_to_utf8(v_value_13_);
v___x_23_ = lean_byte_array_size(v___x_21_);
v___x_24_ = lean_byte_array_size(v___x_22_);
v___x_25_ = lean_byte_array_copy_slice(v___x_22_, v___x_14_, v___x_21_, v___x_23_, v___x_24_, v___x_20_);
lean_dec_ref(v___x_22_);
v___x_26_ = lean_obj_once(&l_Std_Http_Internal_appendFieldLine___closed__4, &l_Std_Http_Internal_appendFieldLine___closed__4_once, _init_l_Std_Http_Internal_appendFieldLine___closed__4);
v___x_27_ = lean_byte_array_size(v___x_25_);
v___x_28_ = lean_obj_once(&l_Std_Http_Internal_appendFieldLine___closed__5, &l_Std_Http_Internal_appendFieldLine___closed__5_once, _init_l_Std_Http_Internal_appendFieldLine___closed__5);
v___x_29_ = lean_byte_array_copy_slice(v___x_26_, v___x_14_, v___x_25_, v___x_27_, v___x_28_, v___x_20_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Internal_appendFieldLine___boxed(lean_object* v_out_30_, lean_object* v_name_31_, lean_object* v_value_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_Http_Internal_appendFieldLine(v_out_30_, v_name_31_, v_value_32_);
lean_dec_ref(v_name_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(lean_object* v_h_34_, lean_object* v_out_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_serialize_37_; lean_object* v___x_38_; lean_object* v_fst_39_; lean_object* v_snd_40_; lean_object* v___x_41_; 
v_serialize_37_ = lean_ctor_get(v_h_34_, 1);
lean_inc_ref(v_serialize_37_);
lean_dec_ref(v_h_34_);
v___x_38_ = lean_apply_1(v_serialize_37_, v_a_36_);
v_fst_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_fst_39_);
v_snd_40_ = lean_ctor_get(v___x_38_, 1);
lean_inc(v_snd_40_);
lean_dec_ref(v___x_38_);
v___x_41_ = l_Std_Http_Internal_appendFieldLine(v_out_35_, v_fst_39_, v_snd_40_);
lean_dec(v_fst_39_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg(lean_object* v_h_42_){
_start:
{
lean_object* v___f_43_; 
v___f_43_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__0), 3, 1);
lean_closure_set(v___f_43_, 0, v_h_42_);
return v___f_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader(lean_object* v_00_u03b1_44_, lean_object* v_h_45_){
_start:
{
lean_object* v___f_46_; 
v___f_46_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__0), 3, 1);
lean_closure_set(v___f_46_, 0, v_h_45_);
return v___f_46_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg(){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___closed__0));
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___boxed(lean_object* v___dummy_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg();
return v_res_52_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0(void){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg();
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(lean_object* v_s_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(lean_object* v_s_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v_s_56_);
lean_dec_ref(v_s_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(lean_object* v_s_58_, lean_object* v_p_59_){
_start:
{
lean_object* v___y_61_; lean_object* v___y_62_; uint32_t v___y_66_; lean_object* v___x_78_; uint8_t v_decide_79_; 
v___x_78_ = lean_string_utf8_byte_size(v_s_58_);
v_decide_79_ = lean_nat_dec_eq(v_p_59_, v___x_78_);
if (v_decide_79_ == 0)
{
uint32_t v___x_80_; uint32_t v___x_81_; uint8_t v___x_82_; 
v___x_80_ = lean_string_utf8_get_fast(v_s_58_, v_p_59_);
v___x_81_ = 65;
v___x_82_ = lean_uint32_dec_le(v___x_81_, v___x_80_);
if (v___x_82_ == 0)
{
v___y_66_ = v___x_80_;
goto v___jp_65_;
}
else
{
uint32_t v___x_83_; uint8_t v___x_84_; 
v___x_83_ = 90;
v___x_84_ = lean_uint32_dec_le(v___x_80_, v___x_83_);
if (v___x_84_ == 0)
{
v___y_66_ = v___x_80_;
goto v___jp_65_;
}
else
{
uint32_t v___x_85_; uint32_t v___x_86_; 
v___x_85_ = 32;
v___x_86_ = lean_uint32_add(v___x_80_, v___x_85_);
v___y_66_ = v___x_86_;
goto v___jp_65_;
}
}
}
else
{
lean_dec(v_p_59_);
return v_s_58_;
}
v___jp_60_:
{
lean_object* v___x_63_; 
v___x_63_ = lean_nat_add(v_p_59_, v___y_62_);
lean_dec(v_p_59_);
v_s_58_ = v___y_61_;
v_p_59_ = v___x_63_;
goto _start;
}
v___jp_65_:
{
lean_object* v___x_67_; uint32_t v___x_68_; uint8_t v___x_69_; 
lean_inc(v_p_59_);
v___x_67_ = lean_string_utf8_set(v_s_58_, v_p_59_, v___y_66_);
v___x_68_ = 127;
v___x_69_ = lean_uint32_dec_le(v___y_66_, v___x_68_);
if (v___x_69_ == 0)
{
uint32_t v___x_70_; uint8_t v___x_71_; 
v___x_70_ = 2047;
v___x_71_ = lean_uint32_dec_le(v___y_66_, v___x_70_);
if (v___x_71_ == 0)
{
uint32_t v___x_72_; uint8_t v___x_73_; 
v___x_72_ = 65535;
v___x_73_ = lean_uint32_dec_le(v___y_66_, v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_74_; 
v___x_74_ = lean_unsigned_to_nat(4u);
v___y_61_ = v___x_67_;
v___y_62_ = v___x_74_;
goto v___jp_60_;
}
else
{
lean_object* v___x_75_; 
v___x_75_ = lean_unsigned_to_nat(3u);
v___y_61_ = v___x_67_;
v___y_62_ = v___x_75_;
goto v___jp_60_;
}
}
else
{
lean_object* v___x_76_; 
v___x_76_ = lean_unsigned_to_nat(2u);
v___y_61_ = v___x_67_;
v___y_62_ = v___x_76_;
goto v___jp_60_;
}
}
else
{
lean_object* v___x_77_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___y_61_ = v___x_67_;
v___y_62_ = v___x_77_;
goto v___jp_60_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t v_sz_87_, size_t v_i_88_, lean_object* v_bs_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = lean_usize_dec_lt(v_i_88_, v_sz_87_);
if (v___x_90_ == 0)
{
return v_bs_89_;
}
else
{
lean_object* v_v_91_; lean_object* v___x_92_; lean_object* v_bs_x27_93_; lean_object* v___x_94_; lean_object* v___x_95_; size_t v___x_96_; size_t v___x_97_; lean_object* v___x_98_; 
v_v_91_ = lean_array_uget(v_bs_89_, v_i_88_);
v___x_92_ = lean_unsigned_to_nat(0u);
v_bs_x27_93_ = lean_array_uset(v_bs_89_, v_i_88_, v___x_92_);
v___x_94_ = l_String_Slice_toString(v_v_91_);
lean_dec(v_v_91_);
v___x_95_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_94_, v___x_92_);
v___x_96_ = ((size_t)1ULL);
v___x_97_ = lean_usize_add(v_i_88_, v___x_96_);
v___x_98_ = lean_array_uset(v_bs_x27_93_, v_i_88_, v___x_95_);
v_i_88_ = v___x_97_;
v_bs_89_ = v___x_98_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(lean_object* v_sz_100_, lean_object* v_i_101_, lean_object* v_bs_102_){
_start:
{
size_t v_sz_boxed_103_; size_t v_i_boxed_104_; lean_object* v_res_105_; 
v_sz_boxed_103_ = lean_unbox_usize(v_sz_100_);
lean_dec(v_sz_100_);
v_i_boxed_104_ = lean_unbox_usize(v_i_101_);
lean_dec(v_i_101_);
v_res_105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_boxed_103_, v_i_boxed_104_, v_bs_102_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(lean_object* v___x_106_, lean_object* v___x_107_, lean_object* v___x_108_, lean_object* v_a_109_, lean_object* v_b_110_){
_start:
{
lean_object* v_it_112_; lean_object* v_startInclusive_113_; lean_object* v_endExclusive_114_; 
if (lean_obj_tag(v_a_109_) == 0)
{
lean_object* v_currPos_119_; lean_object* v_searcher_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_149_; 
v_currPos_119_ = lean_ctor_get(v_a_109_, 0);
v_searcher_120_ = lean_ctor_get(v_a_109_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_a_109_);
if (v_isSharedCheck_149_ == 0)
{
v___x_122_ = v_a_109_;
v_isShared_123_ = v_isSharedCheck_149_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_searcher_120_);
lean_inc(v_currPos_119_);
lean_dec(v_a_109_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_149_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v_str_124_; lean_object* v_startInclusive_125_; lean_object* v_endExclusive_126_; lean_object* v___x_127_; uint8_t v_decide_128_; 
v_str_124_ = lean_ctor_get(v___x_107_, 0);
v_startInclusive_125_ = lean_ctor_get(v___x_107_, 1);
v_endExclusive_126_ = lean_ctor_get(v___x_107_, 2);
v___x_127_ = lean_nat_sub(v_endExclusive_126_, v_startInclusive_125_);
v_decide_128_ = lean_nat_dec_eq(v_searcher_120_, v___x_127_);
lean_dec(v___x_127_);
if (v_decide_128_ == 0)
{
lean_object* v___x_129_; uint32_t v___x_130_; uint32_t v___x_131_; uint8_t v___x_132_; 
v___x_129_ = lean_nat_add(v_startInclusive_125_, v_searcher_120_);
v___x_130_ = lean_string_utf8_get_fast(v_str_124_, v___x_129_);
v___x_131_ = 44;
v___x_132_ = lean_uint32_dec_eq(v___x_130_, v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
lean_dec(v_searcher_120_);
v___x_133_ = lean_string_utf8_next_fast(v_str_124_, v___x_129_);
lean_dec(v___x_129_);
v___x_134_ = lean_nat_sub(v___x_133_, v_startInclusive_125_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_134_);
v___x_136_ = v___x_122_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_currPos_119_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_138_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
v_a_109_ = v___x_136_;
goto _start;
}
}
else
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v_slice_142_; lean_object* v_nextIt_144_; 
v___x_139_ = lean_string_utf8_next_fast(v_str_124_, v___x_129_);
v___x_140_ = lean_nat_sub(v___x_139_, v___x_129_);
lean_dec(v___x_129_);
v___x_141_ = lean_nat_add(v_searcher_120_, v___x_140_);
lean_dec(v___x_140_);
v_slice_142_ = l_String_Slice_subslice_x21(v___x_107_, v_currPos_119_, v_searcher_120_);
lean_inc(v___x_141_);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 1, v___x_141_);
lean_ctor_set(v___x_122_, 0, v___x_141_);
v_nextIt_144_ = v___x_122_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_141_);
v_nextIt_144_ = v_reuseFailAlloc_147_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
lean_object* v_startInclusive_145_; lean_object* v_endExclusive_146_; 
v_startInclusive_145_ = lean_ctor_get(v_slice_142_, 0);
lean_inc(v_startInclusive_145_);
v_endExclusive_146_ = lean_ctor_get(v_slice_142_, 1);
lean_inc(v_endExclusive_146_);
lean_dec_ref(v_slice_142_);
v_it_112_ = v_nextIt_144_;
v_startInclusive_113_ = v_startInclusive_145_;
v_endExclusive_114_ = v_endExclusive_146_;
goto v___jp_111_;
}
}
}
else
{
lean_object* v___x_148_; 
lean_del_object(v___x_122_);
lean_dec(v_searcher_120_);
v___x_148_ = lean_box(1);
lean_inc(v___x_108_);
v_it_112_ = v___x_148_;
v_startInclusive_113_ = v_currPos_119_;
v_endExclusive_114_ = v___x_108_;
goto v___jp_111_;
}
}
}
else
{
lean_dec(v___x_108_);
lean_dec_ref(v___x_106_);
return v_b_110_;
}
v___jp_111_:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
lean_inc_ref(v___x_106_);
v___x_115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_115_, 0, v___x_106_);
lean_ctor_set(v___x_115_, 1, v_startInclusive_113_);
lean_ctor_set(v___x_115_, 2, v_endExclusive_114_);
v___x_116_ = l_String_Slice_trimAscii(v___x_115_);
v___x_117_ = lean_array_push(v_b_110_, v___x_116_);
v_a_109_ = v_it_112_;
v_b_110_ = v___x_117_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(lean_object* v___x_150_, lean_object* v___x_151_, lean_object* v___x_152_, lean_object* v_a_153_, lean_object* v_b_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_150_, v___x_151_, v___x_152_, v_a_153_, v_b_154_);
lean_dec_ref(v___x_151_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(lean_object* v___x_156_, lean_object* v___x_157_, lean_object* v___x_158_, lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
lean_object* v_it_162_; lean_object* v_startInclusive_163_; lean_object* v_endExclusive_164_; 
if (lean_obj_tag(v_a_159_) == 0)
{
lean_object* v_currPos_169_; lean_object* v_searcher_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_199_; 
v_currPos_169_ = lean_ctor_get(v_a_159_, 0);
v_searcher_170_ = lean_ctor_get(v_a_159_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_a_159_);
if (v_isSharedCheck_199_ == 0)
{
v___x_172_ = v_a_159_;
v_isShared_173_ = v_isSharedCheck_199_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_searcher_170_);
lean_inc(v_currPos_169_);
lean_dec(v_a_159_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_199_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v_str_174_; lean_object* v_startInclusive_175_; lean_object* v_endExclusive_176_; lean_object* v___x_177_; uint8_t v_decide_178_; 
v_str_174_ = lean_ctor_get(v___x_157_, 0);
v_startInclusive_175_ = lean_ctor_get(v___x_157_, 1);
v_endExclusive_176_ = lean_ctor_get(v___x_157_, 2);
v___x_177_ = lean_nat_sub(v_endExclusive_176_, v_startInclusive_175_);
v_decide_178_ = lean_nat_dec_eq(v_searcher_170_, v___x_177_);
lean_dec(v___x_177_);
if (v_decide_178_ == 0)
{
lean_object* v___x_179_; uint32_t v___x_180_; uint32_t v___x_181_; uint8_t v___x_182_; 
v___x_179_ = lean_nat_add(v_startInclusive_175_, v_searcher_170_);
v___x_180_ = lean_string_utf8_get_fast(v_str_174_, v___x_179_);
v___x_181_ = 44;
v___x_182_ = lean_uint32_dec_eq(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec(v_searcher_170_);
v___x_183_ = lean_string_utf8_next_fast(v_str_174_, v___x_179_);
lean_dec(v___x_179_);
v___x_184_ = lean_nat_sub(v___x_183_, v_startInclusive_175_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_184_);
v___x_186_ = v___x_172_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_currPos_169_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_184_);
v___x_186_ = v_reuseFailAlloc_188_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_187_; 
v___x_187_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_156_, v___x_157_, v___x_158_, v___x_186_, v_b_160_);
return v___x_187_;
}
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v_slice_192_; lean_object* v_nextIt_194_; 
v___x_189_ = lean_string_utf8_next_fast(v_str_174_, v___x_179_);
v___x_190_ = lean_nat_sub(v___x_189_, v___x_179_);
lean_dec(v___x_179_);
v___x_191_ = lean_nat_add(v_searcher_170_, v___x_190_);
lean_dec(v___x_190_);
v_slice_192_ = l_String_Slice_subslice_x21(v___x_157_, v_currPos_169_, v_searcher_170_);
lean_inc(v___x_191_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 1, v___x_191_);
lean_ctor_set(v___x_172_, 0, v___x_191_);
v_nextIt_194_ = v___x_172_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_197_, 1, v___x_191_);
v_nextIt_194_ = v_reuseFailAlloc_197_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v_startInclusive_195_; lean_object* v_endExclusive_196_; 
v_startInclusive_195_ = lean_ctor_get(v_slice_192_, 0);
lean_inc(v_startInclusive_195_);
v_endExclusive_196_ = lean_ctor_get(v_slice_192_, 1);
lean_inc(v_endExclusive_196_);
lean_dec_ref(v_slice_192_);
v_it_162_ = v_nextIt_194_;
v_startInclusive_163_ = v_startInclusive_195_;
v_endExclusive_164_ = v_endExclusive_196_;
goto v___jp_161_;
}
}
}
else
{
lean_object* v___x_198_; 
lean_del_object(v___x_172_);
lean_dec(v_searcher_170_);
v___x_198_ = lean_box(1);
lean_inc(v___x_158_);
v_it_162_ = v___x_198_;
v_startInclusive_163_ = v_currPos_169_;
v_endExclusive_164_ = v___x_158_;
goto v___jp_161_;
}
}
}
else
{
lean_dec(v___x_158_);
lean_dec_ref(v___x_156_);
return v_b_160_;
}
v___jp_161_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_inc_ref(v___x_156_);
v___x_165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_165_, 0, v___x_156_);
lean_ctor_set(v___x_165_, 1, v_startInclusive_163_);
lean_ctor_set(v___x_165_, 2, v_endExclusive_164_);
v___x_166_ = l_String_Slice_trimAscii(v___x_165_);
v___x_167_ = lean_array_push(v_b_160_, v___x_166_);
v___x_168_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_156_, v___x_157_, v___x_158_, v_it_162_, v___x_167_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(lean_object* v___x_200_, lean_object* v___x_201_, lean_object* v___x_202_, lean_object* v_a_203_, lean_object* v_b_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_200_, v___x_201_, v___x_202_, v_a_203_, v_b_204_);
lean_dec_ref(v___x_201_);
return v_res_205_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object* v___x_206_, lean_object* v___x_207_, lean_object* v___x_208_, lean_object* v_a_209_, uint8_t v_b_210_){
_start:
{
if (lean_obj_tag(v_a_209_) == 0)
{
lean_object* v_currPos_211_; lean_object* v_searcher_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_255_; 
v_currPos_211_ = lean_ctor_get(v_a_209_, 0);
v_searcher_212_ = lean_ctor_get(v_a_209_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_a_209_);
if (v_isSharedCheck_255_ == 0)
{
v___x_214_ = v_a_209_;
v_isShared_215_ = v_isSharedCheck_255_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_searcher_212_);
lean_inc(v_currPos_211_);
lean_dec(v_a_209_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_255_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v_str_216_; lean_object* v_startInclusive_217_; lean_object* v_endExclusive_218_; uint8_t v___x_219_; lean_object* v_it_221_; lean_object* v_startInclusive_222_; lean_object* v_endExclusive_223_; lean_object* v___x_233_; uint8_t v_decide_234_; 
v_str_216_ = lean_ctor_get(v___x_207_, 0);
v_startInclusive_217_ = lean_ctor_get(v___x_207_, 1);
v_endExclusive_218_ = lean_ctor_get(v___x_207_, 2);
v___x_219_ = 1;
v___x_233_ = lean_nat_sub(v_endExclusive_218_, v_startInclusive_217_);
v_decide_234_ = lean_nat_dec_eq(v_searcher_212_, v___x_233_);
lean_dec(v___x_233_);
if (v_decide_234_ == 0)
{
lean_object* v___x_235_; uint32_t v___x_236_; uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_235_ = lean_nat_add(v_startInclusive_217_, v_searcher_212_);
v___x_236_ = lean_string_utf8_get_fast(v_str_216_, v___x_235_);
v___x_237_ = 44;
v___x_238_ = lean_uint32_dec_eq(v___x_236_, v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
lean_dec(v_searcher_212_);
v___x_239_ = lean_string_utf8_next_fast(v_str_216_, v___x_235_);
lean_dec(v___x_235_);
v___x_240_ = lean_nat_sub(v___x_239_, v_startInclusive_217_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_240_);
v___x_242_ = v___x_214_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_currPos_211_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_244_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
v_a_209_ = v___x_242_;
goto _start;
}
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v_slice_248_; lean_object* v_nextIt_250_; 
v___x_245_ = lean_string_utf8_next_fast(v_str_216_, v___x_235_);
v___x_246_ = lean_nat_sub(v___x_245_, v___x_235_);
lean_dec(v___x_235_);
v___x_247_ = lean_nat_add(v_searcher_212_, v___x_246_);
lean_dec(v___x_246_);
v_slice_248_ = l_String_Slice_subslice_x21(v___x_207_, v_currPos_211_, v_searcher_212_);
lean_inc(v___x_247_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 1, v___x_247_);
lean_ctor_set(v___x_214_, 0, v___x_247_);
v_nextIt_250_ = v___x_214_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_247_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_247_);
v_nextIt_250_ = v_reuseFailAlloc_253_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v_startInclusive_251_; lean_object* v_endExclusive_252_; 
v_startInclusive_251_ = lean_ctor_get(v_slice_248_, 0);
lean_inc(v_startInclusive_251_);
v_endExclusive_252_ = lean_ctor_get(v_slice_248_, 1);
lean_inc(v_endExclusive_252_);
lean_dec_ref(v_slice_248_);
v_it_221_ = v_nextIt_250_;
v_startInclusive_222_ = v_startInclusive_251_;
v_endExclusive_223_ = v_endExclusive_252_;
goto v___jp_220_;
}
}
}
else
{
lean_object* v___x_254_; 
lean_del_object(v___x_214_);
lean_dec(v_searcher_212_);
v___x_254_ = lean_box(1);
lean_inc(v___x_208_);
v_it_221_ = v___x_254_;
v_startInclusive_222_ = v_currPos_211_;
v_endExclusive_223_ = v___x_208_;
goto v___jp_220_;
}
v___jp_220_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_startInclusive_226_; lean_object* v_endExclusive_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
lean_inc_ref(v___x_206_);
v___x_224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_224_, 0, v___x_206_);
lean_ctor_set(v___x_224_, 1, v_startInclusive_222_);
lean_ctor_set(v___x_224_, 2, v_endExclusive_223_);
v___x_225_ = l_String_Slice_trimAscii(v___x_224_);
v_startInclusive_226_ = lean_ctor_get(v___x_225_, 1);
lean_inc(v_startInclusive_226_);
v_endExclusive_227_ = lean_ctor_get(v___x_225_, 2);
lean_inc(v_endExclusive_227_);
lean_dec_ref(v___x_225_);
v___x_228_ = lean_nat_sub(v_endExclusive_227_, v_startInclusive_226_);
lean_dec(v_startInclusive_226_);
lean_dec(v_endExclusive_227_);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_nat_dec_eq(v___x_228_, v___x_229_);
lean_dec(v___x_228_);
if (v___x_230_ == 0)
{
v_a_209_ = v_it_221_;
v_b_210_ = v___x_219_;
goto _start;
}
else
{
uint8_t v___x_232_; 
lean_dec(v_it_221_);
lean_dec(v___x_208_);
lean_dec_ref(v___x_206_);
v___x_232_ = 0;
return v___x_232_;
}
}
}
}
else
{
lean_dec(v___x_208_);
lean_dec_ref(v___x_206_);
return v_b_210_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object* v___x_256_, lean_object* v___x_257_, lean_object* v___x_258_, lean_object* v_a_259_, lean_object* v_b_260_){
_start:
{
uint8_t v_b_boxed_261_; uint8_t v_res_262_; lean_object* v_r_263_; 
v_b_boxed_261_ = lean_unbox(v_b_260_);
v_res_262_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_256_, v___x_257_, v___x_258_, v_a_259_, v_b_boxed_261_);
lean_dec_ref(v___x_257_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object* v___x_264_, lean_object* v___x_265_, lean_object* v___x_266_, lean_object* v_a_267_, uint8_t v_b_268_){
_start:
{
if (lean_obj_tag(v_a_267_) == 0)
{
lean_object* v_currPos_269_; lean_object* v_searcher_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_313_; 
v_currPos_269_ = lean_ctor_get(v_a_267_, 0);
v_searcher_270_ = lean_ctor_get(v_a_267_, 1);
v_isSharedCheck_313_ = !lean_is_exclusive(v_a_267_);
if (v_isSharedCheck_313_ == 0)
{
v___x_272_ = v_a_267_;
v_isShared_273_ = v_isSharedCheck_313_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_searcher_270_);
lean_inc(v_currPos_269_);
lean_dec(v_a_267_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_313_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v_str_274_; lean_object* v_startInclusive_275_; lean_object* v_endExclusive_276_; uint8_t v___x_277_; lean_object* v_it_279_; lean_object* v_startInclusive_280_; lean_object* v_endExclusive_281_; lean_object* v___x_291_; uint8_t v_decide_292_; 
v_str_274_ = lean_ctor_get(v___x_265_, 0);
v_startInclusive_275_ = lean_ctor_get(v___x_265_, 1);
v_endExclusive_276_ = lean_ctor_get(v___x_265_, 2);
v___x_277_ = 1;
v___x_291_ = lean_nat_sub(v_endExclusive_276_, v_startInclusive_275_);
v_decide_292_ = lean_nat_dec_eq(v_searcher_270_, v___x_291_);
lean_dec(v___x_291_);
if (v_decide_292_ == 0)
{
lean_object* v___x_293_; uint32_t v___x_294_; uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_293_ = lean_nat_add(v_startInclusive_275_, v_searcher_270_);
v___x_294_ = lean_string_utf8_get_fast(v_str_274_, v___x_293_);
v___x_295_ = 44;
v___x_296_ = lean_uint32_dec_eq(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
lean_dec(v_searcher_270_);
v___x_297_ = lean_string_utf8_next_fast(v_str_274_, v___x_293_);
lean_dec(v___x_293_);
v___x_298_ = lean_nat_sub(v___x_297_, v_startInclusive_275_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___x_298_);
v___x_300_ = v___x_272_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_currPos_269_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v___x_298_);
v___x_300_ = v_reuseFailAlloc_302_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
uint8_t v___x_301_; 
v___x_301_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_264_, v___x_265_, v___x_266_, v___x_300_, v_b_268_);
return v___x_301_;
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_slice_306_; lean_object* v_nextIt_308_; 
v___x_303_ = lean_string_utf8_next_fast(v_str_274_, v___x_293_);
v___x_304_ = lean_nat_sub(v___x_303_, v___x_293_);
lean_dec(v___x_293_);
v___x_305_ = lean_nat_add(v_searcher_270_, v___x_304_);
lean_dec(v___x_304_);
v_slice_306_ = l_String_Slice_subslice_x21(v___x_265_, v_currPos_269_, v_searcher_270_);
lean_inc(v___x_305_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 1, v___x_305_);
lean_ctor_set(v___x_272_, 0, v___x_305_);
v_nextIt_308_ = v___x_272_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_305_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_305_);
v_nextIt_308_ = v_reuseFailAlloc_311_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v_startInclusive_309_; lean_object* v_endExclusive_310_; 
v_startInclusive_309_ = lean_ctor_get(v_slice_306_, 0);
lean_inc(v_startInclusive_309_);
v_endExclusive_310_ = lean_ctor_get(v_slice_306_, 1);
lean_inc(v_endExclusive_310_);
lean_dec_ref(v_slice_306_);
v_it_279_ = v_nextIt_308_;
v_startInclusive_280_ = v_startInclusive_309_;
v_endExclusive_281_ = v_endExclusive_310_;
goto v___jp_278_;
}
}
}
else
{
lean_object* v___x_312_; 
lean_del_object(v___x_272_);
lean_dec(v_searcher_270_);
v___x_312_ = lean_box(1);
lean_inc(v___x_266_);
v_it_279_ = v___x_312_;
v_startInclusive_280_ = v_currPos_269_;
v_endExclusive_281_ = v___x_266_;
goto v___jp_278_;
}
v___jp_278_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v_startInclusive_284_; lean_object* v_endExclusive_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; 
lean_inc_ref(v___x_264_);
v___x_282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_282_, 0, v___x_264_);
lean_ctor_set(v___x_282_, 1, v_startInclusive_280_);
lean_ctor_set(v___x_282_, 2, v_endExclusive_281_);
v___x_283_ = l_String_Slice_trimAscii(v___x_282_);
v_startInclusive_284_ = lean_ctor_get(v___x_283_, 1);
lean_inc(v_startInclusive_284_);
v_endExclusive_285_ = lean_ctor_get(v___x_283_, 2);
lean_inc(v_endExclusive_285_);
lean_dec_ref(v___x_283_);
v___x_286_ = lean_nat_sub(v_endExclusive_285_, v_startInclusive_284_);
lean_dec(v_startInclusive_284_);
lean_dec(v_endExclusive_285_);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_nat_dec_eq(v___x_286_, v___x_287_);
lean_dec(v___x_286_);
if (v___x_288_ == 0)
{
uint8_t v___x_289_; 
v___x_289_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_264_, v___x_265_, v___x_266_, v_it_279_, v___x_277_);
return v___x_289_;
}
else
{
uint8_t v___x_290_; 
lean_dec(v_it_279_);
lean_dec(v___x_266_);
lean_dec_ref(v___x_264_);
v___x_290_ = 0;
return v___x_290_;
}
}
}
}
else
{
lean_dec(v___x_266_);
lean_dec_ref(v___x_264_);
return v_b_268_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object* v___x_314_, lean_object* v___x_315_, lean_object* v___x_316_, lean_object* v_a_317_, lean_object* v_b_318_){
_start:
{
uint8_t v_b_boxed_319_; uint8_t v_res_320_; lean_object* v_r_321_; 
v_b_boxed_319_ = lean_unbox(v_b_318_);
v_res_320_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_314_, v___x_315_, v___x_316_, v_a_317_, v_b_boxed_319_);
lean_dec_ref(v___x_315_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object* v_v_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v_parts_328_; uint8_t v___x_329_; uint8_t v___x_330_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_string_utf8_byte_size(v_v_324_);
lean_inc_ref_n(v_v_324_, 2);
v___x_327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_327_, 0, v_v_324_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
lean_ctor_set(v___x_327_, 2, v___x_326_);
v_parts_328_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
v___x_329_ = 1;
v___x_330_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_324_, v___x_327_, v___x_326_, v_parts_328_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec_ref_known(v___x_327_, 3);
lean_dec_ref(v_v_324_);
v___x_331_ = lean_box(0);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; size_t v_sz_334_; size_t v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_332_ = ((lean_object*)(l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0));
v___x_333_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v_v_324_, v___x_327_, v___x_326_, v_parts_328_, v___x_332_);
lean_dec_ref_known(v___x_327_, 3);
v_sz_334_ = lean_array_size(v___x_333_);
v___x_335_ = ((size_t)0ULL);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_334_, v___x_335_, v___x_333_);
v___x_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object* v___x_338_, lean_object* v___x_339_, lean_object* v___x_340_, lean_object* v_inst_341_, lean_object* v_R_342_, lean_object* v_a_343_, uint8_t v_b_344_, lean_object* v_c_345_){
_start:
{
uint8_t v___x_346_; 
v___x_346_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_338_, v___x_339_, v___x_340_, v_a_343_, v_b_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object* v___x_347_, lean_object* v___x_348_, lean_object* v___x_349_, lean_object* v_inst_350_, lean_object* v_R_351_, lean_object* v_a_352_, lean_object* v_b_353_, lean_object* v_c_354_){
_start:
{
uint8_t v_b_boxed_355_; uint8_t v_res_356_; lean_object* v_r_357_; 
v_b_boxed_355_ = lean_unbox(v_b_353_);
v_res_356_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_347_, v___x_348_, v___x_349_, v_inst_350_, v_R_351_, v_a_352_, v_b_boxed_355_, v_c_354_);
lean_dec_ref(v___x_348_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object* v___x_358_, lean_object* v___x_359_, lean_object* v___x_360_, lean_object* v_inst_361_, lean_object* v_R_362_, lean_object* v_a_363_, lean_object* v_b_364_){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_358_, v___x_359_, v___x_360_, v_a_363_, v_b_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object* v___x_366_, lean_object* v___x_367_, lean_object* v___x_368_, lean_object* v_inst_369_, lean_object* v_R_370_, lean_object* v_a_371_, lean_object* v_b_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_366_, v___x_367_, v___x_368_, v_inst_369_, v_R_370_, v_a_371_, v_b_372_);
lean_dec_ref(v___x_367_);
return v_res_373_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object* v___x_374_, lean_object* v___x_375_, lean_object* v___x_376_, lean_object* v_inst_377_, lean_object* v_R_378_, lean_object* v_a_379_, uint8_t v_b_380_, lean_object* v_c_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_374_, v___x_375_, v___x_376_, v_a_379_, v_b_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object* v___x_383_, lean_object* v___x_384_, lean_object* v___x_385_, lean_object* v_inst_386_, lean_object* v_R_387_, lean_object* v_a_388_, lean_object* v_b_389_, lean_object* v_c_390_){
_start:
{
uint8_t v_b_boxed_391_; uint8_t v_res_392_; lean_object* v_r_393_; 
v_b_boxed_391_ = lean_unbox(v_b_389_);
v_res_392_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_383_, v___x_384_, v___x_385_, v_inst_386_, v_R_387_, v_a_388_, v_b_boxed_391_, v_c_390_);
lean_dec_ref(v___x_384_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object* v___x_394_, lean_object* v___x_395_, lean_object* v___x_396_, lean_object* v_inst_397_, lean_object* v_R_398_, lean_object* v_a_399_, lean_object* v_b_400_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_394_, v___x_395_, v___x_396_, v_a_399_, v_b_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object* v___x_402_, lean_object* v___x_403_, lean_object* v___x_404_, lean_object* v_inst_405_, lean_object* v_R_406_, lean_object* v_a_407_, lean_object* v_b_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(v___x_402_, v___x_403_, v___x_404_, v_inst_405_, v_R_406_, v_a_407_, v_b_408_);
lean_dec_ref(v___x_403_);
return v_res_409_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqContentLength_beq(lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
uint8_t v___x_412_; 
v___x_412_ = lean_nat_dec_eq(v_x_410_, v_x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqContentLength_beq___boxed(lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
uint8_t v_res_415_; lean_object* v_r_416_; 
v_res_415_ = l_Std_Http_Header_instBEqContentLength_beq(v_x_413_, v_x_414_);
lean_dec(v_x_414_);
lean_dec(v_x_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprContentLength_repr_spec__0(lean_object* v_a_419_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_nat_to_int(v_a_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_unsigned_to_nat(10u);
v___x_435_ = lean_nat_to_int(v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0));
v___x_438_ = lean_string_length(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9);
v___x_440_ = lean_nat_to_int(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg(lean_object* v_x_445_){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_446_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6));
v___x_447_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_448_ = l_Nat_reprFast(v_x_445_);
v___x_449_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
v___x_450_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_447_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = 0;
v___x_452_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set_uint8(v___x_452_, sizeof(void*)*1, v___x_451_);
v___x_453_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_446_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_455_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
lean_ctor_set(v___x_456_, 1, v___x_453_);
v___x_457_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_456_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_454_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
v___x_460_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set_uint8(v___x_460_, sizeof(void*)*1, v___x_451_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr(lean_object* v_x_461_, lean_object* v_prec_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_Http_Header_instReprContentLength_repr___redArg(v_x_461_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___boxed(lean_object* v_x_464_, lean_object* v_prec_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_Http_Header_instReprContentLength_repr(v_x_464_, v_prec_465_);
lean_dec(v_prec_465_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(lean_object* v_s_469_, lean_object* v_pos_470_){
_start:
{
lean_object* v_str_471_; lean_object* v_startInclusive_472_; lean_object* v_endExclusive_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v_decide_477_; 
v_str_471_ = lean_ctor_get(v_s_469_, 0);
v_startInclusive_472_ = lean_ctor_get(v_s_469_, 1);
v_endExclusive_473_ = lean_ctor_get(v_s_469_, 2);
v___x_474_ = lean_nat_add(v_startInclusive_472_, v_pos_470_);
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = lean_nat_sub(v_endExclusive_473_, v___x_474_);
v_decide_477_ = lean_nat_dec_eq(v___x_475_, v___x_476_);
lean_dec(v___x_476_);
if (v_decide_477_ == 0)
{
uint32_t v___x_478_; uint32_t v___x_479_; uint8_t v___x_480_; 
v___x_478_ = lean_string_utf8_get_fast(v_str_471_, v___x_474_);
v___x_479_ = 48;
v___x_480_ = lean_uint32_dec_le(v___x_479_, v___x_478_);
if (v___x_480_ == 0)
{
lean_dec(v___x_474_);
return v_pos_470_;
}
else
{
uint32_t v___x_481_; uint8_t v___x_482_; 
v___x_481_ = 57;
v___x_482_ = lean_uint32_dec_le(v___x_478_, v___x_481_);
if (v___x_482_ == 0)
{
lean_dec(v___x_474_);
return v_pos_470_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_483_ = lean_string_utf8_next_fast(v_str_471_, v___x_474_);
v___x_484_ = lean_nat_sub(v___x_483_, v___x_474_);
lean_dec(v___x_474_);
v___x_485_ = lean_nat_add(v_pos_470_, v___x_484_);
lean_dec(v___x_484_);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_pos_470_, v___x_486_);
v___x_488_ = lean_nat_dec_le(v___x_487_, v___x_485_);
lean_dec(v___x_487_);
if (v___x_488_ == 0)
{
lean_dec(v___x_485_);
return v_pos_470_;
}
else
{
lean_dec(v_pos_470_);
v_pos_470_ = v___x_485_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_474_);
return v_pos_470_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0___boxed(lean_object* v_s_490_, lean_object* v_pos_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v_s_490_, v_pos_491_);
lean_dec_ref(v_s_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_parse(lean_object* v_v_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_494_ = lean_string_utf8_byte_size(v_v_493_);
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_nat_dec_eq(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v_decide_499_; 
v___x_497_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_497_, 0, v_v_493_);
lean_ctor_set(v___x_497_, 1, v___x_495_);
lean_ctor_set(v___x_497_, 2, v___x_494_);
v___x_498_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v___x_497_, v___x_495_);
v_decide_499_ = lean_nat_dec_eq(v___x_498_, v___x_494_);
lean_dec(v___x_498_);
if (v_decide_499_ == 0)
{
lean_object* v___x_500_; 
lean_dec_ref_known(v___x_497_, 3);
v___x_500_ = lean_box(0);
return v___x_500_;
}
else
{
lean_object* v___x_501_; 
v___x_501_ = l_String_Slice_toNat_x3f(v___x_497_);
lean_dec_ref_known(v___x_497_, 3);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_box(0);
return v___x_502_;
}
else
{
lean_object* v_val_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
v_val_503_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_501_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_val_503_);
lean_dec(v___x_501_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_val_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
else
{
lean_object* v___x_511_; 
lean_dec_ref(v_v_493_);
v___x_511_ = lean_box(0);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_serialize(lean_object* v_h_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_513_ = l_Std_Http_Header_Name_contentLength;
v___x_514_ = l_Nat_reprFast(v_h_512_);
v___x_515_ = l_Std_Http_Header_Value_ofString_x21(v___x_514_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_513_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
if (lean_obj_tag(v_x_523_) == 0)
{
if (lean_obj_tag(v_x_524_) == 0)
{
uint8_t v___x_525_; 
v___x_525_ = 1;
return v___x_525_;
}
else
{
uint8_t v___x_526_; 
v___x_526_ = 0;
return v___x_526_;
}
}
else
{
if (lean_obj_tag(v_x_524_) == 0)
{
uint8_t v___x_527_; 
v___x_527_ = 0;
return v___x_527_;
}
else
{
lean_object* v_val_528_; lean_object* v_val_529_; uint8_t v___x_530_; 
v_val_528_ = lean_ctor_get(v_x_523_, 0);
v_val_529_ = lean_ctor_get(v_x_524_, 0);
v___x_530_ = lean_string_dec_eq(v_val_528_, v_val_529_);
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
uint8_t v_res_533_; lean_object* v_r_534_; 
v_res_533_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_531_, v_x_532_);
lean_dec(v_x_532_);
lean_dec(v_x_531_);
v_r_534_ = lean_box(v_res_533_);
return v_r_534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object* v_as_536_, size_t v_i_537_, size_t v_stop_538_, lean_object* v_b_539_){
_start:
{
lean_object* v___y_541_; uint8_t v___x_545_; 
v___x_545_ = lean_usize_dec_eq(v_i_537_, v_stop_538_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_546_ = lean_array_uget_borrowed(v_as_536_, v_i_537_);
v___x_547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_548_ = lean_string_dec_eq(v___x_546_, v___x_547_);
if (v___x_548_ == 0)
{
v___y_541_ = v_b_539_;
goto v___jp_540_;
}
else
{
lean_object* v___x_549_; 
lean_inc(v___x_546_);
v___x_549_ = lean_array_push(v_b_539_, v___x_546_);
v___y_541_ = v___x_549_;
goto v___jp_540_;
}
}
else
{
return v_b_539_;
}
v___jp_540_:
{
size_t v___x_542_; size_t v___x_543_; 
v___x_542_ = ((size_t)1ULL);
v___x_543_ = lean_usize_add(v_i_537_, v___x_542_);
v_i_537_ = v___x_543_;
v_b_539_ = v___y_541_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object* v_as_550_, lean_object* v_i_551_, lean_object* v_stop_552_, lean_object* v_b_553_){
_start:
{
size_t v_i_boxed_554_; size_t v_stop_boxed_555_; lean_object* v_res_556_; 
v_i_boxed_554_ = lean_unbox_usize(v_i_551_);
lean_dec(v_i_551_);
v_stop_boxed_555_ = lean_unbox_usize(v_stop_552_);
lean_dec(v_stop_552_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_550_, v_i_boxed_554_, v_stop_boxed_555_, v_b_553_);
lean_dec_ref(v_as_550_);
return v_res_556_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object* v___x_557_, lean_object* v_as_558_, size_t v_i_559_, size_t v_stop_560_){
_start:
{
uint8_t v___x_561_; 
v___x_561_ = lean_usize_dec_eq(v_i_559_, v_stop_560_);
if (v___x_561_ == 0)
{
uint8_t v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_562_ = 1;
v___x_563_ = lean_array_uget_borrowed(v_as_558_, v_i_559_);
lean_inc(v___x_563_);
v___x_564_ = l_Std_Http_Internal_isToken(v___x_563_);
if (v___x_564_ == 0)
{
return v___x_562_;
}
else
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_nat_dec_eq(v___x_557_, v___x_565_);
if (v___x_566_ == 0)
{
size_t v___x_567_; size_t v___x_568_; 
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_add(v_i_559_, v___x_567_);
v_i_559_ = v___x_568_;
goto _start;
}
else
{
return v___x_562_;
}
}
}
else
{
uint8_t v___x_570_; 
v___x_570_ = 0;
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object* v___x_571_, lean_object* v_as_572_, lean_object* v_i_573_, lean_object* v_stop_574_){
_start:
{
size_t v_i_boxed_575_; size_t v_stop_boxed_576_; uint8_t v_res_577_; lean_object* v_r_578_; 
v_i_boxed_575_ = lean_unbox_usize(v_i_573_);
lean_dec(v_i_573_);
v_stop_boxed_576_ = lean_unbox_usize(v_stop_574_);
lean_dec(v_stop_574_);
v_res_577_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_571_, v_as_572_, v_i_boxed_575_, v_stop_boxed_576_);
lean_dec_ref(v_as_572_);
lean_dec(v___x_571_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object* v_codings_583_){
_start:
{
lean_object* v___y_585_; uint8_t v___y_586_; uint8_t v___y_587_; lean_object* v___y_588_; uint8_t v___y_595_; uint8_t v___y_596_; lean_object* v___y_597_; uint8_t v___y_607_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_616_ = lean_array_get_size(v_codings_583_);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = lean_nat_dec_eq(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
uint8_t v___x_619_; 
v___x_619_ = lean_nat_dec_lt(v___x_617_, v___x_616_);
if (v___x_619_ == 0)
{
v___y_607_ = v___x_619_;
goto v___jp_606_;
}
else
{
if (v___x_619_ == 0)
{
v___y_607_ = v___x_619_;
goto v___jp_606_;
}
else
{
size_t v___x_620_; size_t v___x_621_; uint8_t v___x_622_; 
v___x_620_ = ((size_t)0ULL);
v___x_621_ = lean_usize_of_nat(v___x_616_);
v___x_622_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_616_, v_codings_583_, v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
v___y_607_ = v___x_622_;
goto v___jp_606_;
}
else
{
return v___x_618_;
}
}
}
}
else
{
uint8_t v___x_623_; 
v___x_623_ = 0;
return v___x_623_;
}
v___jp_584_:
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(1u);
v___x_590_ = lean_nat_dec_lt(v___x_589_, v___y_585_);
if (v___x_590_ == 0)
{
uint8_t v___x_591_; 
v___x_591_ = lean_nat_dec_eq(v___y_585_, v___x_589_);
lean_dec(v___y_585_);
if (v___x_591_ == 0)
{
lean_dec(v___y_588_);
return v___y_586_;
}
else
{
lean_object* v___x_592_; uint8_t v_lastIsChunked_593_; 
v___x_592_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v_lastIsChunked_593_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_588_, v___x_592_);
lean_dec(v___y_588_);
if (v_lastIsChunked_593_ == 0)
{
return v___x_590_;
}
else
{
return v___y_586_;
}
}
}
else
{
lean_dec(v___y_588_);
lean_dec(v___y_585_);
return v___y_587_;
}
}
v___jp_594_:
{
lean_object* v_chunkedCount_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_chunkedCount_598_ = lean_array_get_size(v___y_597_);
lean_dec_ref(v___y_597_);
v___x_599_ = lean_array_get_size(v_codings_583_);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_sub(v___x_599_, v___x_600_);
v___x_602_ = lean_nat_dec_lt(v___x_601_, v___x_599_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
lean_dec(v___x_601_);
v___x_603_ = lean_box(0);
v___y_585_ = v_chunkedCount_598_;
v___y_586_ = v___y_595_;
v___y_587_ = v___y_596_;
v___y_588_ = v___x_603_;
goto v___jp_584_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_array_fget_borrowed(v_codings_583_, v___x_601_);
lean_dec(v___x_601_);
lean_inc(v___x_604_);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___y_585_ = v_chunkedCount_598_;
v___y_586_ = v___y_595_;
v___y_587_ = v___y_596_;
v___y_588_ = v___x_605_;
goto v___jp_584_;
}
}
v___jp_606_:
{
uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_608_ = 1;
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_array_get_size(v_codings_583_);
v___x_611_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__1));
v___x_612_ = lean_nat_dec_lt(v___x_609_, v___x_610_);
if (v___x_612_ == 0)
{
v___y_595_ = v___x_608_;
v___y_596_ = v___y_607_;
v___y_597_ = v___x_611_;
goto v___jp_594_;
}
else
{
size_t v___x_613_; size_t v___x_614_; lean_object* v___x_615_; 
v___x_613_ = ((size_t)0ULL);
v___x_614_ = lean_usize_of_nat(v___x_610_);
v___x_615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_583_, v___x_613_, v___x_614_, v___x_611_);
v___y_595_ = v___x_608_;
v___y_596_ = v___y_607_;
v___y_597_ = v___x_615_;
goto v___jp_594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_Validate___boxed(lean_object* v_codings_624_){
_start:
{
uint8_t v_res_625_; lean_object* v_r_626_; 
v_res_625_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_624_);
lean_dec_ref(v_codings_624_);
v_r_626_ = lean_box(v_res_625_);
return v_r_626_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(lean_object* v___y_627_){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = l_String_quote(v___y_627_);
v___x_629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_dec(v_x_630_);
return v_x_631_;
}
else
{
lean_object* v_head_633_; lean_object* v_tail_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
v_head_633_ = lean_ctor_get(v_x_632_, 0);
v_tail_634_ = lean_ctor_get(v_x_632_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_645_ == 0)
{
v___x_636_ = v_x_632_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_tail_634_);
lean_inc(v_head_633_);
lean_dec(v_x_632_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
lean_inc(v_x_630_);
if (v_isShared_637_ == 0)
{
lean_ctor_set_tag(v___x_636_, 5);
lean_ctor_set(v___x_636_, 1, v_x_630_);
lean_ctor_set(v___x_636_, 0, v_x_631_);
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_x_631_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_x_630_);
v___x_639_ = v_reuseFailAlloc_644_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = l_String_quote(v_head_633_);
v___x_641_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
v___x_642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_639_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v_x_631_ = v___x_642_;
v_x_632_ = v_tail_634_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
lean_dec(v_x_646_);
return v_x_647_;
}
else
{
lean_object* v_head_649_; lean_object* v_tail_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_661_; 
v_head_649_ = lean_ctor_get(v_x_648_, 0);
v_tail_650_ = lean_ctor_get(v_x_648_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_648_);
if (v_isSharedCheck_661_ == 0)
{
v___x_652_ = v_x_648_;
v_isShared_653_ = v_isSharedCheck_661_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_tail_650_);
lean_inc(v_head_649_);
lean_dec(v_x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_661_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
lean_inc(v_x_646_);
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 5);
lean_ctor_set(v___x_652_, 1, v_x_646_);
lean_ctor_set(v___x_652_, 0, v_x_647_);
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_x_647_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_x_646_);
v___x_655_ = v_reuseFailAlloc_660_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_656_ = l_String_quote(v_head_649_);
v___x_657_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
v___x_658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_655_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(v_x_646_, v___x_658_, v_tail_650_);
return v___x_659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(lean_object* v_x_662_, lean_object* v_x_663_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
lean_object* v___x_664_; 
lean_dec(v_x_663_);
v___x_664_ = lean_box(0);
return v___x_664_;
}
else
{
lean_object* v_tail_665_; 
v_tail_665_ = lean_ctor_get(v_x_662_, 1);
if (lean_obj_tag(v_tail_665_) == 0)
{
lean_object* v_head_666_; lean_object* v___x_667_; 
lean_dec(v_x_663_);
v_head_666_ = lean_ctor_get(v_x_662_, 0);
lean_inc(v_head_666_);
lean_dec_ref_known(v_x_662_, 2);
v___x_667_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_666_);
return v___x_667_;
}
else
{
lean_object* v_head_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
lean_inc(v_tail_665_);
v_head_668_ = lean_ctor_get(v_x_662_, 0);
lean_inc(v_head_668_);
lean_dec_ref_known(v_x_662_, 2);
v___x_669_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_668_);
v___x_670_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(v_x_663_, v___x_669_, v_tail_665_);
return v___x_670_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0));
v___x_680_ = lean_string_length(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5);
v___x_682_ = lean_nat_to_int(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(lean_object* v_xs_690_){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_691_ = lean_array_get_size(v_xs_690_);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_nat_dec_eq(v___x_691_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_694_ = lean_array_to_list(v_xs_690_);
v___x_695_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3));
v___x_696_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(v___x_694_, v___x_695_);
v___x_697_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6);
v___x_698_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7));
v___x_699_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
lean_ctor_set(v___x_699_, 1, v___x_696_);
v___x_700_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8));
v___x_701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_697_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = l_Std_Format_fill(v___x_702_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
lean_dec_ref(v_xs_690_);
v___x_704_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10));
return v___x_704_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_unsigned_to_nat(11u);
v___x_715_ = lean_nat_to_int(v___x_714_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg(lean_object* v_x_722_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_723_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_724_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3));
v___x_725_ = lean_obj_once(&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4, &l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4);
v___x_726_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_722_);
v___x_727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = 0;
v___x_729_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*1, v___x_728_);
v___x_730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_724_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_730_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = lean_box(1);
v___x_734_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_732_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6));
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_723_);
v___x_738_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_737_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_741_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_742_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___x_739_);
v___x_743_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_740_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set_uint8(v___x_746_, sizeof(void*)*1, v___x_728_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr(lean_object* v_x_747_, lean_object* v_prec_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg(v_x_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___boxed(lean_object* v_x_750_, lean_object* v_prec_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Std_Http_Header_instReprTransferEncoding_repr(v_x_750_, v_prec_751_);
lean_dec(v_prec_751_);
return v_res_752_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object* v_te_755_){
_start:
{
lean_object* v___y_757_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_760_ = lean_array_get_size(v_te_755_);
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_sub(v___x_760_, v___x_761_);
v___x_763_ = lean_nat_dec_lt(v___x_762_, v___x_760_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
lean_dec(v___x_762_);
v___x_764_ = lean_box(0);
v___y_757_ = v___x_764_;
goto v___jp_756_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_array_fget_borrowed(v_te_755_, v___x_762_);
lean_dec(v___x_762_);
lean_inc(v___x_765_);
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
v___y_757_ = v___x_766_;
goto v___jp_756_;
}
v___jp_756_:
{
lean_object* v___x_758_; uint8_t v___x_759_; 
v___x_758_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v___x_759_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_757_, v___x_758_);
lean_dec(v___y_757_);
return v___x_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_isChunked___boxed(lean_object* v_te_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_767_);
lean_dec_ref(v_te_767_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object* v_v_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_770_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___x_772_; 
v___x_772_ = lean_box(0);
return v___x_772_;
}
else
{
lean_object* v_val_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_782_; 
v_val_773_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_782_ == 0)
{
v___x_775_ = v___x_771_;
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_val_773_);
lean_dec(v___x_771_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
uint8_t v___x_777_; 
v___x_777_ = l_Std_Http_Header_TransferEncoding_Validate(v_val_773_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
lean_del_object(v___x_775_);
lean_dec(v_val_773_);
v___x_778_ = lean_box(0);
return v___x_778_;
}
else
{
lean_object* v___x_780_; 
if (v_isShared_776_ == 0)
{
v___x_780_ = v___x_775_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_val_773_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_serialize(lean_object* v_te_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_value_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_784_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_785_ = lean_array_to_list(v_te_783_);
v_value_786_ = l_String_intercalate(v___x_784_, v___x_785_);
v___x_787_ = l_Std_Http_Header_Name_transferEncoding;
v___x_788_ = l_Std_Http_Header_Value_ofString_x21(v_value_786_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___redArg(lean_object* v_x_808_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_809_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_810_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__3));
v___x_811_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
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
v___x_821_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__5));
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
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr(lean_object* v_x_833_, lean_object* v_prec_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_Http_Header_instReprConnection_repr___redArg(v_x_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___boxed(lean_object* v_x_836_, lean_object* v_prec_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_Http_Header_instReprConnection_repr(v_x_836_, v_prec_837_);
lean_dec(v_prec_837_);
return v_res_838_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(lean_object* v_token_841_, lean_object* v_as_842_, size_t v_i_843_, size_t v_stop_844_){
_start:
{
uint8_t v___x_845_; 
v___x_845_ = lean_usize_dec_eq(v_i_843_, v_stop_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = lean_array_uget_borrowed(v_as_842_, v_i_843_);
v___x_847_ = lean_string_dec_eq(v___x_846_, v_token_841_);
if (v___x_847_ == 0)
{
size_t v___x_848_; size_t v___x_849_; 
v___x_848_ = ((size_t)1ULL);
v___x_849_ = lean_usize_add(v_i_843_, v___x_848_);
v_i_843_ = v___x_849_;
goto _start;
}
else
{
return v___x_847_;
}
}
else
{
uint8_t v___x_851_; 
v___x_851_ = 0;
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(lean_object* v_token_852_, lean_object* v_as_853_, lean_object* v_i_854_, lean_object* v_stop_855_){
_start:
{
size_t v_i_boxed_856_; size_t v_stop_boxed_857_; uint8_t v_res_858_; lean_object* v_r_859_; 
v_i_boxed_856_ = lean_unbox_usize(v_i_854_);
lean_dec(v_i_854_);
v_stop_boxed_857_ = lean_unbox_usize(v_stop_855_);
lean_dec(v_stop_855_);
v_res_858_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_852_, v_as_853_, v_i_boxed_856_, v_stop_boxed_857_);
lean_dec_ref(v_as_853_);
lean_dec_ref(v_token_852_);
v_r_859_ = lean_box(v_res_858_);
return v_r_859_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_containsToken(lean_object* v_connection_860_, lean_object* v_token_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_array_get_size(v_connection_860_);
v___x_864_ = lean_nat_dec_lt(v___x_862_, v___x_863_);
if (v___x_864_ == 0)
{
lean_dec_ref(v_token_861_);
return v___x_864_;
}
else
{
lean_object* v___x_865_; 
v___x_865_ = lean_string_utf8_byte_size(v_token_861_);
if (v___x_864_ == 0)
{
lean_dec_ref(v_token_861_);
return v___x_864_;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v_token_869_; size_t v___x_870_; size_t v___x_871_; uint8_t v___x_872_; 
v___x_866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_866_, 0, v_token_861_);
lean_ctor_set(v___x_866_, 1, v___x_862_);
lean_ctor_set(v___x_866_, 2, v___x_865_);
v___x_867_ = l_String_Slice_trimAscii(v___x_866_);
v___x_868_ = l_String_Slice_toString(v___x_867_);
lean_dec_ref(v___x_867_);
v_token_869_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_868_, v___x_862_);
v___x_870_ = ((size_t)0ULL);
v___x_871_ = lean_usize_of_nat(v___x_863_);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_869_, v_connection_860_, v___x_870_, v___x_871_);
lean_dec_ref(v_token_869_);
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_containsToken___boxed(lean_object* v_connection_873_, lean_object* v_token_874_){
_start:
{
uint8_t v_res_875_; lean_object* v_r_876_; 
v_res_875_ = l_Std_Http_Header_Connection_containsToken(v_connection_873_, v_token_874_);
lean_dec_ref(v_connection_873_);
v_r_876_ = lean_box(v_res_875_);
return v_r_876_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_shouldClose(lean_object* v_connection_878_){
_start:
{
lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_879_ = ((lean_object*)(l_Std_Http_Header_Connection_shouldClose___closed__0));
v___x_880_ = l_Std_Http_Header_Connection_containsToken(v_connection_878_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_shouldClose___boxed(lean_object* v_connection_881_){
_start:
{
uint8_t v_res_882_; lean_object* v_r_883_; 
v_res_882_ = l_Std_Http_Header_Connection_shouldClose(v_connection_881_);
lean_dec_ref(v_connection_881_);
v_r_883_ = lean_box(v_res_882_);
return v_r_883_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(lean_object* v_as_884_, size_t v_i_885_, size_t v_stop_886_){
_start:
{
uint8_t v___x_887_; 
v___x_887_ = lean_usize_dec_eq(v_i_885_, v_stop_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_array_uget_borrowed(v_as_884_, v_i_885_);
lean_inc(v___x_888_);
v___x_889_ = l_Std_Http_Internal_isToken(v___x_888_);
if (v___x_889_ == 0)
{
uint8_t v___x_890_; 
v___x_890_ = 1;
return v___x_890_;
}
else
{
size_t v___x_891_; size_t v___x_892_; 
v___x_891_ = ((size_t)1ULL);
v___x_892_ = lean_usize_add(v_i_885_, v___x_891_);
v_i_885_ = v___x_892_;
goto _start;
}
}
else
{
uint8_t v___x_894_; 
v___x_894_ = 0;
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(lean_object* v_as_895_, lean_object* v_i_896_, lean_object* v_stop_897_){
_start:
{
size_t v_i_boxed_898_; size_t v_stop_boxed_899_; uint8_t v_res_900_; lean_object* v_r_901_; 
v_i_boxed_898_ = lean_unbox_usize(v_i_896_);
lean_dec(v_i_896_);
v_stop_boxed_899_ = lean_unbox_usize(v_stop_897_);
lean_dec(v_stop_897_);
v_res_900_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_895_, v_i_boxed_898_, v_stop_boxed_899_);
lean_dec_ref(v_as_895_);
v_r_901_ = lean_box(v_res_900_);
return v_r_901_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_parse(lean_object* v_v_902_){
_start:
{
lean_object* v___x_903_; 
v___x_903_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_902_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___x_904_; 
v___x_904_ = lean_box(0);
return v___x_904_;
}
else
{
lean_object* v_val_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_925_; 
v_val_905_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_925_ == 0)
{
v___x_907_ = v___x_903_;
v_isShared_908_ = v_isSharedCheck_925_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_val_905_);
lean_dec(v___x_903_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_925_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_array_get_size(v_val_905_);
v___x_911_ = lean_nat_dec_lt(v___x_909_, v___x_910_);
if (v___x_911_ == 0)
{
lean_object* v___x_913_; 
if (v_isShared_908_ == 0)
{
v___x_913_ = v___x_907_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_val_905_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
else
{
if (v___x_911_ == 0)
{
lean_object* v___x_916_; 
if (v_isShared_908_ == 0)
{
v___x_916_ = v___x_907_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_val_905_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
else
{
size_t v___x_918_; size_t v___x_919_; uint8_t v___x_920_; 
v___x_918_ = ((size_t)0ULL);
v___x_919_ = lean_usize_of_nat(v___x_910_);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_val_905_, v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_922_; 
if (v_isShared_908_ == 0)
{
v___x_922_ = v___x_907_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_val_905_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
lean_object* v___x_924_; 
lean_del_object(v___x_907_);
lean_dec(v_val_905_);
v___x_924_ = lean_box(0);
return v___x_924_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_serialize(lean_object* v_connection_926_){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_value_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_927_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_928_ = lean_array_to_list(v_connection_926_);
v_value_929_ = l_String_intercalate(v___x_927_, v___x_928_);
v___x_930_ = l_Std_Http_Header_Name_connection;
v___x_931_ = l_Std_Http_Header_Value_ofString_x21(v_value_929_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_unsigned_to_nat(8u);
v___x_949_ = lean_nat_to_int(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_unsigned_to_nat(2u);
v___x_951_ = lean_nat_to_int(v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___redArg(lean_object* v_x_959_){
_start:
{
lean_object* v_host_960_; lean_object* v_port_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_1035_; 
v_host_960_ = lean_ctor_get(v_x_959_, 0);
v_port_961_ = lean_ctor_get(v_x_959_, 1);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_x_959_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_963_ = v_x_959_;
v_isShared_964_ = v_isSharedCheck_1035_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_port_961_);
lean_inc(v_host_960_);
lean_dec(v_x_959_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_1035_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_ctr_971_; lean_object* v_a_972_; 
v___x_965_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_966_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__3));
v___x_967_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__4, &l_Std_Http_Header_instReprHost_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__5, &l_Std_Http_Header_instReprHost_repr___redArg___closed__5_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5);
switch(lean_obj_tag(v_host_960_))
{
case 0:
{
lean_object* v_name_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1014_; 
v_name_1005_ = lean_ctor_get(v_host_960_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_host_960_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1007_ = v_host_960_;
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_name_1005_);
lean_dec(v_host_960_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__9));
v___x_1010_ = l_String_quote(v_name_1005_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set_tag(v___x_1007_, 3);
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
v_ctr_971_ = v___x_1009_;
v_a_972_ = v___x_1012_;
goto v___jp_970_;
}
}
}
case 1:
{
lean_object* v_ipv4_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1024_; 
v_ipv4_1015_ = lean_ctor_get(v_host_960_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_host_960_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1017_ = v_host_960_;
v_isShared_1018_ = v_isSharedCheck_1024_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_ipv4_1015_);
lean_dec(v_host_960_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1024_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1019_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__10));
v___x_1020_ = lean_uv_ntop_v4(v_ipv4_1015_);
lean_dec_ref(v_ipv4_1015_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set_tag(v___x_1017_, 3);
lean_ctor_set(v___x_1017_, 0, v___x_1020_);
v___x_1022_ = v___x_1017_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
v_ctr_971_ = v___x_1019_;
v_a_972_ = v___x_1022_;
goto v___jp_970_;
}
}
}
default: 
{
lean_object* v_ipv6_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1034_; 
v_ipv6_1025_ = lean_ctor_get(v_host_960_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_host_960_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1027_ = v_host_960_;
v_isShared_1028_ = v_isSharedCheck_1034_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_ipv6_1025_);
lean_dec(v_host_960_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1034_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1029_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__11));
v___x_1030_ = lean_uv_ntop_v6(v_ipv6_1025_);
lean_dec_ref(v_ipv6_1025_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set_tag(v___x_1027_, 3);
lean_ctor_set(v___x_1027_, 0, v___x_1030_);
v___x_1032_ = v___x_1027_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
v_ctr_971_ = v___x_1029_;
v_a_972_ = v___x_1032_;
goto v___jp_970_;
}
}
}
}
v___jp_970_:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_973_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__6));
v___x_974_ = lean_string_append(v___x_973_, v_ctr_971_);
v___x_975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
v___x_976_ = lean_box(1);
if (v_isShared_964_ == 0)
{
lean_ctor_set_tag(v___x_963_, 5);
lean_ctor_set(v___x_963_, 1, v___x_976_);
lean_ctor_set(v___x_963_, 0, v___x_975_);
v___x_978_ = v___x_963_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___x_976_);
v___x_978_ = v_reuseFailAlloc_1004_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v_a_972_);
v___x_980_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_969_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = 0;
v___x_982_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*1, v___x_981_);
v___x_983_ = l_Repr_addAppParen(v___x_982_, v___x_968_);
v___x_984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_967_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*1, v___x_981_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_966_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_976_);
v___x_990_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__8));
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_965_);
v___x_993_ = l_Std_Http_URI_instReprPort_repr(v_port_961_, v___x_968_);
lean_dec(v_port_961_);
v___x_994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_967_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v___x_981_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_992_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_998_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_996_);
v___x_1000_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_997_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set_uint8(v___x_1003_, sizeof(void*)*1, v___x_981_);
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr(lean_object* v_x_1036_, lean_object* v_prec_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Std_Http_Header_instReprHost_repr___redArg(v_x_1036_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___boxed(lean_object* v_x_1039_, lean_object* v_prec_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_Http_Header_instReprHost_repr(v_x_1039_, v_prec_1040_);
lean_dec(v_prec_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqHost_beq(lean_object* v_x_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v_host_1046_; lean_object* v_port_1047_; lean_object* v_host_1048_; lean_object* v_port_1049_; uint8_t v___x_1050_; 
v_host_1046_ = lean_ctor_get(v_x_1044_, 0);
v_port_1047_ = lean_ctor_get(v_x_1044_, 1);
v_host_1048_ = lean_ctor_get(v_x_1045_, 0);
v_port_1049_ = lean_ctor_get(v_x_1045_, 1);
v___x_1050_ = l_Std_Http_URI_instBEqHost_beq(v_host_1046_, v_host_1048_);
if (v___x_1050_ == 0)
{
return v___x_1050_;
}
else
{
uint8_t v___x_1051_; 
v___x_1051_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1047_, v_port_1049_);
return v___x_1051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqHost_beq___boxed(lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_res_1054_ = l_Std_Http_Header_instBEqHost_beq(v_x_1052_, v_x_1053_);
lean_dec_ref(v_x_1053_);
lean_dec_ref(v_x_1052_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0(lean_object* v___x_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Std_Http_URI_Parser_parseHostHeader(v___x_1061_, v___y_1062_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_pos_1064_; lean_object* v_array_1065_; lean_object* v_idx_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_pos_1064_ = lean_ctor_get(v___x_1063_, 0);
v_array_1065_ = lean_ctor_get(v_pos_1064_, 0);
v_idx_1066_ = lean_ctor_get(v_pos_1064_, 1);
v___x_1067_ = lean_byte_array_size(v_array_1065_);
v___x_1068_ = lean_nat_dec_lt(v_idx_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
return v___x_1063_;
}
else
{
lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1076_; 
lean_inc(v_pos_1064_);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; lean_object* v_unused_1078_; 
v_unused_1077_ = lean_ctor_get(v___x_1063_, 1);
lean_dec(v_unused_1077_);
v_unused_1078_ = lean_ctor_get(v___x_1063_, 0);
lean_dec(v_unused_1078_);
v___x_1070_ = v___x_1063_;
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
else
{
lean_dec(v___x_1063_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1076_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1072_ = ((lean_object*)(l_Std_Http_Header_Host_parse___lam__0___closed__1));
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 1);
lean_ctor_set(v___x_1070_, 1, v___x_1072_);
v___x_1074_ = v___x_1070_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_pos_1064_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0___boxed(lean_object* v___x_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Std_Http_Header_Host_parse___lam__0(v___x_1079_, v___y_1080_);
lean_dec_ref(v___x_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse(lean_object* v_v_1092_){
_start:
{
lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v_parsed_1095_; 
v___f_1093_ = ((lean_object*)(l_Std_Http_Header_Host_parse___closed__1));
v___x_1094_ = lean_string_to_utf8(v_v_1092_);
v_parsed_1095_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1093_, v___x_1094_);
if (lean_obj_tag(v_parsed_1095_) == 0)
{
lean_object* v___x_1096_; 
lean_dec_ref_known(v_parsed_1095_, 1);
v___x_1096_ = lean_box(0);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1113_; 
v_a_1097_ = lean_ctor_get(v_parsed_1095_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_parsed_1095_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1099_ = v_parsed_1095_;
v_isShared_1100_ = v_isSharedCheck_1113_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v_parsed_1095_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1113_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v_fst_1101_; lean_object* v_snd_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1112_; 
v_fst_1101_ = lean_ctor_get(v_a_1097_, 0);
v_snd_1102_ = lean_ctor_get(v_a_1097_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_a_1097_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1104_ = v_a_1097_;
v_isShared_1105_ = v_isSharedCheck_1112_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_snd_1102_);
lean_inc(v_fst_1101_);
lean_dec(v_a_1097_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1112_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fst_1101_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_snd_1102_);
v___x_1107_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v___x_1107_);
v___x_1109_ = v___x_1099_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_serialize(lean_object* v_host_1116_){
_start:
{
lean_object* v___y_1118_; lean_object* v___y_1122_; lean_object* v_port_1126_; 
v_port_1126_ = lean_ctor_get(v_host_1116_, 1);
switch(lean_obj_tag(v_port_1126_))
{
case 0:
{
lean_object* v_host_1127_; 
v_host_1127_ = lean_ctor_get(v_host_1116_, 0);
lean_inc_ref(v_host_1127_);
lean_dec_ref(v_host_1116_);
switch(lean_obj_tag(v_host_1127_))
{
case 0:
{
lean_object* v_name_1128_; lean_object* v___x_1129_; 
v_name_1128_ = lean_ctor_get(v_host_1127_, 0);
lean_inc_ref(v_name_1128_);
lean_dec_ref_known(v_host_1127_, 1);
v___x_1129_ = l_Std_Http_Header_Value_ofString_x21(v_name_1128_);
v___y_1118_ = v___x_1129_;
goto v___jp_1117_;
}
case 1:
{
lean_object* v_ipv4_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v_ipv4_1130_ = lean_ctor_get(v_host_1127_, 0);
lean_inc_ref(v_ipv4_1130_);
lean_dec_ref_known(v_host_1127_, 1);
v___x_1131_ = lean_uv_ntop_v4(v_ipv4_1130_);
lean_dec_ref(v_ipv4_1130_);
v___x_1132_ = l_Std_Http_Header_Value_ofString_x21(v___x_1131_);
v___y_1118_ = v___x_1132_;
goto v___jp_1117_;
}
default: 
{
lean_object* v_ipv6_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_ipv6_1133_ = lean_ctor_get(v_host_1127_, 0);
lean_inc_ref(v_ipv6_1133_);
lean_dec_ref_known(v_host_1127_, 1);
v___x_1134_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1135_ = lean_uv_ntop_v6(v_ipv6_1133_);
lean_dec_ref(v_ipv6_1133_);
v___x_1136_ = lean_string_append(v___x_1134_, v___x_1135_);
lean_dec_ref(v___x_1135_);
v___x_1137_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1138_ = lean_string_append(v___x_1136_, v___x_1137_);
v___x_1139_ = l_Std_Http_Header_Value_ofString_x21(v___x_1138_);
v___y_1118_ = v___x_1139_;
goto v___jp_1117_;
}
}
}
case 1:
{
lean_object* v_host_1140_; 
v_host_1140_ = lean_ctor_get(v_host_1116_, 0);
lean_inc_ref(v_host_1140_);
lean_dec_ref(v_host_1116_);
switch(lean_obj_tag(v_host_1140_))
{
case 0:
{
lean_object* v_name_1141_; 
v_name_1141_ = lean_ctor_get(v_host_1140_, 0);
lean_inc_ref(v_name_1141_);
lean_dec_ref_known(v_host_1140_, 1);
v___y_1122_ = v_name_1141_;
goto v___jp_1121_;
}
case 1:
{
lean_object* v_ipv4_1142_; lean_object* v___x_1143_; 
v_ipv4_1142_ = lean_ctor_get(v_host_1140_, 0);
lean_inc_ref(v_ipv4_1142_);
lean_dec_ref_known(v_host_1140_, 1);
v___x_1143_ = lean_uv_ntop_v4(v_ipv4_1142_);
lean_dec_ref(v_ipv4_1142_);
v___y_1122_ = v___x_1143_;
goto v___jp_1121_;
}
default: 
{
lean_object* v_ipv6_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v_ipv6_1144_ = lean_ctor_get(v_host_1140_, 0);
lean_inc_ref(v_ipv6_1144_);
lean_dec_ref_known(v_host_1140_, 1);
v___x_1145_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1146_ = lean_uv_ntop_v6(v_ipv6_1144_);
lean_dec_ref(v_ipv6_1144_);
v___x_1147_ = lean_string_append(v___x_1145_, v___x_1146_);
lean_dec_ref(v___x_1146_);
v___x_1148_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1149_ = lean_string_append(v___x_1147_, v___x_1148_);
v___y_1122_ = v___x_1149_;
goto v___jp_1121_;
}
}
}
default: 
{
lean_object* v_host_1150_; uint16_t v_port_1151_; lean_object* v___y_1153_; 
lean_inc_ref(v_port_1126_);
v_host_1150_ = lean_ctor_get(v_host_1116_, 0);
lean_inc_ref(v_host_1150_);
lean_dec_ref(v_host_1116_);
v_port_1151_ = lean_ctor_get_uint16(v_port_1126_, 0);
lean_dec_ref_known(v_port_1126_, 0);
switch(lean_obj_tag(v_host_1150_))
{
case 0:
{
lean_object* v_name_1160_; 
v_name_1160_ = lean_ctor_get(v_host_1150_, 0);
lean_inc_ref(v_name_1160_);
lean_dec_ref_known(v_host_1150_, 1);
v___y_1153_ = v_name_1160_;
goto v___jp_1152_;
}
case 1:
{
lean_object* v_ipv4_1161_; lean_object* v___x_1162_; 
v_ipv4_1161_ = lean_ctor_get(v_host_1150_, 0);
lean_inc_ref(v_ipv4_1161_);
lean_dec_ref_known(v_host_1150_, 1);
v___x_1162_ = lean_uv_ntop_v4(v_ipv4_1161_);
lean_dec_ref(v_ipv4_1161_);
v___y_1153_ = v___x_1162_;
goto v___jp_1152_;
}
default: 
{
lean_object* v_ipv6_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_ipv6_1163_ = lean_ctor_get(v_host_1150_, 0);
lean_inc_ref(v_ipv6_1163_);
lean_dec_ref_known(v_host_1150_, 1);
v___x_1164_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1165_ = lean_uv_ntop_v6(v_ipv6_1163_);
lean_dec_ref(v_ipv6_1163_);
v___x_1166_ = lean_string_append(v___x_1164_, v___x_1165_);
lean_dec_ref(v___x_1165_);
v___x_1167_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1168_ = lean_string_append(v___x_1166_, v___x_1167_);
v___y_1153_ = v___x_1168_;
goto v___jp_1152_;
}
}
v___jp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1154_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1155_ = lean_string_append(v___y_1153_, v___x_1154_);
v___x_1156_ = lean_uint16_to_nat(v_port_1151_);
v___x_1157_ = l_Nat_reprFast(v___x_1156_);
v___x_1158_ = lean_string_append(v___x_1155_, v___x_1157_);
lean_dec_ref(v___x_1157_);
v___x_1159_ = l_Std_Http_Header_Value_ofString_x21(v___x_1158_);
v___y_1118_ = v___x_1159_;
goto v___jp_1117_;
}
}
}
v___jp_1117_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__0));
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___y_1118_);
return v___x_1120_;
}
v___jp_1121_:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1124_ = lean_string_append(v___y_1122_, v___x_1123_);
v___x_1125_ = l_Std_Http_Header_Value_ofString_x21(v___x_1124_);
v___y_1118_ = v___x_1125_;
goto v___jp_1117_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1181_ = ((lean_object*)(l_Std_Http_Header_instReprExpect_repr___redArg___closed__1));
v___x_1182_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1183_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v___x_1181_);
return v___x_1183_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3(void){
_start:
{
uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = 0;
v___x_1185_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__2, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__2_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2);
v___x_1186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
lean_ctor_set_uint8(v___x_1186_, sizeof(void*)*1, v___x_1184_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg(){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__3, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__3_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___boxed(lean_object* v___dummy_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v_res_1190_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___closed__0(void){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr(lean_object* v_x_1192_, lean_object* v_prec_1193_){
_start:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___closed__0, &l_Std_Http_Header_instReprExpect_repr___closed__0_once, _init_l_Std_Http_Header_instReprExpect_repr___closed__0);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___boxed(lean_object* v_x_1195_, lean_object* v_prec_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Std_Http_Header_instReprExpect_repr(v_x_1195_, v_prec_1196_);
lean_dec(v_prec_1196_);
return v_res_1197_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq___redArg(){
_start:
{
uint8_t v___x_1201_; 
v___x_1201_ = 1;
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___redArg___boxed(lean_object* v___dummy_1202_){
_start:
{
uint8_t v_res_1203_; lean_object* v_r_1204_; 
v_res_1203_ = l_Std_Http_Header_instBEqExpect_beq___redArg();
v_r_1204_ = lean_box(v_res_1203_);
return v_r_1204_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq(lean_object* v_x_1205_, lean_object* v_y_1206_){
_start:
{
uint8_t v___x_1207_; 
v___x_1207_ = 1;
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___boxed(lean_object* v_x_1208_, lean_object* v_y_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Std_Http_Header_instBEqExpect_beq(v_x_1208_, v_y_1209_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_parse(lean_object* v_v_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_normalized_1223_; lean_object* v___x_1224_; uint8_t v___x_1225_; 
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_string_utf8_byte_size(v_v_1217_);
v___x_1220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1220_, 0, v_v_1217_);
lean_ctor_set(v___x_1220_, 1, v___x_1218_);
lean_ctor_set(v___x_1220_, 2, v___x_1219_);
v___x_1221_ = l_String_Slice_trimAscii(v___x_1220_);
v___x_1222_ = l_String_Slice_toString(v___x_1221_);
lean_dec_ref(v___x_1221_);
v_normalized_1223_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_1222_, v___x_1218_);
v___x_1224_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1225_ = lean_string_dec_eq(v_normalized_1223_, v___x_1224_);
lean_dec_ref(v_normalized_1223_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; 
v___x_1226_ = lean_box(0);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; 
v___x_1227_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__1));
return v___x_1227_;
}
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1229_ = l_Std_Http_Header_Value_ofString_x21(v___x_1228_);
return v___x_1229_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__0, &l_Std_Http_Header_Expect_serialize___redArg___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0);
v___x_1231_ = l_Std_Http_Header_Name_expect;
v___x_1232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v___x_1230_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg(){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__1, &l_Std_Http_Header_Expect_serialize___redArg___closed__1_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg___boxed(lean_object* v___dummy_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_Http_Header_Expect_serialize___redArg();
return v_res_1236_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___closed__0(void){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l_Std_Http_Header_Expect_serialize___redArg();
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize(lean_object* v_x_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___closed__0, &l_Std_Http_Header_Expect_serialize___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___closed__0);
return v___x_1239_;
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

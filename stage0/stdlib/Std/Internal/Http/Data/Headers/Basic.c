// Lean compiler output
// Module: Std.Internal.Http.Data.Headers.Basic
// Imports: public import Std.Internal.Http.Data.Headers.Name public import Std.Internal.Http.Data.Headers.Value public import Std.Internal.Parsec.Basic
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
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
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
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
extern lean_object* l_Std_Http_Header_Name_connection;
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(lean_object*);
static const lean_string_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0_value;
static const lean_string_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1_value;
static const lean_string_object l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2_value;
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_instEncodeV11OfHeader___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_instEncodeV11OfHeader___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___closed__0 = (const lean_object*)&l_Std_Http_instEncodeV11OfHeader___redArg___closed__0_value;
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
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__0(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; uint32_t v___x_3_; uint32_t v___x_4_; uint8_t v___x_5_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_string_utf8_get(v_x_1_, v___x_2_);
v___x_4_ = 97;
v___x_5_ = lean_uint32_dec_le(v___x_4_, v___x_3_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; 
v___x_6_ = lean_string_utf8_set(v_x_1_, v___x_2_, v___x_3_);
return v___x_6_;
}
else
{
uint32_t v___x_7_; uint8_t v___x_8_; 
v___x_7_ = 122;
v___x_8_ = lean_uint32_dec_le(v___x_3_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; 
v___x_9_ = lean_string_utf8_set(v_x_1_, v___x_2_, v___x_3_);
return v___x_9_;
}
else
{
uint32_t v___x_10_; uint32_t v___x_11_; lean_object* v___x_12_; 
v___x_10_ = 4294967264;
v___x_11_ = lean_uint32_add(v___x_3_, v___x_10_);
v___x_12_ = lean_string_utf8_set(v_x_1_, v___x_2_, v___x_11_);
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg___lam__1(lean_object* v_h_16_, lean_object* v___f_17_, lean_object* v_buffer_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_serialize_20_; lean_object* v___x_21_; lean_object* v_fst_22_; lean_object* v_snd_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_data_28_; lean_object* v_size_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_47_; 
v_serialize_20_ = lean_ctor_get(v_h_16_, 1);
lean_inc_ref(v_serialize_20_);
lean_dec_ref(v_h_16_);
v___x_21_ = lean_apply_1(v_serialize_20_, v_a_19_);
v_fst_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_fst_22_);
v_snd_23_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_snd_23_);
lean_dec_ref(v___x_21_);
v___x_24_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__0));
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_box(0);
v___x_27_ = l_String_splitOnAux(v_fst_22_, v___x_24_, v___x_25_, v___x_25_, v___x_25_, v___x_26_);
lean_dec(v_fst_22_);
v_data_28_ = lean_ctor_get(v_buffer_18_, 0);
v_size_29_ = lean_ctor_get(v_buffer_18_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v_buffer_18_);
if (v_isSharedCheck_47_ == 0)
{
v___x_31_ = v_buffer_18_;
v_isShared_32_ = v_isSharedCheck_47_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_size_29_);
lean_inc(v_data_28_);
lean_dec(v_buffer_18_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_47_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v_it_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v_it_33_ = l_List_mapTR_loop___redArg(v___f_17_, v___x_27_, v___x_26_);
v___x_34_ = l_String_intercalate(v___x_24_, v_it_33_);
v___x_35_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__1));
v___x_36_ = lean_string_append(v___x_34_, v___x_35_);
v___x_37_ = lean_string_append(v___x_36_, v_snd_23_);
lean_dec(v_snd_23_);
v___x_38_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1___closed__2));
v___x_39_ = lean_string_append(v___x_37_, v___x_38_);
v___x_40_ = lean_string_to_utf8(v___x_39_);
lean_dec_ref(v___x_39_);
lean_inc_ref(v___x_40_);
v___x_41_ = lean_array_push(v_data_28_, v___x_40_);
v___x_42_ = lean_byte_array_size(v___x_40_);
lean_dec_ref(v___x_40_);
v___x_43_ = lean_nat_add(v_size_29_, v___x_42_);
lean_dec(v_size_29_);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 1, v___x_43_);
lean_ctor_set(v___x_31_, 0, v___x_41_);
v___x_45_ = v___x_31_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_41_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader___redArg(lean_object* v_h_49_){
_start:
{
lean_object* v___f_50_; lean_object* v___f_51_; 
v___f_50_ = ((lean_object*)(l_Std_Http_instEncodeV11OfHeader___redArg___closed__0));
v___f_51_ = lean_alloc_closure((void*)(l_Std_Http_instEncodeV11OfHeader___redArg___lam__1), 4, 2);
lean_closure_set(v___f_51_, 0, v_h_49_);
lean_closure_set(v___f_51_, 1, v___f_50_);
return v___f_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_instEncodeV11OfHeader(lean_object* v_00_u03b1_52_, lean_object* v_h_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Std_Http_instEncodeV11OfHeader___redArg(v_h_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(lean_object* v_s_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0));
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___boxed(lean_object* v_s_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v_s_59_);
lean_dec_ref(v_s_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(lean_object* v_s_61_, lean_object* v_p_62_){
_start:
{
uint32_t v___y_64_; lean_object* v___x_69_; uint8_t v___x_70_; 
v___x_69_ = lean_string_utf8_byte_size(v_s_61_);
v___x_70_ = lean_nat_dec_eq(v_p_62_, v___x_69_);
if (v___x_70_ == 0)
{
uint32_t v___x_71_; uint32_t v___x_72_; uint8_t v___x_73_; 
v___x_71_ = lean_string_utf8_get_fast(v_s_61_, v_p_62_);
v___x_72_ = 65;
v___x_73_ = lean_uint32_dec_le(v___x_72_, v___x_71_);
if (v___x_73_ == 0)
{
v___y_64_ = v___x_71_;
goto v___jp_63_;
}
else
{
uint32_t v___x_74_; uint8_t v___x_75_; 
v___x_74_ = 90;
v___x_75_ = lean_uint32_dec_le(v___x_71_, v___x_74_);
if (v___x_75_ == 0)
{
v___y_64_ = v___x_71_;
goto v___jp_63_;
}
else
{
uint32_t v___x_76_; uint32_t v___x_77_; 
v___x_76_ = 32;
v___x_77_ = lean_uint32_add(v___x_71_, v___x_76_);
v___y_64_ = v___x_77_;
goto v___jp_63_;
}
}
}
else
{
lean_dec(v_p_62_);
return v_s_61_;
}
v___jp_63_:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
lean_inc(v_p_62_);
v___x_65_ = lean_string_utf8_set(v_s_61_, v_p_62_, v___y_64_);
v___x_66_ = l_Char_utf8Size(v___y_64_);
v___x_67_ = lean_nat_add(v_p_62_, v___x_66_);
lean_dec(v___x_66_);
lean_dec(v_p_62_);
v_s_61_ = v___x_65_;
v_p_62_ = v___x_67_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(size_t v_sz_78_, size_t v_i_79_, lean_object* v_bs_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = lean_usize_dec_lt(v_i_79_, v_sz_78_);
if (v___x_81_ == 0)
{
return v_bs_80_;
}
else
{
lean_object* v_v_82_; lean_object* v___x_83_; lean_object* v_bs_x27_84_; lean_object* v___x_85_; lean_object* v___x_86_; size_t v___x_87_; size_t v___x_88_; lean_object* v___x_89_; 
v_v_82_ = lean_array_uget(v_bs_80_, v_i_79_);
v___x_83_ = lean_unsigned_to_nat(0u);
v_bs_x27_84_ = lean_array_uset(v_bs_80_, v_i_79_, v___x_83_);
v___x_85_ = l_String_Slice_toString(v_v_82_);
lean_dec(v_v_82_);
v___x_86_ = l_String_mapAux___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_85_, v___x_83_);
v___x_87_ = ((size_t)1ULL);
v___x_88_ = lean_usize_add(v_i_79_, v___x_87_);
v___x_89_ = lean_array_uset(v_bs_x27_84_, v_i_79_, v___x_86_);
v_i_79_ = v___x_88_;
v_bs_80_ = v___x_89_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4___boxed(lean_object* v_sz_91_, lean_object* v_i_92_, lean_object* v_bs_93_){
_start:
{
size_t v_sz_boxed_94_; size_t v_i_boxed_95_; lean_object* v_res_96_; 
v_sz_boxed_94_ = lean_unbox_usize(v_sz_91_);
lean_dec(v_sz_91_);
v_i_boxed_95_ = lean_unbox_usize(v_i_92_);
lean_dec(v_i_92_);
v_res_96_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_boxed_94_, v_i_boxed_95_, v_bs_93_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(lean_object* v___x_97_, lean_object* v___x_98_, lean_object* v___x_99_, lean_object* v_a_100_, lean_object* v_b_101_){
_start:
{
lean_object* v_it_103_; lean_object* v_startInclusive_104_; lean_object* v_endExclusive_105_; 
if (lean_obj_tag(v_a_100_) == 0)
{
lean_object* v_currPos_110_; lean_object* v_searcher_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_140_; 
v_currPos_110_ = lean_ctor_get(v_a_100_, 0);
v_searcher_111_ = lean_ctor_get(v_a_100_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_a_100_);
if (v_isSharedCheck_140_ == 0)
{
v___x_113_ = v_a_100_;
v_isShared_114_ = v_isSharedCheck_140_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_searcher_111_);
lean_inc(v_currPos_110_);
lean_dec(v_a_100_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_140_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_str_115_; lean_object* v_startInclusive_116_; lean_object* v_endExclusive_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_str_115_ = lean_ctor_get(v___x_98_, 0);
v_startInclusive_116_ = lean_ctor_get(v___x_98_, 1);
v_endExclusive_117_ = lean_ctor_get(v___x_98_, 2);
v___x_118_ = lean_nat_sub(v_endExclusive_117_, v_startInclusive_116_);
v___x_119_ = lean_nat_dec_eq(v_searcher_111_, v___x_118_);
lean_dec(v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; uint32_t v___x_121_; uint32_t v___x_122_; uint8_t v___x_123_; 
v___x_120_ = lean_nat_add(v_startInclusive_116_, v_searcher_111_);
v___x_121_ = lean_string_utf8_get_fast(v_str_115_, v___x_120_);
v___x_122_ = 44;
v___x_123_ = lean_uint32_dec_eq(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
lean_dec(v_searcher_111_);
v___x_124_ = lean_string_utf8_next_fast(v_str_115_, v___x_120_);
lean_dec(v___x_120_);
v___x_125_ = lean_nat_sub(v___x_124_, v_startInclusive_116_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_125_);
v___x_127_ = v___x_113_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_currPos_110_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_125_);
v___x_127_ = v_reuseFailAlloc_129_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v_a_100_ = v___x_127_;
goto _start;
}
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v_slice_133_; lean_object* v_nextIt_135_; 
v___x_130_ = lean_string_utf8_next_fast(v_str_115_, v___x_120_);
v___x_131_ = lean_nat_sub(v___x_130_, v___x_120_);
lean_dec(v___x_120_);
v___x_132_ = lean_nat_add(v_searcher_111_, v___x_131_);
lean_dec(v___x_131_);
v_slice_133_ = l_String_Slice_subslice_x21(v___x_98_, v_currPos_110_, v_searcher_111_);
lean_inc(v___x_132_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 1, v___x_132_);
lean_ctor_set(v___x_113_, 0, v___x_132_);
v_nextIt_135_ = v___x_113_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_132_);
v_nextIt_135_ = v_reuseFailAlloc_138_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v_startInclusive_136_; lean_object* v_endExclusive_137_; 
v_startInclusive_136_ = lean_ctor_get(v_slice_133_, 0);
lean_inc(v_startInclusive_136_);
v_endExclusive_137_ = lean_ctor_get(v_slice_133_, 1);
lean_inc(v_endExclusive_137_);
lean_dec_ref(v_slice_133_);
v_it_103_ = v_nextIt_135_;
v_startInclusive_104_ = v_startInclusive_136_;
v_endExclusive_105_ = v_endExclusive_137_;
goto v___jp_102_;
}
}
}
else
{
lean_object* v___x_139_; 
lean_del_object(v___x_113_);
lean_dec(v_searcher_111_);
v___x_139_ = lean_box(1);
lean_inc(v___x_99_);
v_it_103_ = v___x_139_;
v_startInclusive_104_ = v_currPos_110_;
v_endExclusive_105_ = v___x_99_;
goto v___jp_102_;
}
}
}
else
{
lean_dec(v___x_99_);
lean_dec_ref(v___x_97_);
return v_b_101_;
}
v___jp_102_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
lean_inc_ref(v___x_97_);
v___x_106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_97_);
lean_ctor_set(v___x_106_, 1, v_startInclusive_104_);
lean_ctor_set(v___x_106_, 2, v_endExclusive_105_);
v___x_107_ = l_String_Slice_trimAscii(v___x_106_);
v___x_108_ = lean_array_push(v_b_101_, v___x_107_);
v_a_100_ = v_it_103_;
v_b_101_ = v___x_108_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg___boxed(lean_object* v___x_141_, lean_object* v___x_142_, lean_object* v___x_143_, lean_object* v_a_144_, lean_object* v_b_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_141_, v___x_142_, v___x_143_, v_a_144_, v_b_145_);
lean_dec_ref(v___x_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(lean_object* v___x_147_, lean_object* v___x_148_, lean_object* v___x_149_, lean_object* v_a_150_, lean_object* v_b_151_){
_start:
{
lean_object* v_it_153_; lean_object* v_startInclusive_154_; lean_object* v_endExclusive_155_; 
if (lean_obj_tag(v_a_150_) == 0)
{
lean_object* v_currPos_160_; lean_object* v_searcher_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_190_; 
v_currPos_160_ = lean_ctor_get(v_a_150_, 0);
v_searcher_161_ = lean_ctor_get(v_a_150_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_a_150_);
if (v_isSharedCheck_190_ == 0)
{
v___x_163_ = v_a_150_;
v_isShared_164_ = v_isSharedCheck_190_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_searcher_161_);
lean_inc(v_currPos_160_);
lean_dec(v_a_150_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_190_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v_str_165_; lean_object* v_startInclusive_166_; lean_object* v_endExclusive_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_str_165_ = lean_ctor_get(v___x_148_, 0);
v_startInclusive_166_ = lean_ctor_get(v___x_148_, 1);
v_endExclusive_167_ = lean_ctor_get(v___x_148_, 2);
v___x_168_ = lean_nat_sub(v_endExclusive_167_, v_startInclusive_166_);
v___x_169_ = lean_nat_dec_eq(v_searcher_161_, v___x_168_);
lean_dec(v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; uint32_t v___x_171_; uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_170_ = lean_nat_add(v_startInclusive_166_, v_searcher_161_);
v___x_171_ = lean_string_utf8_get_fast(v_str_165_, v___x_170_);
v___x_172_ = 44;
v___x_173_ = lean_uint32_dec_eq(v___x_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
lean_dec(v_searcher_161_);
v___x_174_ = lean_string_utf8_next_fast(v_str_165_, v___x_170_);
lean_dec(v___x_170_);
v___x_175_ = lean_nat_sub(v___x_174_, v_startInclusive_166_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v___x_175_);
v___x_177_ = v___x_163_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_currPos_160_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v___x_175_);
v___x_177_ = v_reuseFailAlloc_179_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; 
v___x_178_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_147_, v___x_148_, v___x_149_, v___x_177_, v_b_151_);
return v___x_178_;
}
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v_slice_183_; lean_object* v_nextIt_185_; 
v___x_180_ = lean_string_utf8_next_fast(v_str_165_, v___x_170_);
v___x_181_ = lean_nat_sub(v___x_180_, v___x_170_);
lean_dec(v___x_170_);
v___x_182_ = lean_nat_add(v_searcher_161_, v___x_181_);
lean_dec(v___x_181_);
v_slice_183_ = l_String_Slice_subslice_x21(v___x_148_, v_currPos_160_, v_searcher_161_);
lean_inc(v___x_182_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 1, v___x_182_);
lean_ctor_set(v___x_163_, 0, v___x_182_);
v_nextIt_185_ = v___x_163_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_182_);
v_nextIt_185_ = v_reuseFailAlloc_188_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_object* v_startInclusive_186_; lean_object* v_endExclusive_187_; 
v_startInclusive_186_ = lean_ctor_get(v_slice_183_, 0);
lean_inc(v_startInclusive_186_);
v_endExclusive_187_ = lean_ctor_get(v_slice_183_, 1);
lean_inc(v_endExclusive_187_);
lean_dec_ref(v_slice_183_);
v_it_153_ = v_nextIt_185_;
v_startInclusive_154_ = v_startInclusive_186_;
v_endExclusive_155_ = v_endExclusive_187_;
goto v___jp_152_;
}
}
}
else
{
lean_object* v___x_189_; 
lean_del_object(v___x_163_);
lean_dec(v_searcher_161_);
v___x_189_ = lean_box(1);
lean_inc(v___x_149_);
v_it_153_ = v___x_189_;
v_startInclusive_154_ = v_currPos_160_;
v_endExclusive_155_ = v___x_149_;
goto v___jp_152_;
}
}
}
else
{
lean_dec(v___x_149_);
lean_dec_ref(v___x_147_);
return v_b_151_;
}
v___jp_152_:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
lean_inc_ref(v___x_147_);
v___x_156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_156_, 0, v___x_147_);
lean_ctor_set(v___x_156_, 1, v_startInclusive_154_);
lean_ctor_set(v___x_156_, 2, v_endExclusive_155_);
v___x_157_ = l_String_Slice_trimAscii(v___x_156_);
v___x_158_ = lean_array_push(v_b_151_, v___x_157_);
v___x_159_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_147_, v___x_148_, v___x_149_, v_it_153_, v___x_158_);
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg___boxed(lean_object* v___x_191_, lean_object* v___x_192_, lean_object* v___x_193_, lean_object* v_a_194_, lean_object* v_b_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_191_, v___x_192_, v___x_193_, v_a_194_, v_b_195_);
lean_dec_ref(v___x_192_);
return v_res_196_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(lean_object* v___x_197_, lean_object* v___x_198_, lean_object* v___x_199_, lean_object* v_a_200_, uint8_t v_b_201_){
_start:
{
if (lean_obj_tag(v_a_200_) == 0)
{
lean_object* v_currPos_202_; lean_object* v_searcher_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_246_; 
v_currPos_202_ = lean_ctor_get(v_a_200_, 0);
v_searcher_203_ = lean_ctor_get(v_a_200_, 1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_a_200_);
if (v_isSharedCheck_246_ == 0)
{
v___x_205_ = v_a_200_;
v_isShared_206_ = v_isSharedCheck_246_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_searcher_203_);
lean_inc(v_currPos_202_);
lean_dec(v_a_200_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_246_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v_str_207_; lean_object* v_startInclusive_208_; lean_object* v_endExclusive_209_; uint8_t v___x_210_; lean_object* v_it_212_; lean_object* v_startInclusive_213_; lean_object* v_endExclusive_214_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_str_207_ = lean_ctor_get(v___x_198_, 0);
v_startInclusive_208_ = lean_ctor_get(v___x_198_, 1);
v_endExclusive_209_ = lean_ctor_get(v___x_198_, 2);
v___x_210_ = 1;
v___x_224_ = lean_nat_sub(v_endExclusive_209_, v_startInclusive_208_);
v___x_225_ = lean_nat_dec_eq(v_searcher_203_, v___x_224_);
lean_dec(v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; uint32_t v___x_227_; uint32_t v___x_228_; uint8_t v___x_229_; 
v___x_226_ = lean_nat_add(v_startInclusive_208_, v_searcher_203_);
v___x_227_ = lean_string_utf8_get_fast(v_str_207_, v___x_226_);
v___x_228_ = 44;
v___x_229_ = lean_uint32_dec_eq(v___x_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_searcher_203_);
v___x_230_ = lean_string_utf8_next_fast(v_str_207_, v___x_226_);
lean_dec(v___x_226_);
v___x_231_ = lean_nat_sub(v___x_230_, v_startInclusive_208_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_231_);
v___x_233_ = v___x_205_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_currPos_202_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_235_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
v_a_200_ = v___x_233_;
goto _start;
}
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v_slice_239_; lean_object* v_nextIt_241_; 
v___x_236_ = lean_string_utf8_next_fast(v_str_207_, v___x_226_);
v___x_237_ = lean_nat_sub(v___x_236_, v___x_226_);
lean_dec(v___x_226_);
v___x_238_ = lean_nat_add(v_searcher_203_, v___x_237_);
lean_dec(v___x_237_);
v_slice_239_ = l_String_Slice_subslice_x21(v___x_198_, v_currPos_202_, v_searcher_203_);
lean_inc(v___x_238_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v___x_238_);
lean_ctor_set(v___x_205_, 0, v___x_238_);
v_nextIt_241_ = v___x_205_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_238_);
v_nextIt_241_ = v_reuseFailAlloc_244_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v_startInclusive_242_; lean_object* v_endExclusive_243_; 
v_startInclusive_242_ = lean_ctor_get(v_slice_239_, 0);
lean_inc(v_startInclusive_242_);
v_endExclusive_243_ = lean_ctor_get(v_slice_239_, 1);
lean_inc(v_endExclusive_243_);
lean_dec_ref(v_slice_239_);
v_it_212_ = v_nextIt_241_;
v_startInclusive_213_ = v_startInclusive_242_;
v_endExclusive_214_ = v_endExclusive_243_;
goto v___jp_211_;
}
}
}
else
{
lean_object* v___x_245_; 
lean_del_object(v___x_205_);
lean_dec(v_searcher_203_);
v___x_245_ = lean_box(1);
lean_inc(v___x_199_);
v_it_212_ = v___x_245_;
v_startInclusive_213_ = v_currPos_202_;
v_endExclusive_214_ = v___x_199_;
goto v___jp_211_;
}
v___jp_211_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_startInclusive_217_; lean_object* v_endExclusive_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
lean_inc_ref(v___x_197_);
v___x_215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_215_, 0, v___x_197_);
lean_ctor_set(v___x_215_, 1, v_startInclusive_213_);
lean_ctor_set(v___x_215_, 2, v_endExclusive_214_);
v___x_216_ = l_String_Slice_trimAscii(v___x_215_);
v_startInclusive_217_ = lean_ctor_get(v___x_216_, 1);
lean_inc(v_startInclusive_217_);
v_endExclusive_218_ = lean_ctor_get(v___x_216_, 2);
lean_inc(v_endExclusive_218_);
lean_dec_ref(v___x_216_);
v___x_219_ = lean_nat_sub(v_endExclusive_218_, v_startInclusive_217_);
lean_dec(v_startInclusive_217_);
lean_dec(v_endExclusive_218_);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_nat_dec_eq(v___x_219_, v___x_220_);
lean_dec(v___x_219_);
if (v___x_221_ == 0)
{
v_a_200_ = v_it_212_;
v_b_201_ = v___x_210_;
goto _start;
}
else
{
uint8_t v___x_223_; 
lean_dec(v_it_212_);
lean_dec(v___x_199_);
lean_dec_ref(v___x_197_);
v___x_223_ = 0;
return v___x_223_;
}
}
}
}
else
{
lean_dec(v___x_199_);
lean_dec_ref(v___x_197_);
return v_b_201_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg___boxed(lean_object* v___x_247_, lean_object* v___x_248_, lean_object* v___x_249_, lean_object* v_a_250_, lean_object* v_b_251_){
_start:
{
uint8_t v_b_boxed_252_; uint8_t v_res_253_; lean_object* v_r_254_; 
v_b_boxed_252_ = lean_unbox(v_b_251_);
v_res_253_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_247_, v___x_248_, v___x_249_, v_a_250_, v_b_boxed_252_);
lean_dec_ref(v___x_248_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object* v___x_255_, lean_object* v___x_256_, lean_object* v___x_257_, lean_object* v_a_258_, uint8_t v_b_259_){
_start:
{
if (lean_obj_tag(v_a_258_) == 0)
{
lean_object* v_currPos_260_; lean_object* v_searcher_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_304_; 
v_currPos_260_ = lean_ctor_get(v_a_258_, 0);
v_searcher_261_ = lean_ctor_get(v_a_258_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_a_258_);
if (v_isSharedCheck_304_ == 0)
{
v___x_263_ = v_a_258_;
v_isShared_264_ = v_isSharedCheck_304_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_searcher_261_);
lean_inc(v_currPos_260_);
lean_dec(v_a_258_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_304_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_str_265_; lean_object* v_startInclusive_266_; lean_object* v_endExclusive_267_; uint8_t v___x_268_; lean_object* v_it_270_; lean_object* v_startInclusive_271_; lean_object* v_endExclusive_272_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_str_265_ = lean_ctor_get(v___x_256_, 0);
v_startInclusive_266_ = lean_ctor_get(v___x_256_, 1);
v_endExclusive_267_ = lean_ctor_get(v___x_256_, 2);
v___x_268_ = 1;
v___x_282_ = lean_nat_sub(v_endExclusive_267_, v_startInclusive_266_);
v___x_283_ = lean_nat_dec_eq(v_searcher_261_, v___x_282_);
lean_dec(v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; uint32_t v___x_285_; uint32_t v___x_286_; uint8_t v___x_287_; 
v___x_284_ = lean_nat_add(v_startInclusive_266_, v_searcher_261_);
v___x_285_ = lean_string_utf8_get_fast(v_str_265_, v___x_284_);
v___x_286_ = 44;
v___x_287_ = lean_uint32_dec_eq(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
lean_dec(v_searcher_261_);
v___x_288_ = lean_string_utf8_next_fast(v_str_265_, v___x_284_);
lean_dec(v___x_284_);
v___x_289_ = lean_nat_sub(v___x_288_, v_startInclusive_266_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_289_);
v___x_291_ = v___x_263_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_currPos_260_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_293_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
uint8_t v___x_292_; 
v___x_292_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_255_, v___x_256_, v___x_257_, v___x_291_, v_b_259_);
return v___x_292_;
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v_slice_297_; lean_object* v_nextIt_299_; 
v___x_294_ = lean_string_utf8_next_fast(v_str_265_, v___x_284_);
v___x_295_ = lean_nat_sub(v___x_294_, v___x_284_);
lean_dec(v___x_284_);
v___x_296_ = lean_nat_add(v_searcher_261_, v___x_295_);
lean_dec(v___x_295_);
v_slice_297_ = l_String_Slice_subslice_x21(v___x_256_, v_currPos_260_, v_searcher_261_);
lean_inc(v___x_296_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_296_);
lean_ctor_set(v___x_263_, 0, v___x_296_);
v_nextIt_299_ = v___x_263_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v___x_296_);
v_nextIt_299_ = v_reuseFailAlloc_302_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v_startInclusive_300_; lean_object* v_endExclusive_301_; 
v_startInclusive_300_ = lean_ctor_get(v_slice_297_, 0);
lean_inc(v_startInclusive_300_);
v_endExclusive_301_ = lean_ctor_get(v_slice_297_, 1);
lean_inc(v_endExclusive_301_);
lean_dec_ref(v_slice_297_);
v_it_270_ = v_nextIt_299_;
v_startInclusive_271_ = v_startInclusive_300_;
v_endExclusive_272_ = v_endExclusive_301_;
goto v___jp_269_;
}
}
}
else
{
lean_object* v___x_303_; 
lean_del_object(v___x_263_);
lean_dec(v_searcher_261_);
v___x_303_ = lean_box(1);
lean_inc(v___x_257_);
v_it_270_ = v___x_303_;
v_startInclusive_271_ = v_currPos_260_;
v_endExclusive_272_ = v___x_257_;
goto v___jp_269_;
}
v___jp_269_:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v_startInclusive_275_; lean_object* v_endExclusive_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
lean_inc_ref(v___x_255_);
v___x_273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_273_, 0, v___x_255_);
lean_ctor_set(v___x_273_, 1, v_startInclusive_271_);
lean_ctor_set(v___x_273_, 2, v_endExclusive_272_);
v___x_274_ = l_String_Slice_trimAscii(v___x_273_);
v_startInclusive_275_ = lean_ctor_get(v___x_274_, 1);
lean_inc(v_startInclusive_275_);
v_endExclusive_276_ = lean_ctor_get(v___x_274_, 2);
lean_inc(v_endExclusive_276_);
lean_dec_ref(v___x_274_);
v___x_277_ = lean_nat_sub(v_endExclusive_276_, v_startInclusive_275_);
lean_dec(v_startInclusive_275_);
lean_dec(v_endExclusive_276_);
v___x_278_ = lean_unsigned_to_nat(0u);
v___x_279_ = lean_nat_dec_eq(v___x_277_, v___x_278_);
lean_dec(v___x_277_);
if (v___x_279_ == 0)
{
uint8_t v___x_280_; 
v___x_280_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_255_, v___x_256_, v___x_257_, v_it_270_, v___x_268_);
return v___x_280_;
}
else
{
uint8_t v___x_281_; 
lean_dec(v_it_270_);
lean_dec(v___x_257_);
lean_dec_ref(v___x_255_);
v___x_281_ = 0;
return v___x_281_;
}
}
}
}
else
{
lean_dec(v___x_257_);
lean_dec_ref(v___x_255_);
return v_b_259_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object* v___x_305_, lean_object* v___x_306_, lean_object* v___x_307_, lean_object* v_a_308_, lean_object* v_b_309_){
_start:
{
uint8_t v_b_boxed_310_; uint8_t v_res_311_; lean_object* v_r_312_; 
v_b_boxed_310_ = lean_unbox(v_b_309_);
v_res_311_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_305_, v___x_306_, v___x_307_, v_a_308_, v_b_boxed_310_);
lean_dec_ref(v___x_306_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object* v_v_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_parts_319_; uint8_t v___x_320_; uint8_t v___x_321_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_string_utf8_byte_size(v_v_315_);
lean_inc_ref(v_v_315_);
v___x_318_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_318_, 0, v_v_315_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
lean_ctor_set(v___x_318_, 2, v___x_317_);
v_parts_319_ = l_String_Slice_splitToSubslice___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1(v___x_318_);
v___x_320_ = 1;
lean_inc(v_parts_319_);
lean_inc_ref(v_v_315_);
v___x_321_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_315_, v___x_318_, v___x_317_, v_parts_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; 
lean_dec(v_parts_319_);
lean_dec_ref(v___x_318_);
lean_dec_ref(v_v_315_);
v___x_322_ = lean_box(0);
return v___x_322_;
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; size_t v_sz_325_; size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((lean_object*)(l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList___closed__0));
v___x_324_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v_v_315_, v___x_318_, v___x_317_, v_parts_319_, v___x_323_);
lean_dec_ref(v___x_318_);
v_sz_325_ = lean_array_size(v___x_324_);
v___x_326_ = ((size_t)0ULL);
v___x_327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__4(v_sz_325_, v___x_326_, v___x_324_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object* v___x_329_, lean_object* v___x_330_, lean_object* v___x_331_, lean_object* v_inst_332_, lean_object* v_R_333_, lean_object* v_a_334_, uint8_t v_b_335_, lean_object* v_c_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_329_, v___x_330_, v___x_331_, v_a_334_, v_b_335_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object* v___x_338_, lean_object* v___x_339_, lean_object* v___x_340_, lean_object* v_inst_341_, lean_object* v_R_342_, lean_object* v_a_343_, lean_object* v_b_344_, lean_object* v_c_345_){
_start:
{
uint8_t v_b_boxed_346_; uint8_t v_res_347_; lean_object* v_r_348_; 
v_b_boxed_346_ = lean_unbox(v_b_344_);
v_res_347_ = l_WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_338_, v___x_339_, v___x_340_, v_inst_341_, v_R_342_, v_a_343_, v_b_boxed_346_, v_c_345_);
lean_dec_ref(v___x_339_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object* v___x_349_, lean_object* v___x_350_, lean_object* v___x_351_, lean_object* v_inst_352_, lean_object* v_R_353_, lean_object* v_a_354_, lean_object* v_b_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___redArg(v___x_349_, v___x_350_, v___x_351_, v_a_354_, v_b_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object* v___x_357_, lean_object* v___x_358_, lean_object* v___x_359_, lean_object* v_inst_360_, lean_object* v_R_361_, lean_object* v_a_362_, lean_object* v_b_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_357_, v___x_358_, v___x_359_, v_inst_360_, v_R_361_, v_a_362_, v_b_363_);
lean_dec_ref(v___x_358_);
return v_res_364_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(lean_object* v___x_365_, lean_object* v___x_366_, lean_object* v___x_367_, lean_object* v_inst_368_, lean_object* v_R_369_, lean_object* v_a_370_, uint8_t v_b_371_, lean_object* v_c_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___redArg(v___x_365_, v___x_366_, v___x_367_, v_a_370_, v_b_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2___boxed(lean_object* v___x_374_, lean_object* v___x_375_, lean_object* v___x_376_, lean_object* v_inst_377_, lean_object* v_R_378_, lean_object* v_a_379_, lean_object* v_b_380_, lean_object* v_c_381_){
_start:
{
uint8_t v_b_boxed_382_; uint8_t v_res_383_; lean_object* v_r_384_; 
v_b_boxed_382_ = lean_unbox(v_b_380_);
v_res_383_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2_spec__2(v___x_374_, v___x_375_, v___x_376_, v_inst_377_, v_R_378_, v_a_379_, v_b_boxed_382_, v_c_381_);
lean_dec_ref(v___x_375_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(lean_object* v___x_385_, lean_object* v___x_386_, lean_object* v___x_387_, lean_object* v_inst_388_, lean_object* v_R_389_, lean_object* v_a_390_, lean_object* v_b_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___redArg(v___x_385_, v___x_386_, v___x_387_, v_a_390_, v_b_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4___boxed(lean_object* v___x_393_, lean_object* v___x_394_, lean_object* v___x_395_, lean_object* v_inst_396_, lean_object* v_R_397_, lean_object* v_a_398_, lean_object* v_b_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__4(v___x_393_, v___x_394_, v___x_395_, v_inst_396_, v_R_397_, v_a_398_, v_b_399_);
lean_dec_ref(v___x_394_);
return v_res_400_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqContentLength_beq(lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = lean_nat_dec_eq(v_x_401_, v_x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqContentLength_beq___boxed(lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Std_Http_Header_instBEqContentLength_beq(v_x_404_, v_x_405_);
lean_dec(v_x_405_);
lean_dec(v_x_404_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprContentLength_repr_spec__0(lean_object* v_a_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = lean_nat_to_int(v_a_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_unsigned_to_nat(10u);
v___x_426_ = lean_nat_to_int(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0));
v___x_429_ = lean_string_length(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9);
v___x_431_ = lean_nat_to_int(v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg(lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_437_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6));
v___x_438_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_439_ = l_Nat_reprFast(v_x_436_);
v___x_440_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
v___x_441_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_438_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = 0;
v___x_443_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_443_, 0, v___x_441_);
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*1, v___x_442_);
v___x_444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_437_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_446_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_447_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_444_);
v___x_448_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_449_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
v___x_450_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_445_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
v___x_451_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*1, v___x_442_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr(lean_object* v_x_452_, lean_object* v_prec_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_Http_Header_instReprContentLength_repr___redArg(v_x_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___boxed(lean_object* v_x_455_, lean_object* v_prec_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_Http_Header_instReprContentLength_repr(v_x_455_, v_prec_456_);
lean_dec(v_prec_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_parse(lean_object* v_v_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_string_utf8_byte_size(v_v_460_);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v_v_460_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
lean_ctor_set(v___x_463_, 2, v___x_462_);
v___x_464_ = l_String_Slice_toNat_x3f(v___x_463_);
lean_dec_ref(v___x_463_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v___x_465_; 
v___x_465_ = lean_box(0);
return v___x_465_;
}
else
{
lean_object* v_val_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
v_val_466_ = lean_ctor_get(v___x_464_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_464_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_val_466_);
lean_dec(v___x_464_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_val_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_serialize(lean_object* v_h_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_475_ = l_Std_Http_Header_Name_contentLength;
v___x_476_ = l_Nat_reprFast(v_h_474_);
v___x_477_ = l_Std_Http_Header_Value_ofString_x21(v___x_476_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_475_);
lean_ctor_set(v___x_478_, 1, v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
if (lean_obj_tag(v_x_486_) == 0)
{
uint8_t v___x_487_; 
v___x_487_ = 1;
return v___x_487_;
}
else
{
uint8_t v___x_488_; 
v___x_488_ = 0;
return v___x_488_;
}
}
else
{
if (lean_obj_tag(v_x_486_) == 0)
{
uint8_t v___x_489_; 
v___x_489_ = 0;
return v___x_489_;
}
else
{
lean_object* v_val_490_; lean_object* v_val_491_; uint8_t v___x_492_; 
v_val_490_ = lean_ctor_get(v_x_485_, 0);
v_val_491_ = lean_ctor_get(v_x_486_, 0);
v___x_492_ = lean_string_dec_eq(v_val_490_, v_val_491_);
return v___x_492_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_493_, v_x_494_);
lean_dec(v_x_494_);
lean_dec(v_x_493_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object* v_as_498_, size_t v_i_499_, size_t v_stop_500_, lean_object* v_b_501_){
_start:
{
lean_object* v___y_503_; uint8_t v___x_507_; 
v___x_507_ = lean_usize_dec_eq(v_i_499_, v_stop_500_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_508_ = lean_array_uget_borrowed(v_as_498_, v_i_499_);
v___x_509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_510_ = lean_string_dec_eq(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
v___y_503_ = v_b_501_;
goto v___jp_502_;
}
else
{
lean_object* v___x_511_; 
lean_inc(v___x_508_);
v___x_511_ = lean_array_push(v_b_501_, v___x_508_);
v___y_503_ = v___x_511_;
goto v___jp_502_;
}
}
else
{
return v_b_501_;
}
v___jp_502_:
{
size_t v___x_504_; size_t v___x_505_; 
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_499_, v___x_504_);
v_i_499_ = v___x_505_;
v_b_501_ = v___y_503_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object* v_as_512_, lean_object* v_i_513_, lean_object* v_stop_514_, lean_object* v_b_515_){
_start:
{
size_t v_i_boxed_516_; size_t v_stop_boxed_517_; lean_object* v_res_518_; 
v_i_boxed_516_ = lean_unbox_usize(v_i_513_);
lean_dec(v_i_513_);
v_stop_boxed_517_ = lean_unbox_usize(v_stop_514_);
lean_dec(v_stop_514_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_512_, v_i_boxed_516_, v_stop_boxed_517_, v_b_515_);
lean_dec_ref(v_as_512_);
return v_res_518_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object* v___x_519_, lean_object* v_as_520_, size_t v_i_521_, size_t v_stop_522_){
_start:
{
uint8_t v___x_523_; 
v___x_523_ = lean_usize_dec_eq(v_i_521_, v_stop_522_);
if (v___x_523_ == 0)
{
uint8_t v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_524_ = 1;
v___x_525_ = lean_array_uget_borrowed(v_as_520_, v_i_521_);
lean_inc(v___x_525_);
v___x_526_ = l_Std_Http_Internal_isToken(v___x_525_);
if (v___x_526_ == 0)
{
return v___x_524_;
}
else
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_nat_dec_eq(v___x_519_, v___x_527_);
if (v___x_528_ == 0)
{
size_t v___x_529_; size_t v___x_530_; 
v___x_529_ = ((size_t)1ULL);
v___x_530_ = lean_usize_add(v_i_521_, v___x_529_);
v_i_521_ = v___x_530_;
goto _start;
}
else
{
return v___x_524_;
}
}
}
else
{
uint8_t v___x_532_; 
v___x_532_ = 0;
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object* v___x_533_, lean_object* v_as_534_, lean_object* v_i_535_, lean_object* v_stop_536_){
_start:
{
size_t v_i_boxed_537_; size_t v_stop_boxed_538_; uint8_t v_res_539_; lean_object* v_r_540_; 
v_i_boxed_537_ = lean_unbox_usize(v_i_535_);
lean_dec(v_i_535_);
v_stop_boxed_538_ = lean_unbox_usize(v_stop_536_);
lean_dec(v_stop_536_);
v_res_539_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_533_, v_as_534_, v_i_boxed_537_, v_stop_boxed_538_);
lean_dec_ref(v_as_534_);
lean_dec(v___x_533_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object* v_codings_545_){
_start:
{
uint8_t v___y_547_; uint8_t v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; uint8_t v___y_557_; uint8_t v___y_558_; lean_object* v___y_559_; uint8_t v___y_569_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = lean_array_get_size(v_codings_545_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_nat_dec_eq(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_lt(v___x_584_, v___x_583_);
if (v___x_586_ == 0)
{
v___y_569_ = v___x_585_;
goto v___jp_568_;
}
else
{
if (v___x_586_ == 0)
{
v___y_569_ = v___x_585_;
goto v___jp_568_;
}
else
{
size_t v___x_587_; size_t v___x_588_; uint8_t v___x_589_; 
v___x_587_ = ((size_t)0ULL);
v___x_588_ = lean_usize_of_nat(v___x_583_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_583_, v_codings_545_, v___x_587_, v___x_588_);
v___y_569_ = v___x_589_;
goto v___jp_568_;
}
}
}
else
{
v___y_569_ = v___x_585_;
goto v___jp_568_;
}
v___jp_546_:
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = lean_nat_dec_lt(v___x_551_, v___y_549_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; 
v___x_553_ = lean_nat_dec_eq(v___y_549_, v___x_551_);
lean_dec(v___y_549_);
if (v___x_553_ == 0)
{
lean_dec(v___y_550_);
if (v___x_553_ == 0)
{
return v___y_548_;
}
else
{
return v___y_547_;
}
}
else
{
lean_object* v___x_554_; uint8_t v_lastIsChunked_555_; 
v___x_554_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v_lastIsChunked_555_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_550_, v___x_554_);
lean_dec(v___y_550_);
if (v_lastIsChunked_555_ == 0)
{
if (v___x_553_ == 0)
{
return v___y_548_;
}
else
{
return v___y_547_;
}
}
else
{
return v___y_548_;
}
}
}
else
{
lean_dec(v___y_550_);
lean_dec(v___y_549_);
return v___y_547_;
}
}
v___jp_556_:
{
lean_object* v_chunkedCount_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_chunkedCount_560_ = lean_array_get_size(v___y_559_);
lean_dec_ref(v___y_559_);
v___x_561_ = lean_array_get_size(v_codings_545_);
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_sub(v___x_561_, v___x_562_);
v___x_564_ = lean_nat_dec_lt(v___x_563_, v___x_561_);
if (v___x_564_ == 0)
{
lean_object* v___x_565_; 
lean_dec(v___x_563_);
v___x_565_ = lean_box(0);
v___y_547_ = v___y_557_;
v___y_548_ = v___y_558_;
v___y_549_ = v_chunkedCount_560_;
v___y_550_ = v___x_565_;
goto v___jp_546_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_array_fget_borrowed(v_codings_545_, v___x_563_);
lean_dec(v___x_563_);
lean_inc(v___x_566_);
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___y_547_ = v___y_557_;
v___y_548_ = v___y_558_;
v___y_549_ = v_chunkedCount_560_;
v___y_550_ = v___x_567_;
goto v___jp_546_;
}
}
v___jp_568_:
{
if (v___y_569_ == 0)
{
uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_570_ = 1;
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_array_get_size(v_codings_545_);
v___x_573_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__1));
v___x_574_ = lean_nat_dec_lt(v___x_571_, v___x_572_);
if (v___x_574_ == 0)
{
v___y_557_ = v___y_569_;
v___y_558_ = v___x_570_;
v___y_559_ = v___x_573_;
goto v___jp_556_;
}
else
{
uint8_t v___x_575_; 
v___x_575_ = lean_nat_dec_le(v___x_572_, v___x_572_);
if (v___x_575_ == 0)
{
if (v___x_574_ == 0)
{
v___y_557_ = v___y_569_;
v___y_558_ = v___x_570_;
v___y_559_ = v___x_573_;
goto v___jp_556_;
}
else
{
size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((size_t)0ULL);
v___x_577_ = lean_usize_of_nat(v___x_572_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_545_, v___x_576_, v___x_577_, v___x_573_);
v___y_557_ = v___y_569_;
v___y_558_ = v___x_570_;
v___y_559_ = v___x_578_;
goto v___jp_556_;
}
}
else
{
size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; 
v___x_579_ = ((size_t)0ULL);
v___x_580_ = lean_usize_of_nat(v___x_572_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_545_, v___x_579_, v___x_580_, v___x_573_);
v___y_557_ = v___y_569_;
v___y_558_ = v___x_570_;
v___y_559_ = v___x_581_;
goto v___jp_556_;
}
}
}
else
{
uint8_t v___x_582_; 
v___x_582_ = 0;
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_Validate___boxed(lean_object* v_codings_590_){
_start:
{
uint8_t v_res_591_; lean_object* v_r_592_; 
v_res_591_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_590_);
lean_dec_ref(v_codings_590_);
v_r_592_ = lean_box(v_res_591_);
return v_r_592_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(lean_object* v___y_593_){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_String_quote(v___y_593_);
v___x_595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_dec(v_x_596_);
return v_x_597_;
}
else
{
lean_object* v_head_599_; lean_object* v_tail_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_611_; 
v_head_599_ = lean_ctor_get(v_x_598_, 0);
v_tail_600_ = lean_ctor_get(v_x_598_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_611_ == 0)
{
v___x_602_ = v_x_598_;
v_isShared_603_ = v_isSharedCheck_611_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_tail_600_);
lean_inc(v_head_599_);
lean_dec(v_x_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_611_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
lean_inc(v_x_596_);
if (v_isShared_603_ == 0)
{
lean_ctor_set_tag(v___x_602_, 5);
lean_ctor_set(v___x_602_, 1, v_x_596_);
lean_ctor_set(v___x_602_, 0, v_x_597_);
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_x_597_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_x_596_);
v___x_605_ = v_reuseFailAlloc_610_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_606_ = l_String_quote(v_head_599_);
v___x_607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
v___x_608_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v_x_597_ = v___x_608_;
v_x_598_ = v_tail_600_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
if (lean_obj_tag(v_x_614_) == 0)
{
lean_dec(v_x_612_);
return v_x_613_;
}
else
{
lean_object* v_head_615_; lean_object* v_tail_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_627_; 
v_head_615_ = lean_ctor_get(v_x_614_, 0);
v_tail_616_ = lean_ctor_get(v_x_614_, 1);
v_isSharedCheck_627_ = !lean_is_exclusive(v_x_614_);
if (v_isSharedCheck_627_ == 0)
{
v___x_618_ = v_x_614_;
v_isShared_619_ = v_isSharedCheck_627_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_tail_616_);
lean_inc(v_head_615_);
lean_dec(v_x_614_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_627_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
lean_inc(v_x_612_);
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 5);
lean_ctor_set(v___x_618_, 1, v_x_612_);
lean_ctor_set(v___x_618_, 0, v_x_613_);
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_x_613_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_x_612_);
v___x_621_ = v_reuseFailAlloc_626_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_622_ = l_String_quote(v_head_615_);
v___x_623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
v___x_624_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_621_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(v_x_612_, v___x_624_, v_tail_616_);
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
lean_object* v___x_630_; 
lean_dec(v_x_629_);
v___x_630_ = lean_box(0);
return v___x_630_;
}
else
{
lean_object* v_tail_631_; 
v_tail_631_ = lean_ctor_get(v_x_628_, 1);
if (lean_obj_tag(v_tail_631_) == 0)
{
lean_object* v_head_632_; lean_object* v___x_633_; 
lean_dec(v_x_629_);
v_head_632_ = lean_ctor_get(v_x_628_, 0);
lean_inc(v_head_632_);
lean_dec_ref(v_x_628_);
v___x_633_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_632_);
return v___x_633_;
}
else
{
lean_object* v_head_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
lean_inc(v_tail_631_);
v_head_634_ = lean_ctor_get(v_x_628_, 0);
lean_inc(v_head_634_);
lean_dec_ref(v_x_628_);
v___x_635_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_634_);
v___x_636_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(v_x_629_, v___x_635_, v_tail_631_);
return v___x_636_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0));
v___x_646_ = lean_string_length(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5);
v___x_648_ = lean_nat_to_int(v___x_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(lean_object* v_xs_656_){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_657_ = lean_array_get_size(v_xs_656_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_nat_dec_eq(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_660_ = lean_array_to_list(v_xs_656_);
v___x_661_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3));
v___x_662_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(v___x_660_, v___x_661_);
v___x_663_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6);
v___x_664_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7));
v___x_665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___x_662_);
v___x_666_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8));
v___x_667_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_663_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Std_Format_fill(v___x_668_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; 
lean_dec_ref(v_xs_656_);
v___x_670_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10));
return v___x_670_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_unsigned_to_nat(11u);
v___x_681_ = lean_nat_to_int(v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg(lean_object* v_x_688_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_689_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_690_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3));
v___x_691_ = lean_obj_once(&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4, &l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4);
v___x_692_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_688_);
v___x_693_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_691_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = 0;
v___x_695_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set_uint8(v___x_695_, sizeof(void*)*1, v___x_694_);
v___x_696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_690_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_696_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = lean_box(1);
v___x_700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6));
v___x_702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___x_689_);
v___x_704_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_707_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_708_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v___x_705_);
v___x_709_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_710_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_706_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set_uint8(v___x_712_, sizeof(void*)*1, v___x_694_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr(lean_object* v_x_713_, lean_object* v_prec_714_){
_start:
{
lean_object* v___x_715_; 
v___x_715_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg(v_x_713_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___boxed(lean_object* v_x_716_, lean_object* v_prec_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_Http_Header_instReprTransferEncoding_repr(v_x_716_, v_prec_717_);
lean_dec(v_prec_717_);
return v_res_718_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object* v_te_721_){
_start:
{
lean_object* v___y_723_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_726_ = lean_array_get_size(v_te_721_);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_nat_sub(v___x_726_, v___x_727_);
v___x_729_ = lean_nat_dec_lt(v___x_728_, v___x_726_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_dec(v___x_728_);
v___x_730_ = lean_box(0);
v___y_723_ = v___x_730_;
goto v___jp_722_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_array_fget_borrowed(v_te_721_, v___x_728_);
lean_dec(v___x_728_);
lean_inc(v___x_731_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
v___y_723_ = v___x_732_;
goto v___jp_722_;
}
v___jp_722_:
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v___x_725_ = l_Option_instBEq_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_723_, v___x_724_);
lean_dec(v___y_723_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_isChunked___boxed(lean_object* v_te_733_){
_start:
{
uint8_t v_res_734_; lean_object* v_r_735_; 
v_res_734_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_733_);
lean_dec_ref(v_te_733_);
v_r_735_ = lean_box(v_res_734_);
return v_r_735_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object* v_v_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_738_; 
v___x_738_ = lean_box(0);
return v___x_738_;
}
else
{
lean_object* v_val_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_748_; 
v_val_739_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_748_ == 0)
{
v___x_741_ = v___x_737_;
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_val_739_);
lean_dec(v___x_737_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_748_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
uint8_t v___x_743_; 
v___x_743_ = l_Std_Http_Header_TransferEncoding_Validate(v_val_739_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_del_object(v___x_741_);
lean_dec(v_val_739_);
v___x_744_ = lean_box(0);
return v___x_744_;
}
else
{
lean_object* v___x_746_; 
if (v_isShared_742_ == 0)
{
v___x_746_ = v___x_741_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_val_739_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_serialize(lean_object* v_te_749_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_value_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_750_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_751_ = lean_array_to_list(v_te_749_);
v_value_752_ = l_String_intercalate(v___x_750_, v___x_751_);
v___x_753_ = l_Std_Http_Header_Name_transferEncoding;
v___x_754_ = l_Std_Http_Header_Value_ofString_x21(v_value_752_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___redArg(lean_object* v_x_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_775_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_776_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__3));
v___x_777_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_778_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_774_);
v___x_779_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_777_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = 0;
v___x_781_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*1, v___x_780_);
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_776_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_box(1);
v___x_786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_784_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__5));
v___x_788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_786_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___x_789_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
lean_ctor_set(v___x_789_, 1, v___x_775_);
v___x_790_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_791_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_793_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_794_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___x_791_);
v___x_795_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_796_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_792_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set_uint8(v___x_798_, sizeof(void*)*1, v___x_780_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr(lean_object* v_x_799_, lean_object* v_prec_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_Http_Header_instReprConnection_repr___redArg(v_x_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___boxed(lean_object* v_x_802_, lean_object* v_prec_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_Http_Header_instReprConnection_repr(v_x_802_, v_prec_803_);
lean_dec(v_prec_803_);
return v_res_804_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(lean_object* v_token_807_, lean_object* v_as_808_, size_t v_i_809_, size_t v_stop_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = lean_usize_dec_eq(v_i_809_, v_stop_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_812_ = lean_array_uget_borrowed(v_as_808_, v_i_809_);
v___x_813_ = lean_string_dec_eq(v___x_812_, v_token_807_);
if (v___x_813_ == 0)
{
size_t v___x_814_; size_t v___x_815_; 
v___x_814_ = ((size_t)1ULL);
v___x_815_ = lean_usize_add(v_i_809_, v___x_814_);
v_i_809_ = v___x_815_;
goto _start;
}
else
{
return v___x_813_;
}
}
else
{
uint8_t v___x_817_; 
v___x_817_ = 0;
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(lean_object* v_token_818_, lean_object* v_as_819_, lean_object* v_i_820_, lean_object* v_stop_821_){
_start:
{
size_t v_i_boxed_822_; size_t v_stop_boxed_823_; uint8_t v_res_824_; lean_object* v_r_825_; 
v_i_boxed_822_ = lean_unbox_usize(v_i_820_);
lean_dec(v_i_820_);
v_stop_boxed_823_ = lean_unbox_usize(v_stop_821_);
lean_dec(v_stop_821_);
v_res_824_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_818_, v_as_819_, v_i_boxed_822_, v_stop_boxed_823_);
lean_dec_ref(v_as_819_);
lean_dec_ref(v_token_818_);
v_r_825_ = lean_box(v_res_824_);
return v_r_825_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_containsToken(lean_object* v_connection_826_, lean_object* v_token_827_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_array_get_size(v_connection_826_);
v___x_830_ = lean_nat_dec_lt(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_dec_ref(v_token_827_);
return v___x_830_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = lean_string_utf8_byte_size(v_token_827_);
if (v___x_830_ == 0)
{
lean_dec_ref(v_token_827_);
return v___x_830_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_token_835_; size_t v___x_836_; size_t v___x_837_; uint8_t v___x_838_; 
v___x_832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_832_, 0, v_token_827_);
lean_ctor_set(v___x_832_, 1, v___x_828_);
lean_ctor_set(v___x_832_, 2, v___x_831_);
v___x_833_ = l_String_Slice_trimAscii(v___x_832_);
v___x_834_ = l_String_Slice_toString(v___x_833_);
lean_dec_ref(v___x_833_);
v_token_835_ = l_String_mapAux___at___00__private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_834_, v___x_828_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_of_nat(v___x_829_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_835_, v_connection_826_, v___x_836_, v___x_837_);
lean_dec_ref(v_token_835_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_containsToken___boxed(lean_object* v_connection_839_, lean_object* v_token_840_){
_start:
{
uint8_t v_res_841_; lean_object* v_r_842_; 
v_res_841_ = l_Std_Http_Header_Connection_containsToken(v_connection_839_, v_token_840_);
lean_dec_ref(v_connection_839_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_shouldClose(lean_object* v_connection_844_){
_start:
{
lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_845_ = ((lean_object*)(l_Std_Http_Header_Connection_shouldClose___closed__0));
v___x_846_ = l_Std_Http_Header_Connection_containsToken(v_connection_844_, v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_shouldClose___boxed(lean_object* v_connection_847_){
_start:
{
uint8_t v_res_848_; lean_object* v_r_849_; 
v_res_848_ = l_Std_Http_Header_Connection_shouldClose(v_connection_847_);
lean_dec_ref(v_connection_847_);
v_r_849_ = lean_box(v_res_848_);
return v_r_849_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(lean_object* v_as_850_, size_t v_i_851_, size_t v_stop_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_eq(v_i_851_, v_stop_852_);
if (v___x_853_ == 0)
{
uint8_t v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v___x_854_ = 1;
v___x_855_ = lean_array_uget_borrowed(v_as_850_, v_i_851_);
lean_inc(v___x_855_);
v___x_856_ = l_Std_Http_Internal_isToken(v___x_855_);
if (v___x_856_ == 0)
{
return v___x_854_;
}
else
{
if (v___x_853_ == 0)
{
size_t v___x_857_; size_t v___x_858_; 
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_add(v_i_851_, v___x_857_);
v_i_851_ = v___x_858_;
goto _start;
}
else
{
return v___x_854_;
}
}
}
else
{
uint8_t v___x_860_; 
v___x_860_ = 0;
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(lean_object* v_as_861_, lean_object* v_i_862_, lean_object* v_stop_863_){
_start:
{
size_t v_i_boxed_864_; size_t v_stop_boxed_865_; uint8_t v_res_866_; lean_object* v_r_867_; 
v_i_boxed_864_ = lean_unbox_usize(v_i_862_);
lean_dec(v_i_862_);
v_stop_boxed_865_ = lean_unbox_usize(v_stop_863_);
lean_dec(v_stop_863_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_861_, v_i_boxed_864_, v_stop_boxed_865_);
lean_dec_ref(v_as_861_);
v_r_867_ = lean_box(v_res_866_);
return v_r_867_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_parse(lean_object* v_v_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l___private_Std_Internal_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v___x_870_; 
v___x_870_ = lean_box(0);
return v___x_870_;
}
else
{
lean_object* v_val_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_891_; 
v_val_871_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_891_ == 0)
{
v___x_873_ = v___x_869_;
v_isShared_874_ = v_isSharedCheck_891_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_val_871_);
lean_dec(v___x_869_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_891_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = lean_array_get_size(v_val_871_);
v___x_877_ = lean_nat_dec_lt(v___x_875_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_879_; 
if (v_isShared_874_ == 0)
{
v___x_879_ = v___x_873_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_val_871_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
if (v___x_877_ == 0)
{
lean_object* v___x_882_; 
if (v_isShared_874_ == 0)
{
v___x_882_ = v___x_873_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_val_871_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
else
{
size_t v___x_884_; size_t v___x_885_; uint8_t v___x_886_; 
v___x_884_ = ((size_t)0ULL);
v___x_885_ = lean_usize_of_nat(v___x_876_);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_val_871_, v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_888_; 
if (v_isShared_874_ == 0)
{
v___x_888_ = v___x_873_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_val_871_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
else
{
lean_object* v___x_890_; 
lean_del_object(v___x_873_);
lean_dec(v_val_871_);
v___x_890_ = lean_box(0);
return v___x_890_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_serialize(lean_object* v_connection_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v_value_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_893_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_894_ = lean_array_to_list(v_connection_892_);
v_value_895_ = l_String_intercalate(v___x_893_, v___x_894_);
v___x_896_ = l_Std_Http_Header_Name_connection;
v___x_897_ = l_Std_Http_Header_Value_ofString_x21(v_value_895_);
v___x_898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
return v___x_898_;
}
}
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers_Name(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Http_Data_Headers_Value(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Parsec_Basic(uint8_t builtin);
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

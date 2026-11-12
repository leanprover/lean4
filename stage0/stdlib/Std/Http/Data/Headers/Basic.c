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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Std_Http_URI_Parser_parseHostHeader(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_Http_Internal_isToken(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
lean_object* lean_array_mk(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Std_Http_Internal_unquoteHttpString_x3f(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_Http_Header_Name_instEncodeV11_go(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_byte_array_copy_slice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter___closed__0 = (const lean_object*)&l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter___closed__0_value;
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0_value)}};
static const lean_object* l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parseCodings_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_parseFieldLines_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_parseFieldLines_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parseFieldLines_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parseFieldLines_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f___boxed(lean_object*);
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
static const lean_ctor_object l_Std_Http_Header_Host_parse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*9 + 0, .m_other = 9, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(64) << 1) | 1)),((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1)),((lean_object*)(((size_t)(8192) << 1) | 1))}};
static const lean_object* l_Std_Http_Header_Host_parse___closed__0 = (const lean_object*)&l_Std_Http_Header_Host_parse___closed__0_value;
static const lean_closure_object l_Std_Http_Header_Host_parse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Header_Host_parse___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Http_Header_Host_parse___closed__0_value)} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__3(lean_object* v_as_87_, size_t v_i_88_, size_t v_stop_89_, lean_object* v_b_90_){
_start:
{
lean_object* v___y_92_; uint8_t v___x_96_; 
v___x_96_ = lean_usize_dec_eq(v_i_88_, v_stop_89_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v_part_101_; lean_object* v_startInclusive_102_; lean_object* v_endExclusive_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_97_ = lean_array_uget_borrowed(v_as_87_, v_i_88_);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = lean_string_utf8_byte_size(v___x_97_);
lean_inc(v___x_97_);
v___x_100_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_97_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
v_part_101_ = l_String_Slice_trimAscii(v___x_100_);
v_startInclusive_102_ = lean_ctor_get(v_part_101_, 1);
v_endExclusive_103_ = lean_ctor_get(v_part_101_, 2);
v___x_104_ = lean_nat_sub(v_endExclusive_103_, v_startInclusive_102_);
v___x_105_ = lean_nat_dec_eq(v___x_104_, v___x_98_);
lean_dec(v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = l_String_Slice_toString(v_part_101_);
lean_dec_ref(v_part_101_);
v___x_107_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_106_, v___x_98_);
v___x_108_ = lean_array_push(v_b_90_, v___x_107_);
v___y_92_ = v___x_108_;
goto v___jp_91_;
}
else
{
lean_dec_ref(v_part_101_);
v___y_92_ = v_b_90_;
goto v___jp_91_;
}
}
else
{
return v_b_90_;
}
v___jp_91_:
{
size_t v___x_93_; size_t v___x_94_; 
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_add(v_i_88_, v___x_93_);
v_i_88_ = v___x_94_;
v_b_90_ = v___y_92_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__3___boxed(lean_object* v_as_109_, lean_object* v_i_110_, lean_object* v_stop_111_, lean_object* v_b_112_){
_start:
{
size_t v_i_boxed_113_; size_t v_stop_boxed_114_; lean_object* v_res_115_; 
v_i_boxed_113_ = lean_unbox_usize(v_i_110_);
lean_dec(v_i_110_);
v_stop_boxed_114_ = lean_unbox_usize(v_stop_111_);
lean_dec(v_stop_111_);
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__3(v_as_109_, v_i_boxed_113_, v_stop_boxed_114_, v_b_112_);
lean_dec_ref(v_as_109_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(lean_object* v_as_118_, lean_object* v_start_119_, lean_object* v_stop_120_){
_start:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0));
v___x_122_ = lean_nat_dec_lt(v_start_119_, v_stop_120_);
if (v___x_122_ == 0)
{
return v___x_121_;
}
else
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_array_get_size(v_as_118_);
v___x_124_ = lean_nat_dec_le(v_stop_120_, v___x_123_);
if (v___x_124_ == 0)
{
uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_lt(v_start_119_, v___x_123_);
if (v___x_125_ == 0)
{
return v___x_121_;
}
else
{
size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_usize_of_nat(v_start_119_);
v___x_127_ = lean_usize_of_nat(v___x_123_);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__3(v_as_118_, v___x_126_, v___x_127_, v___x_121_);
return v___x_128_;
}
}
else
{
size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_usize_of_nat(v_start_119_);
v___x_130_ = lean_usize_of_nat(v_stop_120_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3_spec__3(v_as_118_, v___x_129_, v___x_130_, v___x_121_);
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___boxed(lean_object* v_as_132_, lean_object* v_start_133_, lean_object* v_stop_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v_as_132_, v_start_133_, v_stop_134_);
lean_dec(v_stop_134_);
lean_dec(v_start_133_);
lean_dec_ref(v_as_132_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(lean_object* v___x_136_, lean_object* v___x_137_, lean_object* v___x_138_, lean_object* v_a_139_, lean_object* v_b_140_){
_start:
{
lean_object* v_it_142_; lean_object* v_startInclusive_143_; lean_object* v_endExclusive_144_; 
if (lean_obj_tag(v_a_139_) == 0)
{
lean_object* v_currPos_149_; lean_object* v_searcher_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_173_; 
v_currPos_149_ = lean_ctor_get(v_a_139_, 0);
v_searcher_150_ = lean_ctor_get(v_a_139_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_a_139_);
if (v_isSharedCheck_173_ == 0)
{
v___x_152_ = v_a_139_;
v_isShared_153_ = v_isSharedCheck_173_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_searcher_150_);
lean_inc(v_currPos_149_);
lean_dec(v_a_139_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_173_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
uint8_t v_decide_154_; 
v_decide_154_ = lean_nat_dec_eq(v_searcher_150_, v___x_138_);
if (v_decide_154_ == 0)
{
uint32_t v___x_155_; uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_155_ = 44;
v___x_156_ = lean_string_utf8_get_fast(v___x_136_, v_searcher_150_);
v___x_157_ = lean_uint32_dec_eq(v___x_156_, v___x_155_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_160_; 
v___x_158_ = lean_string_utf8_next_fast(v___x_136_, v_searcher_150_);
lean_dec(v_searcher_150_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___x_158_);
v___x_160_ = v___x_152_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_currPos_149_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___x_158_);
v___x_160_ = v_reuseFailAlloc_162_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
v_a_139_ = v___x_160_;
goto _start;
}
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_slice_166_; lean_object* v_nextIt_168_; 
v___x_163_ = lean_string_utf8_next_fast(v___x_136_, v_searcher_150_);
v___x_164_ = lean_nat_sub(v___x_163_, v_searcher_150_);
v___x_165_ = lean_nat_add(v_searcher_150_, v___x_164_);
lean_dec(v___x_164_);
v_slice_166_ = l_String_Slice_subslice_x21(v___x_137_, v_currPos_149_, v_searcher_150_);
lean_inc(v___x_165_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___x_165_);
lean_ctor_set(v___x_152_, 0, v___x_165_);
v_nextIt_168_ = v___x_152_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_165_);
v_nextIt_168_ = v_reuseFailAlloc_171_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v_startInclusive_169_; lean_object* v_endExclusive_170_; 
v_startInclusive_169_ = lean_ctor_get(v_slice_166_, 0);
lean_inc(v_startInclusive_169_);
v_endExclusive_170_ = lean_ctor_get(v_slice_166_, 1);
lean_inc(v_endExclusive_170_);
lean_dec_ref(v_slice_166_);
v_it_142_ = v_nextIt_168_;
v_startInclusive_143_ = v_startInclusive_169_;
v_endExclusive_144_ = v_endExclusive_170_;
goto v___jp_141_;
}
}
}
else
{
lean_object* v___x_172_; 
lean_del_object(v___x_152_);
lean_dec(v_searcher_150_);
v___x_172_ = lean_box(1);
lean_inc(v___x_138_);
v_it_142_ = v___x_172_;
v_startInclusive_143_ = v_currPos_149_;
v_endExclusive_144_ = v___x_138_;
goto v___jp_141_;
}
}
}
else
{
lean_dec(v___x_138_);
lean_dec_ref(v___x_136_);
return v_b_140_;
}
v___jp_141_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
lean_inc_ref(v___x_136_);
v___x_145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_136_);
lean_ctor_set(v___x_145_, 1, v_startInclusive_143_);
lean_ctor_set(v___x_145_, 2, v_endExclusive_144_);
v___x_146_ = l_String_Slice_toString(v___x_145_);
lean_dec_ref_known(v___x_145_, 3);
v___x_147_ = lean_array_push(v_b_140_, v___x_146_);
v_a_139_ = v_it_142_;
v_b_140_ = v___x_147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg___boxed(lean_object* v___x_174_, lean_object* v___x_175_, lean_object* v___x_176_, lean_object* v_a_177_, lean_object* v_b_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_174_, v___x_175_, v___x_176_, v_a_177_, v_b_178_);
lean_dec_ref(v___x_175_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(lean_object* v_v_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_string_utf8_byte_size(v_v_180_);
lean_inc_ref(v_v_180_);
v___x_183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_183_, 0, v_v_180_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
lean_ctor_set(v___x_183_, 2, v___x_182_);
v___x_184_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
v___x_185_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0));
v___x_186_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_180_, v___x_183_, v___x_182_, v___x_184_, v___x_185_);
lean_dec_ref_known(v___x_183_, 3);
v___x_187_ = lean_array_to_list(v___x_186_);
v___x_188_ = lean_array_mk(v___x_187_);
v___x_189_ = lean_array_get_size(v___x_188_);
v___x_190_ = l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3(v___x_188_, v___x_181_, v___x_189_);
lean_dec_ref(v___x_188_);
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(lean_object* v___x_192_, lean_object* v___x_193_, lean_object* v___x_194_, lean_object* v_inst_195_, lean_object* v_R_196_, lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v___x_192_, v___x_193_, v___x_194_, v_a_197_, v_b_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___boxed(lean_object* v___x_200_, lean_object* v___x_201_, lean_object* v___x_202_, lean_object* v_inst_203_, lean_object* v_R_204_, lean_object* v_a_205_, lean_object* v_b_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2(v___x_200_, v___x_201_, v___x_202_, v_inst_203_, v_R_204_, v_a_205_, v_b_206_);
lean_dec_ref(v___x_201_);
return v_res_207_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqContentLength_beq(lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = lean_nat_dec_eq(v_x_208_, v_x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqContentLength_beq___boxed(lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
uint8_t v_res_213_; lean_object* v_r_214_; 
v_res_213_ = l_Std_Http_Header_instBEqContentLength_beq(v_x_211_, v_x_212_);
lean_dec(v_x_212_);
lean_dec(v_x_211_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Std_Http_Header_instReprContentLength_repr_spec__0(lean_object* v_a_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_nat_to_int(v_a_217_);
return v___x_218_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = lean_unsigned_to_nat(10u);
v___x_233_ = lean_nat_to_int(v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__0));
v___x_236_ = lean_string_length(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__9);
v___x_238_ = lean_nat_to_int(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___redArg(lean_object* v_x_243_){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_244_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__6));
v___x_245_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_246_ = l_Nat_reprFast(v_x_243_);
v___x_247_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
v___x_248_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_245_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = 0;
v___x_250_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set_uint8(v___x_250_, sizeof(void*)*1, v___x_249_);
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_244_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_253_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_254_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___x_251_);
v___x_255_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_252_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_249_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr(lean_object* v_x_259_, lean_object* v_prec_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Std_Http_Header_instReprContentLength_repr___redArg(v_x_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprContentLength_repr___boxed(lean_object* v_x_262_, lean_object* v_prec_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Std_Http_Header_instReprContentLength_repr(v_x_262_, v_prec_263_);
lean_dec(v_prec_263_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(lean_object* v_s_267_, lean_object* v_pos_268_){
_start:
{
lean_object* v_str_269_; lean_object* v_startInclusive_270_; lean_object* v_endExclusive_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v_decide_275_; 
v_str_269_ = lean_ctor_get(v_s_267_, 0);
v_startInclusive_270_ = lean_ctor_get(v_s_267_, 1);
v_endExclusive_271_ = lean_ctor_get(v_s_267_, 2);
v___x_272_ = lean_nat_add(v_startInclusive_270_, v_pos_268_);
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_nat_sub(v_endExclusive_271_, v___x_272_);
v_decide_275_ = lean_nat_dec_eq(v___x_273_, v___x_274_);
lean_dec(v___x_274_);
if (v_decide_275_ == 0)
{
uint32_t v___x_276_; uint32_t v___x_277_; uint8_t v___x_278_; 
v___x_276_ = lean_string_utf8_get_fast(v_str_269_, v___x_272_);
v___x_277_ = 48;
v___x_278_ = lean_uint32_dec_le(v___x_277_, v___x_276_);
if (v___x_278_ == 0)
{
lean_dec(v___x_272_);
return v_pos_268_;
}
else
{
uint32_t v___x_279_; uint8_t v___x_280_; 
v___x_279_ = 57;
v___x_280_ = lean_uint32_dec_le(v___x_276_, v___x_279_);
if (v___x_280_ == 0)
{
lean_dec(v___x_272_);
return v_pos_268_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_281_ = lean_string_utf8_next_fast(v_str_269_, v___x_272_);
v___x_282_ = lean_nat_sub(v___x_281_, v___x_272_);
lean_dec(v___x_272_);
v___x_283_ = lean_nat_add(v_pos_268_, v___x_282_);
lean_dec(v___x_282_);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_pos_268_, v___x_284_);
v___x_286_ = lean_nat_dec_le(v___x_285_, v___x_283_);
lean_dec(v___x_285_);
if (v___x_286_ == 0)
{
lean_dec(v___x_283_);
return v_pos_268_;
}
else
{
lean_dec(v_pos_268_);
v_pos_268_ = v___x_283_;
goto _start;
}
}
}
}
else
{
lean_dec(v___x_272_);
return v_pos_268_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0___boxed(lean_object* v_s_288_, lean_object* v_pos_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v_s_288_, v_pos_289_);
lean_dec_ref(v_s_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_parse(lean_object* v_v_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_292_ = lean_string_utf8_byte_size(v_v_291_);
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_nat_dec_eq(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v_decide_297_; 
v___x_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_295_, 0, v_v_291_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_292_);
v___x_296_ = l_String_Slice_Pos_skipWhile___at___00Std_Http_Header_ContentLength_parse_spec__0(v___x_295_, v___x_293_);
v_decide_297_ = lean_nat_dec_eq(v___x_296_, v___x_292_);
lean_dec(v___x_296_);
if (v_decide_297_ == 0)
{
lean_object* v___x_298_; 
lean_dec_ref_known(v___x_295_, 3);
v___x_298_ = lean_box(0);
return v___x_298_;
}
else
{
lean_object* v___x_299_; 
v___x_299_ = l_String_Slice_toNat_x3f(v___x_295_);
lean_dec_ref_known(v___x_295_, 3);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v_val_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
v_val_301_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_299_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_val_301_);
lean_dec(v___x_299_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_val_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
else
{
lean_object* v___x_309_; 
lean_dec_ref(v_v_291_);
v___x_309_ = lean_box(0);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_ContentLength_serialize(lean_object* v_h_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = l_Std_Http_Header_Name_contentLength;
v___x_312_ = l_Nat_reprFast(v_h_310_);
v___x_313_ = l_Std_Http_Header_Value_ofString_x21(v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_311_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
if (lean_obj_tag(v_x_322_) == 0)
{
uint8_t v___x_323_; 
v___x_323_ = 1;
return v___x_323_;
}
else
{
uint8_t v___x_324_; 
v___x_324_ = 0;
return v___x_324_;
}
}
else
{
if (lean_obj_tag(v_x_322_) == 0)
{
uint8_t v___x_325_; 
v___x_325_ = 0;
return v___x_325_;
}
else
{
lean_object* v_val_326_; lean_object* v_val_327_; uint8_t v___x_328_; 
v_val_326_ = lean_ctor_get(v_x_321_, 0);
v_val_327_ = lean_ctor_get(v_x_322_, 0);
v___x_328_ = lean_string_dec_eq(v_val_326_, v_val_327_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0___boxed(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v_x_329_, v_x_330_);
lean_dec(v_x_330_);
lean_dec(v_x_329_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(lean_object* v_as_334_, size_t v_i_335_, size_t v_stop_336_, lean_object* v_b_337_){
_start:
{
lean_object* v___y_339_; uint8_t v___x_343_; 
v___x_343_ = lean_usize_dec_eq(v_i_335_, v_stop_336_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = lean_array_uget_borrowed(v_as_334_, v_i_335_);
v___x_345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_346_ = lean_string_dec_eq(v___x_344_, v___x_345_);
if (v___x_346_ == 0)
{
v___y_339_ = v_b_337_;
goto v___jp_338_;
}
else
{
lean_object* v___x_347_; 
lean_inc(v___x_344_);
v___x_347_ = lean_array_push(v_b_337_, v___x_344_);
v___y_339_ = v___x_347_;
goto v___jp_338_;
}
}
else
{
return v_b_337_;
}
v___jp_338_:
{
size_t v___x_340_; size_t v___x_341_; 
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_add(v_i_335_, v___x_340_);
v_i_335_ = v___x_341_;
v_b_337_ = v___y_339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___boxed(lean_object* v_as_348_, lean_object* v_i_349_, lean_object* v_stop_350_, lean_object* v_b_351_){
_start:
{
size_t v_i_boxed_352_; size_t v_stop_boxed_353_; lean_object* v_res_354_; 
v_i_boxed_352_ = lean_unbox_usize(v_i_349_);
lean_dec(v_i_349_);
v_stop_boxed_353_ = lean_unbox_usize(v_stop_350_);
lean_dec(v_stop_350_);
v_res_354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_as_348_, v_i_boxed_352_, v_stop_boxed_353_, v_b_351_);
lean_dec_ref(v_as_348_);
return v_res_354_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(lean_object* v___x_355_, lean_object* v_as_356_, size_t v_i_357_, size_t v_stop_358_){
_start:
{
uint8_t v___x_359_; 
v___x_359_ = lean_usize_dec_eq(v_i_357_, v_stop_358_);
if (v___x_359_ == 0)
{
uint8_t v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v___x_360_ = 1;
v___x_361_ = lean_array_uget_borrowed(v_as_356_, v_i_357_);
lean_inc(v___x_361_);
v___x_362_ = l_Std_Http_Internal_isToken(v___x_361_);
if (v___x_362_ == 0)
{
return v___x_360_;
}
else
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_nat_dec_eq(v___x_355_, v___x_363_);
if (v___x_364_ == 0)
{
size_t v___x_365_; size_t v___x_366_; 
v___x_365_ = ((size_t)1ULL);
v___x_366_ = lean_usize_add(v_i_357_, v___x_365_);
v_i_357_ = v___x_366_;
goto _start;
}
else
{
return v___x_360_;
}
}
}
else
{
uint8_t v___x_368_; 
v___x_368_ = 0;
return v___x_368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2___boxed(lean_object* v___x_369_, lean_object* v_as_370_, lean_object* v_i_371_, lean_object* v_stop_372_){
_start:
{
size_t v_i_boxed_373_; size_t v_stop_boxed_374_; uint8_t v_res_375_; lean_object* v_r_376_; 
v_i_boxed_373_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_stop_boxed_374_ = lean_unbox_usize(v_stop_372_);
lean_dec(v_stop_372_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_369_, v_as_370_, v_i_boxed_373_, v_stop_boxed_374_);
lean_dec_ref(v_as_370_);
lean_dec(v___x_369_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_Validate(lean_object* v_codings_379_){
_start:
{
lean_object* v___y_381_; uint8_t v___y_382_; uint8_t v___y_383_; lean_object* v___y_384_; uint8_t v___y_391_; uint8_t v___y_392_; lean_object* v___y_393_; uint8_t v___y_403_; lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_412_ = lean_array_get_size(v_codings_379_);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_nat_dec_eq(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
uint8_t v___x_415_; 
v___x_415_ = lean_nat_dec_lt(v___x_413_, v___x_412_);
if (v___x_415_ == 0)
{
v___y_403_ = v___x_415_;
goto v___jp_402_;
}
else
{
if (v___x_415_ == 0)
{
v___y_403_ = v___x_415_;
goto v___jp_402_;
}
else
{
size_t v___x_416_; size_t v___x_417_; uint8_t v___x_418_; 
v___x_416_ = ((size_t)0ULL);
v___x_417_ = lean_usize_of_nat(v___x_412_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_TransferEncoding_Validate_spec__2(v___x_412_, v_codings_379_, v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
v___y_403_ = v___x_418_;
goto v___jp_402_;
}
else
{
return v___x_414_;
}
}
}
}
else
{
uint8_t v___x_419_; 
v___x_419_ = 0;
return v___x_419_;
}
v___jp_380_:
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = lean_unsigned_to_nat(1u);
v___x_386_ = lean_nat_dec_lt(v___x_385_, v___y_381_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; 
v___x_387_ = lean_nat_dec_eq(v___y_381_, v___x_385_);
lean_dec(v___y_381_);
if (v___x_387_ == 0)
{
lean_dec(v___y_384_);
return v___y_382_;
}
else
{
lean_object* v___x_388_; uint8_t v_lastIsChunked_389_; 
v___x_388_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v_lastIsChunked_389_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_384_, v___x_388_);
lean_dec(v___y_384_);
if (v_lastIsChunked_389_ == 0)
{
return v___x_386_;
}
else
{
return v___y_382_;
}
}
}
else
{
lean_dec(v___y_384_);
lean_dec(v___y_381_);
return v___y_383_;
}
}
v___jp_390_:
{
lean_object* v_chunkedCount_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_chunkedCount_394_ = lean_array_get_size(v___y_393_);
lean_dec_ref(v___y_393_);
v___x_395_ = lean_array_get_size(v_codings_379_);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_sub(v___x_395_, v___x_396_);
v___x_398_ = lean_nat_dec_lt(v___x_397_, v___x_395_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec(v___x_397_);
v___x_399_ = lean_box(0);
v___y_381_ = v_chunkedCount_394_;
v___y_382_ = v___y_391_;
v___y_383_ = v___y_392_;
v___y_384_ = v___x_399_;
goto v___jp_380_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = lean_array_fget_borrowed(v_codings_379_, v___x_397_);
lean_dec(v___x_397_);
lean_inc(v___x_400_);
v___x_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
v___y_381_ = v_chunkedCount_394_;
v___y_382_ = v___y_391_;
v___y_383_ = v___y_392_;
v___y_384_ = v___x_401_;
goto v___jp_380_;
}
}
v___jp_402_:
{
uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_404_ = 1;
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_array_get_size(v_codings_379_);
v___x_407_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0));
v___x_408_ = lean_nat_dec_lt(v___x_405_, v___x_406_);
if (v___x_408_ == 0)
{
v___y_391_ = v___x_404_;
v___y_392_ = v___y_403_;
v___y_393_ = v___x_407_;
goto v___jp_390_;
}
else
{
size_t v___x_409_; size_t v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((size_t)0ULL);
v___x_410_ = lean_usize_of_nat(v___x_406_);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1(v_codings_379_, v___x_409_, v___x_410_, v___x_407_);
v___y_391_ = v___x_404_;
v___y_392_ = v___y_403_;
v___y_393_ = v___x_411_;
goto v___jp_390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_Validate___boxed(lean_object* v_codings_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Std_Http_Header_TransferEncoding_Validate(v_codings_420_);
lean_dec_ref(v_codings_420_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(lean_object* v___y_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = l_String_quote(v___y_423_);
v___x_425_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_428_) == 0)
{
lean_dec(v_x_426_);
return v_x_427_;
}
else
{
lean_object* v_head_429_; lean_object* v_tail_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_441_; 
v_head_429_ = lean_ctor_get(v_x_428_, 0);
v_tail_430_ = lean_ctor_get(v_x_428_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v_x_428_);
if (v_isSharedCheck_441_ == 0)
{
v___x_432_ = v_x_428_;
v_isShared_433_ = v_isSharedCheck_441_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_tail_430_);
lean_inc(v_head_429_);
lean_dec(v_x_428_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_441_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
lean_inc(v_x_426_);
if (v_isShared_433_ == 0)
{
lean_ctor_set_tag(v___x_432_, 5);
lean_ctor_set(v___x_432_, 1, v_x_426_);
lean_ctor_set(v___x_432_, 0, v_x_427_);
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_x_427_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_x_426_);
v___x_435_ = v_reuseFailAlloc_440_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = l_String_quote(v_head_429_);
v___x_437_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
v___x_438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_435_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
v_x_427_ = v___x_438_;
v_x_428_ = v_tail_430_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
if (lean_obj_tag(v_x_444_) == 0)
{
lean_dec(v_x_442_);
return v_x_443_;
}
else
{
lean_object* v_head_445_; lean_object* v_tail_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_457_; 
v_head_445_ = lean_ctor_get(v_x_444_, 0);
v_tail_446_ = lean_ctor_get(v_x_444_, 1);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_444_);
if (v_isSharedCheck_457_ == 0)
{
v___x_448_ = v_x_444_;
v_isShared_449_ = v_isSharedCheck_457_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_tail_446_);
lean_inc(v_head_445_);
lean_dec(v_x_444_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_457_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
lean_inc(v_x_442_);
if (v_isShared_449_ == 0)
{
lean_ctor_set_tag(v___x_448_, 5);
lean_ctor_set(v___x_448_, 1, v_x_442_);
lean_ctor_set(v___x_448_, 0, v_x_443_);
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_x_443_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_x_442_);
v___x_451_ = v_reuseFailAlloc_456_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_452_ = l_String_quote(v_head_445_);
v___x_453_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
v___x_454_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_451_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1_spec__2(v_x_442_, v___x_454_, v_tail_446_);
return v___x_455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_object* v___x_460_; 
lean_dec(v_x_459_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v_tail_461_; 
v_tail_461_ = lean_ctor_get(v_x_458_, 1);
if (lean_obj_tag(v_tail_461_) == 0)
{
lean_object* v_head_462_; lean_object* v___x_463_; 
lean_dec(v_x_459_);
v_head_462_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_head_462_);
lean_dec_ref_known(v_x_458_, 2);
v___x_463_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_462_);
return v___x_463_;
}
else
{
lean_object* v_head_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_inc(v_tail_461_);
v_head_464_ = lean_ctor_get(v_x_458_, 0);
lean_inc(v_head_464_);
lean_dec_ref_known(v_x_458_, 2);
v___x_465_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0___lam__0(v_head_464_);
v___x_466_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0_spec__1(v_x_459_, v___x_465_, v_tail_461_);
return v___x_466_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__0));
v___x_476_ = lean_string_length(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__5);
v___x_478_ = lean_nat_to_int(v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(lean_object* v_xs_486_){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_487_ = lean_array_get_size(v_xs_486_);
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = lean_nat_dec_eq(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_490_ = lean_array_to_list(v_xs_486_);
v___x_491_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__3));
v___x_492_ = l_Std_Format_joinSep___at___00Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0_spec__0(v___x_490_, v___x_491_);
v___x_493_ = lean_obj_once(&l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6, &l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6_once, _init_l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__6);
v___x_494_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__7));
v___x_495_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_492_);
v___x_496_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__8));
v___x_497_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_493_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = l_Std_Format_fill(v___x_498_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; 
lean_dec_ref(v_xs_486_);
v___x_500_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__10));
return v___x_500_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = lean_unsigned_to_nat(11u);
v___x_511_ = lean_nat_to_int(v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___redArg(lean_object* v_x_518_){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_519_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_520_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__3));
v___x_521_ = lean_obj_once(&l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4, &l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__4);
v___x_522_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_518_);
v___x_523_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = 0;
v___x_525_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*1, v___x_524_);
v___x_526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_520_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_526_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_box(1);
v___x_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__6));
v___x_532_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v___x_519_);
v___x_534_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
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
lean_ctor_set_uint8(v___x_542_, sizeof(void*)*1, v___x_524_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr(lean_object* v_x_543_, lean_object* v_prec_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_Http_Header_instReprTransferEncoding_repr___redArg(v_x_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprTransferEncoding_repr___boxed(lean_object* v_x_546_, lean_object* v_prec_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Std_Http_Header_instReprTransferEncoding_repr(v_x_546_, v_prec_547_);
lean_dec(v_prec_547_);
return v_res_548_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_TransferEncoding_isChunked(lean_object* v_te_551_){
_start:
{
lean_object* v___y_553_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_556_ = lean_array_get_size(v_te_551_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_sub(v___x_556_, v___x_557_);
v___x_559_ = lean_nat_dec_lt(v___x_558_, v___x_556_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
lean_dec(v___x_558_);
v___x_560_ = lean_box(0);
v___y_553_ = v___x_560_;
goto v___jp_552_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = lean_array_fget_borrowed(v_te_551_, v___x_558_);
lean_dec(v___x_558_);
lean_inc(v___x_561_);
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___y_553_ = v___x_562_;
goto v___jp_552_;
}
v___jp_552_:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v___x_555_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_553_, v___x_554_);
lean_dec(v___y_553_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_isChunked___boxed(lean_object* v_te_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_Std_Http_Header_TransferEncoding_isChunked(v_te_563_);
lean_dec_ref(v_te_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___redArg(){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___closed__0));
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___redArg___boxed(lean_object* v___dummy_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___redArg();
return v_res_569_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___closed__0(void){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___redArg();
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0(lean_object* v_s_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___closed__0);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___boxed(lean_object* v_s_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0(v_s_573_);
lean_dec_ref(v_s_573_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1___redArg(lean_object* v_param_575_, lean_object* v___x_576_, lean_object* v___x_577_, lean_object* v_a_578_, lean_object* v_b_579_){
_start:
{
lean_object* v_it_581_; lean_object* v_startInclusive_582_; lean_object* v_endExclusive_583_; 
if (lean_obj_tag(v_a_578_) == 0)
{
lean_object* v_currPos_588_; lean_object* v_searcher_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_612_; 
v_currPos_588_ = lean_ctor_get(v_a_578_, 0);
v_searcher_589_ = lean_ctor_get(v_a_578_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_a_578_);
if (v_isSharedCheck_612_ == 0)
{
v___x_591_ = v_a_578_;
v_isShared_592_ = v_isSharedCheck_612_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_searcher_589_);
lean_inc(v_currPos_588_);
lean_dec(v_a_578_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_612_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
uint8_t v_decide_593_; 
v_decide_593_ = lean_nat_dec_eq(v_searcher_589_, v___x_577_);
if (v_decide_593_ == 0)
{
uint32_t v___x_594_; uint32_t v___x_595_; uint8_t v___x_596_; 
v___x_594_ = 61;
v___x_595_ = lean_string_utf8_get_fast(v_param_575_, v_searcher_589_);
v___x_596_ = lean_uint32_dec_eq(v___x_595_, v___x_594_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = lean_string_utf8_next_fast(v_param_575_, v_searcher_589_);
lean_dec(v_searcher_589_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_597_);
v___x_599_ = v___x_591_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_currPos_588_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v___x_597_);
v___x_599_ = v_reuseFailAlloc_601_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
v_a_578_ = v___x_599_;
goto _start;
}
}
else
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_slice_605_; lean_object* v_nextIt_607_; 
v___x_602_ = lean_string_utf8_next_fast(v_param_575_, v_searcher_589_);
v___x_603_ = lean_nat_sub(v___x_602_, v_searcher_589_);
v___x_604_ = lean_nat_add(v_searcher_589_, v___x_603_);
lean_dec(v___x_603_);
v_slice_605_ = l_String_Slice_subslice_x21(v___x_576_, v_currPos_588_, v_searcher_589_);
lean_inc(v___x_604_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_604_);
lean_ctor_set(v___x_591_, 0, v___x_604_);
v_nextIt_607_ = v___x_591_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v___x_604_);
v_nextIt_607_ = v_reuseFailAlloc_610_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
lean_object* v_startInclusive_608_; lean_object* v_endExclusive_609_; 
v_startInclusive_608_ = lean_ctor_get(v_slice_605_, 0);
lean_inc(v_startInclusive_608_);
v_endExclusive_609_ = lean_ctor_get(v_slice_605_, 1);
lean_inc(v_endExclusive_609_);
lean_dec_ref(v_slice_605_);
v_it_581_ = v_nextIt_607_;
v_startInclusive_582_ = v_startInclusive_608_;
v_endExclusive_583_ = v_endExclusive_609_;
goto v___jp_580_;
}
}
}
else
{
lean_object* v___x_611_; 
lean_del_object(v___x_591_);
lean_dec(v_searcher_589_);
v___x_611_ = lean_box(1);
lean_inc(v___x_577_);
v_it_581_ = v___x_611_;
v_startInclusive_582_ = v_currPos_588_;
v_endExclusive_583_ = v___x_577_;
goto v___jp_580_;
}
}
}
else
{
lean_dec(v___x_577_);
lean_dec_ref(v_param_575_);
return v_b_579_;
}
v___jp_580_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
lean_inc_ref(v_param_575_);
v___x_584_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_584_, 0, v_param_575_);
lean_ctor_set(v___x_584_, 1, v_startInclusive_582_);
lean_ctor_set(v___x_584_, 2, v_endExclusive_583_);
v___x_585_ = l_String_Slice_toString(v___x_584_);
lean_dec_ref_known(v___x_584_, 3);
v___x_586_ = lean_array_push(v_b_579_, v___x_585_);
v_a_578_ = v_it_581_;
v_b_579_ = v___x_586_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1___redArg___boxed(lean_object* v_param_613_, lean_object* v___x_614_, lean_object* v___x_615_, lean_object* v_a_616_, lean_object* v_b_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1___redArg(v_param_613_, v___x_614_, v___x_615_, v_a_616_, v_b_617_);
lean_dec_ref(v___x_614_);
return v_res_618_;
}
}
LEAN_EXPORT uint8_t l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter(lean_object* v_param_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_string_utf8_byte_size(v_param_620_);
lean_inc_ref(v_param_620_);
v___x_623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_623_, 0, v_param_620_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
lean_ctor_set(v___x_623_, 2, v___x_622_);
v___x_624_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__0___closed__0);
v___x_625_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0));
v___x_626_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1___redArg(v_param_620_, v___x_623_, v___x_622_, v___x_624_, v___x_625_);
lean_dec_ref_known(v___x_623_, 3);
v___x_627_ = lean_array_to_list(v___x_626_);
if (lean_obj_tag(v___x_627_) == 1)
{
lean_object* v_tail_628_; 
v_tail_628_ = lean_ctor_get(v___x_627_, 1);
lean_inc(v_tail_628_);
if (lean_obj_tag(v_tail_628_) == 1)
{
lean_object* v_head_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_head_629_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_head_629_);
lean_dec_ref_known(v___x_627_, 2);
v___x_630_ = lean_string_utf8_byte_size(v_head_629_);
v___x_631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_631_, 0, v_head_629_);
lean_ctor_set(v___x_631_, 1, v___x_621_);
lean_ctor_set(v___x_631_, 2, v___x_630_);
v___x_632_ = l_String_Slice_trimAscii(v___x_631_);
v___x_633_ = l_String_Slice_toString(v___x_632_);
lean_dec_ref(v___x_632_);
v___x_634_ = l_Std_Http_Internal_isToken(v___x_633_);
if (v___x_634_ == 0)
{
lean_dec_ref_known(v_tail_628_, 2);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v_value_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_635_ = ((lean_object*)(l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter___closed__0));
v___x_636_ = l_String_intercalate(v___x_635_, v_tail_628_);
v___x_637_ = lean_string_utf8_byte_size(v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_621_);
lean_ctor_set(v___x_638_, 2, v___x_637_);
v___x_639_ = l_String_Slice_trimAscii(v___x_638_);
v_value_640_ = l_String_Slice_toString(v___x_639_);
lean_dec_ref(v___x_639_);
v___x_641_ = lean_string_utf8_byte_size(v_value_640_);
v___x_642_ = lean_nat_dec_eq(v___x_641_, v___x_621_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_Http_Internal_unquoteHttpString_x3f(v_value_640_);
if (lean_obj_tag(v___x_643_) == 0)
{
return v___x_642_;
}
else
{
lean_dec_ref_known(v___x_643_, 1);
return v___x_634_;
}
}
else
{
uint8_t v___x_644_; 
lean_dec_ref(v_value_640_);
v___x_644_ = 0;
return v___x_644_;
}
}
}
else
{
uint8_t v___x_645_; 
lean_dec(v_tail_628_);
lean_dec_ref_known(v___x_627_, 2);
v___x_645_ = 0;
return v___x_645_;
}
}
else
{
uint8_t v___x_646_; 
lean_dec(v___x_627_);
v___x_646_ = 0;
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter___boxed(lean_object* v_param_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter(v_param_647_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1(lean_object* v_param_650_, lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v_inst_653_, lean_object* v_R_654_, lean_object* v_a_655_, lean_object* v_b_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1___redArg(v_param_650_, v___x_651_, v___x_652_, v_a_655_, v_b_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1___boxed(lean_object* v_param_658_, lean_object* v___x_659_, lean_object* v___x_660_, lean_object* v_inst_661_, lean_object* v_R_662_, lean_object* v_a_663_, lean_object* v_b_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter_spec__1(v_param_658_, v___x_659_, v___x_660_, v_inst_661_, v_R_662_, v_a_663_, v_b_664_);
lean_dec_ref(v___x_659_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___redArg(){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___redArg___closed__0));
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___redArg___boxed(lean_object* v___dummy_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___redArg();
return v_res_669_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___redArg();
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0(lean_object* v_s_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___closed__0);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___boxed(lean_object* v_s_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0(v_s_673_);
lean_dec_ref(v_s_673_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1___redArg(lean_object* v_element_675_, lean_object* v___x_676_, lean_object* v___x_677_, lean_object* v_a_678_, lean_object* v_b_679_){
_start:
{
lean_object* v_it_681_; lean_object* v_startInclusive_682_; lean_object* v_endExclusive_683_; 
if (lean_obj_tag(v_a_678_) == 0)
{
lean_object* v_currPos_688_; lean_object* v_searcher_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_712_; 
v_currPos_688_ = lean_ctor_get(v_a_678_, 0);
v_searcher_689_ = lean_ctor_get(v_a_678_, 1);
v_isSharedCheck_712_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_712_ == 0)
{
v___x_691_ = v_a_678_;
v_isShared_692_ = v_isSharedCheck_712_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_searcher_689_);
lean_inc(v_currPos_688_);
lean_dec(v_a_678_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_712_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
uint8_t v_decide_693_; 
v_decide_693_ = lean_nat_dec_eq(v_searcher_689_, v___x_677_);
if (v_decide_693_ == 0)
{
uint32_t v___x_694_; uint32_t v___x_695_; uint8_t v___x_696_; 
v___x_694_ = 59;
v___x_695_ = lean_string_utf8_get_fast(v_element_675_, v_searcher_689_);
v___x_696_ = lean_uint32_dec_eq(v___x_695_, v___x_694_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_string_utf8_next_fast(v_element_675_, v_searcher_689_);
lean_dec(v_searcher_689_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_697_);
v___x_699_ = v___x_691_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_currPos_688_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v_a_678_ = v___x_699_;
goto _start;
}
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_slice_705_; lean_object* v_nextIt_707_; 
v___x_702_ = lean_string_utf8_next_fast(v_element_675_, v_searcher_689_);
v___x_703_ = lean_nat_sub(v___x_702_, v_searcher_689_);
v___x_704_ = lean_nat_add(v_searcher_689_, v___x_703_);
lean_dec(v___x_703_);
v_slice_705_ = l_String_Slice_subslice_x21(v___x_676_, v_currPos_688_, v_searcher_689_);
lean_inc(v___x_704_);
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___x_704_);
lean_ctor_set(v___x_691_, 0, v___x_704_);
v_nextIt_707_ = v___x_691_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v___x_704_);
v_nextIt_707_ = v_reuseFailAlloc_710_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v_startInclusive_708_; lean_object* v_endExclusive_709_; 
v_startInclusive_708_ = lean_ctor_get(v_slice_705_, 0);
lean_inc(v_startInclusive_708_);
v_endExclusive_709_ = lean_ctor_get(v_slice_705_, 1);
lean_inc(v_endExclusive_709_);
lean_dec_ref(v_slice_705_);
v_it_681_ = v_nextIt_707_;
v_startInclusive_682_ = v_startInclusive_708_;
v_endExclusive_683_ = v_endExclusive_709_;
goto v___jp_680_;
}
}
}
else
{
lean_object* v___x_711_; 
lean_del_object(v___x_691_);
lean_dec(v_searcher_689_);
v___x_711_ = lean_box(1);
lean_inc(v___x_677_);
v_it_681_ = v___x_711_;
v_startInclusive_682_ = v_currPos_688_;
v_endExclusive_683_ = v___x_677_;
goto v___jp_680_;
}
}
}
else
{
lean_dec(v___x_677_);
lean_dec_ref(v_element_675_);
return v_b_679_;
}
v___jp_680_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
lean_inc_ref(v_element_675_);
v___x_684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_684_, 0, v_element_675_);
lean_ctor_set(v___x_684_, 1, v_startInclusive_682_);
lean_ctor_set(v___x_684_, 2, v_endExclusive_683_);
v___x_685_ = l_String_Slice_toString(v___x_684_);
lean_dec_ref_known(v___x_684_, 3);
v___x_686_ = lean_array_push(v_b_679_, v___x_685_);
v_a_678_ = v_it_681_;
v_b_679_ = v___x_686_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1___redArg___boxed(lean_object* v_element_713_, lean_object* v___x_714_, lean_object* v___x_715_, lean_object* v_a_716_, lean_object* v_b_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1___redArg(v_element_713_, v___x_714_, v___x_715_, v_a_716_, v_b_717_);
lean_dec_ref(v___x_714_);
return v_res_718_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__2(lean_object* v_x_719_){
_start:
{
if (lean_obj_tag(v_x_719_) == 0)
{
uint8_t v___x_720_; 
v___x_720_ = 1;
return v___x_720_;
}
else
{
lean_object* v_head_721_; lean_object* v_tail_722_; uint8_t v___x_723_; 
v_head_721_ = lean_ctor_get(v_x_719_, 0);
lean_inc(v_head_721_);
v_tail_722_ = lean_ctor_get(v_x_719_, 1);
lean_inc(v_tail_722_);
lean_dec_ref_known(v_x_719_, 2);
v___x_723_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_TransferEncoding_isTransferParameter(v_head_721_);
if (v___x_723_ == 0)
{
lean_dec(v_tail_722_);
return v___x_723_;
}
else
{
v_x_719_ = v_tail_722_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__2___boxed(lean_object* v_x_725_){
_start:
{
uint8_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l_List_all___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__2(v_x_725_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3_spec__3(lean_object* v_as_728_, size_t v_i_729_, size_t v_stop_730_, lean_object* v_b_731_){
_start:
{
lean_object* v_val_733_; lean_object* v_val_738_; uint8_t v___x_740_; 
v___x_740_ = lean_usize_dec_eq(v_i_729_, v_stop_730_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_startInclusive_746_; lean_object* v_endExclusive_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_775_; 
v___x_741_ = lean_array_uget_borrowed(v_as_728_, v_i_729_);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_string_utf8_byte_size(v___x_741_);
lean_inc(v___x_741_);
v___x_744_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_744_, 0, v___x_741_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
lean_ctor_set(v___x_744_, 2, v___x_743_);
lean_inc_ref(v___x_744_);
v___x_745_ = l_String_Slice_trimAscii(v___x_744_);
v_startInclusive_746_ = lean_ctor_get(v___x_745_, 1);
v_endExclusive_747_ = lean_ctor_get(v___x_745_, 2);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_775_ == 0)
{
lean_object* v_unused_776_; 
v_unused_776_ = lean_ctor_get(v___x_745_, 0);
lean_dec(v_unused_776_);
v___x_749_ = v___x_745_;
v_isShared_750_ = v_isSharedCheck_775_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_endExclusive_747_);
lean_inc(v_startInclusive_746_);
lean_dec(v___x_745_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_775_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = lean_nat_sub(v_endExclusive_747_, v_startInclusive_746_);
lean_dec(v_startInclusive_746_);
lean_dec(v_endExclusive_747_);
v___x_752_ = lean_nat_dec_eq(v___x_751_, v___x_742_);
lean_dec(v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_753_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__0___closed__0);
v___x_754_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0));
lean_inc(v___x_741_);
v___x_755_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1___redArg(v___x_741_, v___x_744_, v___x_743_, v___x_753_, v___x_754_);
lean_dec_ref_known(v___x_744_, 3);
v___x_756_ = lean_array_to_list(v___x_755_);
if (lean_obj_tag(v___x_756_) == 1)
{
lean_object* v_head_757_; lean_object* v_tail_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v_head_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_head_757_);
v_tail_758_ = lean_ctor_get(v___x_756_, 1);
lean_inc(v_tail_758_);
lean_dec_ref_known(v___x_756_, 2);
v___x_759_ = lean_string_utf8_byte_size(v_head_757_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 2, v___x_759_);
lean_ctor_set(v___x_749_, 1, v___x_742_);
lean_ctor_set(v___x_749_, 0, v_head_757_);
v___x_761_ = v___x_749_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_head_757_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v___x_759_);
v___x_761_ = v_reuseFailAlloc_773_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v_name_764_; uint8_t v___x_765_; 
v___x_762_ = l_String_Slice_trimAscii(v___x_761_);
v___x_763_ = l_String_Slice_toString(v___x_762_);
lean_dec_ref(v___x_762_);
v_name_764_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_763_, v___x_742_);
lean_inc_ref(v_name_764_);
v___x_765_ = l_Std_Http_Internal_isToken(v_name_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
lean_dec_ref(v_name_764_);
lean_dec(v_tail_758_);
lean_dec_ref(v_b_731_);
v___x_766_ = lean_box(0);
return v___x_766_;
}
else
{
uint8_t v___x_767_; 
lean_inc(v_tail_758_);
v___x_767_ = l_List_all___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__2(v_tail_758_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_dec_ref(v_name_764_);
lean_dec(v_tail_758_);
lean_dec_ref(v_b_731_);
v___x_768_ = lean_box(0);
return v___x_768_;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = l_List_isEmpty___redArg(v_tail_758_);
lean_dec(v_tail_758_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_771_ = lean_string_dec_eq(v_name_764_, v___x_770_);
if (v___x_771_ == 0)
{
v_val_738_ = v_name_764_;
goto v___jp_737_;
}
else
{
lean_object* v___x_772_; 
lean_dec_ref(v_name_764_);
lean_dec_ref(v_b_731_);
v___x_772_ = lean_box(0);
return v___x_772_;
}
}
else
{
v_val_738_ = v_name_764_;
goto v___jp_737_;
}
}
}
}
}
else
{
lean_object* v___x_774_; 
lean_dec(v___x_756_);
lean_del_object(v___x_749_);
lean_dec_ref(v_b_731_);
v___x_774_ = lean_box(0);
return v___x_774_;
}
}
else
{
lean_del_object(v___x_749_);
lean_dec_ref_known(v___x_744_, 3);
v_val_733_ = v_b_731_;
goto v___jp_732_;
}
}
}
else
{
lean_object* v___x_777_; 
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v_b_731_);
return v___x_777_;
}
v___jp_732_:
{
size_t v___x_734_; size_t v___x_735_; 
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_729_, v___x_734_);
v_i_729_ = v___x_735_;
v_b_731_ = v_val_733_;
goto _start;
}
v___jp_737_:
{
lean_object* v___x_739_; 
v___x_739_ = lean_array_push(v_b_731_, v_val_738_);
v_val_733_ = v___x_739_;
goto v___jp_732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3_spec__3___boxed(lean_object* v_as_778_, lean_object* v_i_779_, lean_object* v_stop_780_, lean_object* v_b_781_){
_start:
{
size_t v_i_boxed_782_; size_t v_stop_boxed_783_; lean_object* v_res_784_; 
v_i_boxed_782_ = lean_unbox_usize(v_i_779_);
lean_dec(v_i_779_);
v_stop_boxed_783_ = lean_unbox_usize(v_stop_780_);
lean_dec(v_stop_780_);
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3_spec__3(v_as_778_, v_i_boxed_782_, v_stop_boxed_783_, v_b_781_);
lean_dec_ref(v_as_778_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3(lean_object* v_as_787_, lean_object* v_start_788_, lean_object* v_stop_789_){
_start:
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0));
v___x_791_ = lean_nat_dec_lt(v_start_788_, v_stop_789_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; 
v___x_792_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3___closed__0));
return v___x_792_;
}
else
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_array_get_size(v_as_787_);
v___x_794_ = lean_nat_dec_le(v_stop_789_, v___x_793_);
if (v___x_794_ == 0)
{
uint8_t v___x_795_; 
v___x_795_ = lean_nat_dec_lt(v_start_788_, v___x_793_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; 
v___x_796_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3___closed__0));
return v___x_796_;
}
else
{
size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_usize_of_nat(v_start_788_);
v___x_798_ = lean_usize_of_nat(v___x_793_);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3_spec__3(v_as_787_, v___x_797_, v___x_798_, v___x_790_);
return v___x_799_;
}
}
else
{
size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
v___x_800_ = lean_usize_of_nat(v_start_788_);
v___x_801_ = lean_usize_of_nat(v_stop_789_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3_spec__3(v_as_787_, v___x_800_, v___x_801_, v___x_790_);
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3___boxed(lean_object* v_as_803_, lean_object* v_start_804_, lean_object* v_stop_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3(v_as_803_, v_start_804_, v_stop_805_);
lean_dec(v_stop_805_);
lean_dec(v_start_804_);
lean_dec_ref(v_as_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parseCodings_x3f(lean_object* v_v_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = lean_string_utf8_byte_size(v_v_807_);
lean_inc_ref(v_v_807_);
v___x_810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_810_, 0, v_v_807_);
lean_ctor_set(v___x_810_, 1, v___x_808_);
lean_ctor_set(v___x_810_, 2, v___x_809_);
v___x_811_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__1___closed__0);
v___x_812_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0));
v___x_813_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__2___redArg(v_v_807_, v___x_810_, v___x_809_, v___x_811_, v___x_812_);
lean_dec_ref_known(v___x_810_, 3);
v___x_814_ = lean_array_to_list(v___x_813_);
v___x_815_ = lean_array_mk(v___x_814_);
v___x_816_ = lean_array_get_size(v___x_815_);
v___x_817_ = l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3(v___x_815_, v___x_808_, v___x_816_);
lean_dec_ref(v___x_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1(lean_object* v_element_818_, lean_object* v___x_819_, lean_object* v___x_820_, lean_object* v_inst_821_, lean_object* v_R_822_, lean_object* v_a_823_, lean_object* v_b_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1___redArg(v_element_818_, v___x_819_, v___x_820_, v_a_823_, v_b_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1___boxed(lean_object* v_element_826_, lean_object* v___x_827_, lean_object* v___x_828_, lean_object* v_inst_829_, lean_object* v_R_830_, lean_object* v_a_831_, lean_object* v_b_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__1(v_element_826_, v___x_827_, v___x_828_, v_inst_829_, v_R_830_, v_a_831_, v_b_832_);
lean_dec_ref(v___x_827_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_parseFieldLines_x3f_spec__0(lean_object* v_as_834_, size_t v_i_835_, size_t v_stop_836_, lean_object* v_b_837_){
_start:
{
uint8_t v___x_838_; 
v___x_838_ = lean_usize_dec_eq(v_i_835_, v_stop_836_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = lean_array_uget_borrowed(v_as_834_, v_i_835_);
lean_inc(v___x_839_);
v___x_840_ = l_Std_Http_Header_TransferEncoding_parseCodings_x3f(v___x_839_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_dec_ref(v_b_837_);
return v___x_840_;
}
else
{
lean_object* v_val_841_; lean_object* v___x_842_; size_t v___x_843_; size_t v___x_844_; 
v_val_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v___x_840_, 1);
v___x_842_ = l_Array_append___redArg(v_b_837_, v_val_841_);
lean_dec(v_val_841_);
v___x_843_ = ((size_t)1ULL);
v___x_844_ = lean_usize_add(v_i_835_, v___x_843_);
v_i_835_ = v___x_844_;
v_b_837_ = v___x_842_;
goto _start;
}
}
else
{
lean_object* v___x_846_; 
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v_b_837_);
return v___x_846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_parseFieldLines_x3f_spec__0___boxed(lean_object* v_as_847_, lean_object* v_i_848_, lean_object* v_stop_849_, lean_object* v_b_850_){
_start:
{
size_t v_i_boxed_851_; size_t v_stop_boxed_852_; lean_object* v_res_853_; 
v_i_boxed_851_ = lean_unbox_usize(v_i_848_);
lean_dec(v_i_848_);
v_stop_boxed_852_ = lean_unbox_usize(v_stop_849_);
lean_dec(v_stop_849_);
v_res_853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_parseFieldLines_x3f_spec__0(v_as_847_, v_i_boxed_851_, v_stop_boxed_852_, v_b_850_);
lean_dec_ref(v_as_847_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parseFieldLines_x3f(lean_object* v_values_854_){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__3___closed__0));
v___x_857_ = lean_array_get_size(v_values_854_);
v___x_858_ = lean_nat_dec_lt(v___x_855_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; 
v___x_859_ = ((lean_object*)(l_Array_filterMapM___at___00Std_Http_Header_TransferEncoding_parseCodings_x3f_spec__3___closed__0));
return v___x_859_;
}
else
{
size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; 
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_of_nat(v___x_857_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_parseFieldLines_x3f_spec__0(v_values_854_, v___x_860_, v___x_861_, v___x_856_);
return v___x_862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parseFieldLines_x3f___boxed(lean_object* v_values_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Std_Http_Header_TransferEncoding_parseFieldLines_x3f(v_values_863_);
lean_dec_ref(v_values_863_);
return v_res_864_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_parse(lean_object* v_v_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Std_Http_Header_TransferEncoding_parseCodings_x3f(v_v_865_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v___x_867_; 
v___x_867_ = lean_box(0);
return v___x_867_;
}
else
{
lean_object* v_val_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_877_; 
v_val_868_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_877_ == 0)
{
v___x_870_ = v___x_866_;
v_isShared_871_ = v_isSharedCheck_877_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_val_868_);
lean_dec(v___x_866_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_877_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
uint8_t v___x_872_; 
v___x_872_ = l_Std_Http_Header_TransferEncoding_Validate(v_val_868_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
lean_del_object(v___x_870_);
lean_dec(v_val_868_);
v___x_873_ = lean_box(0);
return v___x_873_;
}
else
{
lean_object* v___x_875_; 
if (v_isShared_871_ == 0)
{
v___x_875_ = v___x_870_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_val_868_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f_spec__0(lean_object* v_as_878_, size_t v_i_879_, size_t v_stop_880_, lean_object* v_b_881_){
_start:
{
uint8_t v___x_882_; 
v___x_882_ = lean_usize_dec_eq(v_i_879_, v_stop_880_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v___x_883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_Validate_spec__1___closed__0));
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_sub(v_i_879_, v___x_884_);
v___x_886_ = lean_array_uget_borrowed(v_as_878_, v___x_885_);
v___x_887_ = lean_string_dec_eq(v___x_886_, v___x_883_);
if (v___x_887_ == 0)
{
v_i_879_ = v___x_885_;
goto _start;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_unsigned_to_nat(1u);
v___x_890_ = lean_nat_add(v_b_881_, v___x_889_);
lean_dec(v_b_881_);
v_i_879_ = v___x_885_;
v_b_881_ = v___x_890_;
goto _start;
}
}
else
{
return v_b_881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f_spec__0___boxed(lean_object* v_as_892_, lean_object* v_i_893_, lean_object* v_stop_894_, lean_object* v_b_895_){
_start:
{
size_t v_i_boxed_896_; size_t v_stop_boxed_897_; lean_object* v_res_898_; 
v_i_boxed_896_ = lean_unbox_usize(v_i_893_);
lean_dec(v_i_893_);
v_stop_boxed_897_ = lean_unbox_usize(v_stop_894_);
lean_dec(v_stop_894_);
v_res_898_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f_spec__0(v_as_892_, v_i_boxed_896_, v_stop_boxed_897_, v_b_895_);
lean_dec_ref(v_as_892_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f(lean_object* v_values_899_){
_start:
{
uint8_t v___y_901_; lean_object* v___y_902_; lean_object* v___x_908_; 
v___x_908_ = l_Std_Http_Header_TransferEncoding_parseFieldLines_x3f(v_values_899_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_box(0);
return v___x_909_;
}
else
{
lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_935_; 
v_val_910_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_935_ == 0)
{
v___x_912_ = v___x_908_;
v_isShared_913_ = v_isSharedCheck_935_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_dec(v___x_908_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_935_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___y_915_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_928_ = lean_array_get_size(v_val_910_);
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_sub(v___x_928_, v___x_929_);
v___x_931_ = lean_nat_dec_lt(v___x_930_, v___x_928_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; 
lean_dec(v___x_930_);
v___x_932_ = lean_box(0);
v___y_915_ = v___x_932_;
goto v___jp_914_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_array_fget_borrowed(v_val_910_, v___x_930_);
lean_dec(v___x_930_);
lean_inc(v___x_933_);
v___x_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
v___y_915_ = v___x_934_;
goto v___jp_914_;
}
v___jp_914_:
{
lean_object* v___x_916_; uint8_t v___x_917_; 
v___x_916_ = ((lean_object*)(l_Std_Http_Header_TransferEncoding_Validate___closed__0));
v___x_917_ = l_instBEqOption_beq___at___00Std_Http_Header_TransferEncoding_Validate_spec__0(v___y_915_, v___x_916_);
lean_dec(v___y_915_);
if (v___x_917_ == 0)
{
lean_object* v___x_918_; lean_object* v___x_920_; 
lean_dec(v_val_910_);
v___x_918_ = lean_box(v___x_917_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_918_);
v___x_920_ = v___x_912_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
lean_del_object(v___x_912_);
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = lean_array_get_size(v_val_910_);
v___x_924_ = lean_nat_dec_lt(v___x_922_, v___x_923_);
if (v___x_924_ == 0)
{
lean_dec(v_val_910_);
v___y_901_ = v___x_917_;
v___y_902_ = v___x_922_;
goto v___jp_900_;
}
else
{
size_t v___x_925_; size_t v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_usize_of_nat(v___x_923_);
v___x_926_ = ((size_t)0ULL);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f_spec__0(v_val_910_, v___x_925_, v___x_926_, v___x_922_);
lean_dec(v_val_910_);
v___y_901_ = v___x_917_;
v___y_902_ = v___x_927_;
goto v___jp_900_;
}
}
}
}
}
v___jp_900_:
{
lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_dec_eq(v___y_902_, v___x_903_);
lean_dec(v___y_902_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
v___x_905_ = lean_box(0);
return v___x_905_;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_box(v___y_901_);
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f___boxed(lean_object* v_values_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_Http_Header_TransferEncoding_finalCodingIsChunked_x3f(v_values_936_);
lean_dec_ref(v_values_936_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_TransferEncoding_serialize(lean_object* v_te_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_value_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_939_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_940_ = lean_array_to_list(v_te_938_);
v_value_941_ = l_String_intercalate(v___x_939_, v___x_940_);
v___x_942_ = l_Std_Http_Header_Name_transferEncoding;
v___x_943_ = l_Std_Http_Header_Value_ofString_x21(v_value_941_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___redArg(lean_object* v_x_963_){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_964_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_965_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__3));
v___x_966_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__7);
v___x_967_ = l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0(v_x_963_);
v___x_968_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = 0;
v___x_970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_970_, 0, v___x_968_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*1, v___x_969_);
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_965_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_box(1);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = ((lean_object*)(l_Std_Http_Header_instReprConnection_repr___redArg___closed__5));
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_964_);
v___x_979_ = ((lean_object*)(l_Std_Http_Header_instReprTransferEncoding_repr___redArg___closed__8));
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_982_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_980_);
v___x_984_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_981_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set_uint8(v___x_987_, sizeof(void*)*1, v___x_969_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr(lean_object* v_x_988_, lean_object* v_prec_989_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_Http_Header_instReprConnection_repr___redArg(v_x_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprConnection_repr___boxed(lean_object* v_x_991_, lean_object* v_prec_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_Http_Header_instReprConnection_repr(v_x_991_, v_prec_992_);
lean_dec(v_prec_992_);
return v_res_993_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(lean_object* v_token_996_, lean_object* v_as_997_, size_t v_i_998_, size_t v_stop_999_){
_start:
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_usize_dec_eq(v_i_998_, v_stop_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1001_ = lean_array_uget_borrowed(v_as_997_, v_i_998_);
v___x_1002_ = lean_string_dec_eq(v___x_1001_, v_token_996_);
if (v___x_1002_ == 0)
{
size_t v___x_1003_; size_t v___x_1004_; 
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_998_, v___x_1003_);
v_i_998_ = v___x_1004_;
goto _start;
}
else
{
return v___x_1002_;
}
}
else
{
uint8_t v___x_1006_; 
v___x_1006_ = 0;
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0___boxed(lean_object* v_token_1007_, lean_object* v_as_1008_, lean_object* v_i_1009_, lean_object* v_stop_1010_){
_start:
{
size_t v_i_boxed_1011_; size_t v_stop_boxed_1012_; uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_i_boxed_1011_ = lean_unbox_usize(v_i_1009_);
lean_dec(v_i_1009_);
v_stop_boxed_1012_ = lean_unbox_usize(v_stop_1010_);
lean_dec(v_stop_1010_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_1007_, v_as_1008_, v_i_boxed_1011_, v_stop_boxed_1012_);
lean_dec_ref(v_as_1008_);
lean_dec_ref(v_token_1007_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_containsToken(lean_object* v_connection_1015_, lean_object* v_token_1016_){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lean_array_get_size(v_connection_1015_);
v___x_1019_ = lean_nat_dec_lt(v___x_1017_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_dec_ref(v_token_1016_);
return v___x_1019_;
}
else
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_string_utf8_byte_size(v_token_1016_);
if (v___x_1019_ == 0)
{
lean_dec_ref(v_token_1016_);
return v___x_1019_;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v_token_1024_; size_t v___x_1025_; size_t v___x_1026_; uint8_t v___x_1027_; 
v___x_1021_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1021_, 0, v_token_1016_);
lean_ctor_set(v___x_1021_, 1, v___x_1017_);
lean_ctor_set(v___x_1021_, 2, v___x_1020_);
v___x_1022_ = l_String_Slice_trimAscii(v___x_1021_);
v___x_1023_ = l_String_Slice_toString(v___x_1022_);
lean_dec_ref(v___x_1022_);
v_token_1024_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_1023_, v___x_1017_);
v___x_1025_ = ((size_t)0ULL);
v___x_1026_ = lean_usize_of_nat(v___x_1018_);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_containsToken_spec__0(v_token_1024_, v_connection_1015_, v___x_1025_, v___x_1026_);
lean_dec_ref(v_token_1024_);
return v___x_1027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_containsToken___boxed(lean_object* v_connection_1028_, lean_object* v_token_1029_){
_start:
{
uint8_t v_res_1030_; lean_object* v_r_1031_; 
v_res_1030_ = l_Std_Http_Header_Connection_containsToken(v_connection_1028_, v_token_1029_);
lean_dec_ref(v_connection_1028_);
v_r_1031_ = lean_box(v_res_1030_);
return v_r_1031_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_Connection_shouldClose(lean_object* v_connection_1033_){
_start:
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Std_Http_Header_Connection_shouldClose___closed__0));
v___x_1035_ = l_Std_Http_Header_Connection_containsToken(v_connection_1033_, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_shouldClose___boxed(lean_object* v_connection_1036_){
_start:
{
uint8_t v_res_1037_; lean_object* v_r_1038_; 
v_res_1037_ = l_Std_Http_Header_Connection_shouldClose(v_connection_1036_);
lean_dec_ref(v_connection_1036_);
v_r_1038_ = lean_box(v_res_1037_);
return v_r_1038_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(lean_object* v_as_1039_, size_t v_i_1040_, size_t v_stop_1041_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_usize_dec_eq(v_i_1040_, v_stop_1041_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = lean_array_uget_borrowed(v_as_1039_, v_i_1040_);
lean_inc(v___x_1043_);
v___x_1044_ = l_Std_Http_Internal_isToken(v___x_1043_);
if (v___x_1044_ == 0)
{
uint8_t v___x_1045_; 
v___x_1045_ = 1;
return v___x_1045_;
}
else
{
size_t v___x_1046_; size_t v___x_1047_; 
v___x_1046_ = ((size_t)1ULL);
v___x_1047_ = lean_usize_add(v_i_1040_, v___x_1046_);
v_i_1040_ = v___x_1047_;
goto _start;
}
}
else
{
uint8_t v___x_1049_; 
v___x_1049_ = 0;
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0___boxed(lean_object* v_as_1050_, lean_object* v_i_1051_, lean_object* v_stop_1052_){
_start:
{
size_t v_i_boxed_1053_; size_t v_stop_boxed_1054_; uint8_t v_res_1055_; lean_object* v_r_1056_; 
v_i_boxed_1053_ = lean_unbox_usize(v_i_1051_);
lean_dec(v_i_1051_);
v_stop_boxed_1054_ = lean_unbox_usize(v_stop_1052_);
lean_dec(v_stop_1052_);
v_res_1055_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_as_1050_, v_i_boxed_1053_, v_stop_boxed_1054_);
lean_dec_ref(v_as_1050_);
v_r_1056_ = lean_box(v_res_1055_);
return v_r_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_parse(lean_object* v_v_1057_){
_start:
{
lean_object* v___x_1058_; lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1079_; 
v___x_1058_ = l___private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList(v_v_1057_);
v_val_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1079_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1079_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1063_ = lean_unsigned_to_nat(0u);
v___x_1064_ = lean_array_get_size(v_val_1059_);
v___x_1065_ = lean_nat_dec_lt(v___x_1063_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1067_; 
if (v_isShared_1062_ == 0)
{
v___x_1067_ = v___x_1061_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_val_1059_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
else
{
if (v___x_1065_ == 0)
{
lean_object* v___x_1070_; 
if (v_isShared_1062_ == 0)
{
v___x_1070_ = v___x_1061_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_val_1059_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
else
{
size_t v___x_1072_; size_t v___x_1073_; uint8_t v___x_1074_; 
v___x_1072_ = ((size_t)0ULL);
v___x_1073_ = lean_usize_of_nat(v___x_1064_);
v___x_1074_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Std_Http_Header_Connection_parse_spec__0(v_val_1059_, v___x_1072_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1076_; 
if (v_isShared_1062_ == 0)
{
v___x_1076_ = v___x_1061_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_val_1059_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
else
{
lean_object* v___x_1078_; 
lean_del_object(v___x_1061_);
lean_dec(v_val_1059_);
v___x_1078_ = lean_box(0);
return v___x_1078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Connection_serialize(lean_object* v_connection_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v_value_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1081_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__1));
v___x_1082_ = lean_array_to_list(v_connection_1080_);
v_value_1083_ = l_String_intercalate(v___x_1081_, v___x_1082_);
v___x_1084_ = l_Std_Http_Header_Name_connection;
v___x_1085_ = l_Std_Http_Header_Value_ofString_x21(v_value_1083_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_unsigned_to_nat(8u);
v___x_1103_ = lean_nat_to_int(v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(2u);
v___x_1105_ = lean_nat_to_int(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___redArg(lean_object* v_x_1113_){
_start:
{
lean_object* v_host_1114_; lean_object* v_port_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1189_; 
v_host_1114_ = lean_ctor_get(v_x_1113_, 0);
v_port_1115_ = lean_ctor_get(v_x_1113_, 1);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_x_1113_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1117_ = v_x_1113_;
v_isShared_1118_ = v_isSharedCheck_1189_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_port_1115_);
lean_inc(v_host_1114_);
lean_dec(v_x_1113_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1189_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v_ctr_1125_; lean_object* v_a_1126_; 
v___x_1119_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__5));
v___x_1120_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__3));
v___x_1121_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__4, &l_Std_Http_Header_instReprHost_repr___redArg___closed__4_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__4);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_obj_once(&l_Std_Http_Header_instReprHost_repr___redArg___closed__5, &l_Std_Http_Header_instReprHost_repr___redArg___closed__5_once, _init_l_Std_Http_Header_instReprHost_repr___redArg___closed__5);
switch(lean_obj_tag(v_host_1114_))
{
case 0:
{
lean_object* v_name_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1168_; 
v_name_1159_ = lean_ctor_get(v_host_1114_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_host_1114_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1161_ = v_host_1114_;
v_isShared_1162_ = v_isSharedCheck_1168_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_name_1159_);
lean_dec(v_host_1114_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1168_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1163_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__9));
v___x_1164_ = l_String_quote(v_name_1159_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set_tag(v___x_1161_, 3);
lean_ctor_set(v___x_1161_, 0, v___x_1164_);
v___x_1166_ = v___x_1161_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
v_ctr_1125_ = v___x_1163_;
v_a_1126_ = v___x_1166_;
goto v___jp_1124_;
}
}
}
case 1:
{
lean_object* v_ipv4_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1178_; 
v_ipv4_1169_ = lean_ctor_get(v_host_1114_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_host_1114_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1171_ = v_host_1114_;
v_isShared_1172_ = v_isSharedCheck_1178_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_ipv4_1169_);
lean_dec(v_host_1114_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1178_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v___x_1173_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__10));
v___x_1174_ = lean_uv_ntop_v4(v_ipv4_1169_);
lean_dec_ref(v_ipv4_1169_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set_tag(v___x_1171_, 3);
lean_ctor_set(v___x_1171_, 0, v___x_1174_);
v___x_1176_ = v___x_1171_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
v_ctr_1125_ = v___x_1173_;
v_a_1126_ = v___x_1176_;
goto v___jp_1124_;
}
}
}
default: 
{
lean_object* v_ipv6_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1188_; 
v_ipv6_1179_ = lean_ctor_get(v_host_1114_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_host_1114_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1181_ = v_host_1114_;
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_ipv6_1179_);
lean_dec(v_host_1114_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1183_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__11));
v___x_1184_ = lean_uv_ntop_v6(v_ipv6_1179_);
lean_dec_ref(v_ipv6_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set_tag(v___x_1181_, 3);
lean_ctor_set(v___x_1181_, 0, v___x_1184_);
v___x_1186_ = v___x_1181_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
v_ctr_1125_ = v___x_1183_;
v_a_1126_ = v___x_1186_;
goto v___jp_1124_;
}
}
}
}
v___jp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1127_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__6));
v___x_1128_ = lean_string_append(v___x_1127_, v_ctr_1125_);
v___x_1129_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
v___x_1130_ = lean_box(1);
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 5);
lean_ctor_set(v___x_1117_, 1, v___x_1130_);
lean_ctor_set(v___x_1117_, 0, v___x_1129_);
v___x_1132_ = v___x_1117_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v_a_1126_);
v___x_1134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1123_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = 0;
v___x_1136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*1, v___x_1135_);
v___x_1137_ = l_Repr_addAppParen(v___x_1136_, v___x_1122_);
v___x_1138_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1121_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*1, v___x_1135_);
v___x_1140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1120_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v___x_1141_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__2));
v___x_1142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1140_);
lean_ctor_set(v___x_1142_, 1, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v___x_1130_);
v___x_1144_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__8));
v___x_1145_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1143_);
lean_ctor_set(v___x_1145_, 1, v___x_1144_);
v___x_1146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1145_);
lean_ctor_set(v___x_1146_, 1, v___x_1119_);
v___x_1147_ = l_Std_Http_URI_instReprPort_repr(v_port_1115_, v___x_1122_);
lean_dec(v_port_1115_);
v___x_1148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1121_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
lean_ctor_set_uint8(v___x_1149_, sizeof(void*)*1, v___x_1135_);
v___x_1150_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1146_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1152_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__11));
v___x_1153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v___x_1150_);
v___x_1154_ = ((lean_object*)(l_Std_Http_Header_instReprContentLength_repr___redArg___closed__12));
v___x_1155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1151_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v___x_1157_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*1, v___x_1135_);
return v___x_1157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr(lean_object* v_x_1190_, lean_object* v_prec_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Std_Http_Header_instReprHost_repr___redArg(v_x_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprHost_repr___boxed(lean_object* v_x_1193_, lean_object* v_prec_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Std_Http_Header_instReprHost_repr(v_x_1193_, v_prec_1194_);
lean_dec(v_prec_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqHost_beq(lean_object* v_x_1198_, lean_object* v_x_1199_){
_start:
{
lean_object* v_host_1200_; lean_object* v_port_1201_; lean_object* v_host_1202_; lean_object* v_port_1203_; uint8_t v___x_1204_; 
v_host_1200_ = lean_ctor_get(v_x_1198_, 0);
v_port_1201_ = lean_ctor_get(v_x_1198_, 1);
v_host_1202_ = lean_ctor_get(v_x_1199_, 0);
v_port_1203_ = lean_ctor_get(v_x_1199_, 1);
v___x_1204_ = l_Std_Http_URI_instBEqHost_beq(v_host_1200_, v_host_1202_);
if (v___x_1204_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = l_Std_Http_URI_instDecidableEqPort_decEq(v_port_1201_, v_port_1203_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqHost_beq___boxed(lean_object* v_x_1206_, lean_object* v_x_1207_){
_start:
{
uint8_t v_res_1208_; lean_object* v_r_1209_; 
v_res_1208_ = l_Std_Http_Header_instBEqHost_beq(v_x_1206_, v_x_1207_);
lean_dec_ref(v_x_1207_);
lean_dec_ref(v_x_1206_);
v_r_1209_ = lean_box(v_res_1208_);
return v_r_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse___lam__0(lean_object* v___x_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Std_Http_URI_Parser_parseHostHeader(v___x_1215_, v___y_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_pos_1218_; lean_object* v_array_1219_; lean_object* v_idx_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v_pos_1218_ = lean_ctor_get(v___x_1217_, 0);
v_array_1219_ = lean_ctor_get(v_pos_1218_, 0);
v_idx_1220_ = lean_ctor_get(v_pos_1218_, 1);
v___x_1221_ = lean_byte_array_size(v_array_1219_);
v___x_1222_ = lean_nat_dec_lt(v_idx_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
return v___x_1217_;
}
else
{
lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
lean_inc(v_pos_1218_);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; lean_object* v_unused_1232_; 
v_unused_1231_ = lean_ctor_get(v___x_1217_, 1);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1232_);
v___x_1224_ = v___x_1217_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_dec(v___x_1217_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = ((lean_object*)(l_Std_Http_Header_Host_parse___lam__0___closed__1));
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 1);
lean_ctor_set(v___x_1224_, 1, v___x_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_pos_1218_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
return v___x_1217_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_parse(lean_object* v_v_1240_){
_start:
{
lean_object* v___f_1241_; lean_object* v___x_1242_; lean_object* v_parsed_1243_; 
v___f_1241_ = ((lean_object*)(l_Std_Http_Header_Host_parse___closed__1));
v___x_1242_ = lean_string_to_utf8(v_v_1240_);
v_parsed_1243_ = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(v___f_1241_, v___x_1242_);
if (lean_obj_tag(v_parsed_1243_) == 0)
{
lean_object* v___x_1244_; 
lean_dec_ref_known(v_parsed_1243_, 1);
v___x_1244_ = lean_box(0);
return v___x_1244_;
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1261_; 
v_a_1245_ = lean_ctor_get(v_parsed_1243_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_parsed_1243_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1247_ = v_parsed_1243_;
v_isShared_1248_ = v_isSharedCheck_1261_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v_parsed_1243_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1261_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v_fst_1249_; lean_object* v_snd_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1260_; 
v_fst_1249_ = lean_ctor_get(v_a_1245_, 0);
v_snd_1250_ = lean_ctor_get(v_a_1245_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_a_1245_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1252_ = v_a_1245_;
v_isShared_1253_ = v_isSharedCheck_1260_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snd_1250_);
lean_inc(v_fst_1249_);
lean_dec(v_a_1245_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1260_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_fst_1249_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_snd_1250_);
v___x_1255_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1257_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1255_);
v___x_1257_ = v___x_1247_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Host_serialize(lean_object* v_host_1264_){
_start:
{
lean_object* v___y_1266_; lean_object* v___y_1270_; lean_object* v_port_1274_; 
v_port_1274_ = lean_ctor_get(v_host_1264_, 1);
switch(lean_obj_tag(v_port_1274_))
{
case 0:
{
lean_object* v_host_1275_; 
v_host_1275_ = lean_ctor_get(v_host_1264_, 0);
lean_inc_ref(v_host_1275_);
lean_dec_ref(v_host_1264_);
switch(lean_obj_tag(v_host_1275_))
{
case 0:
{
lean_object* v_name_1276_; lean_object* v___x_1277_; 
v_name_1276_ = lean_ctor_get(v_host_1275_, 0);
lean_inc_ref(v_name_1276_);
lean_dec_ref_known(v_host_1275_, 1);
v___x_1277_ = l_Std_Http_Header_Value_ofString_x21(v_name_1276_);
v___y_1266_ = v___x_1277_;
goto v___jp_1265_;
}
case 1:
{
lean_object* v_ipv4_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_ipv4_1278_ = lean_ctor_get(v_host_1275_, 0);
lean_inc_ref(v_ipv4_1278_);
lean_dec_ref_known(v_host_1275_, 1);
v___x_1279_ = lean_uv_ntop_v4(v_ipv4_1278_);
lean_dec_ref(v_ipv4_1278_);
v___x_1280_ = l_Std_Http_Header_Value_ofString_x21(v___x_1279_);
v___y_1266_ = v___x_1280_;
goto v___jp_1265_;
}
default: 
{
lean_object* v_ipv6_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v_ipv6_1281_ = lean_ctor_get(v_host_1275_, 0);
lean_inc_ref(v_ipv6_1281_);
lean_dec_ref_known(v_host_1275_, 1);
v___x_1282_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1283_ = lean_uv_ntop_v6(v_ipv6_1281_);
lean_dec_ref(v_ipv6_1281_);
v___x_1284_ = lean_string_append(v___x_1282_, v___x_1283_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1286_ = lean_string_append(v___x_1284_, v___x_1285_);
v___x_1287_ = l_Std_Http_Header_Value_ofString_x21(v___x_1286_);
v___y_1266_ = v___x_1287_;
goto v___jp_1265_;
}
}
}
case 1:
{
lean_object* v_host_1288_; 
v_host_1288_ = lean_ctor_get(v_host_1264_, 0);
lean_inc_ref(v_host_1288_);
lean_dec_ref(v_host_1264_);
switch(lean_obj_tag(v_host_1288_))
{
case 0:
{
lean_object* v_name_1289_; 
v_name_1289_ = lean_ctor_get(v_host_1288_, 0);
lean_inc_ref(v_name_1289_);
lean_dec_ref_known(v_host_1288_, 1);
v___y_1270_ = v_name_1289_;
goto v___jp_1269_;
}
case 1:
{
lean_object* v_ipv4_1290_; lean_object* v___x_1291_; 
v_ipv4_1290_ = lean_ctor_get(v_host_1288_, 0);
lean_inc_ref(v_ipv4_1290_);
lean_dec_ref_known(v_host_1288_, 1);
v___x_1291_ = lean_uv_ntop_v4(v_ipv4_1290_);
lean_dec_ref(v_ipv4_1290_);
v___y_1270_ = v___x_1291_;
goto v___jp_1269_;
}
default: 
{
lean_object* v_ipv6_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_ipv6_1292_ = lean_ctor_get(v_host_1288_, 0);
lean_inc_ref(v_ipv6_1292_);
lean_dec_ref_known(v_host_1288_, 1);
v___x_1293_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1294_ = lean_uv_ntop_v6(v_ipv6_1292_);
lean_dec_ref(v_ipv6_1292_);
v___x_1295_ = lean_string_append(v___x_1293_, v___x_1294_);
lean_dec_ref(v___x_1294_);
v___x_1296_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1297_ = lean_string_append(v___x_1295_, v___x_1296_);
v___y_1270_ = v___x_1297_;
goto v___jp_1269_;
}
}
}
default: 
{
lean_object* v_host_1298_; uint16_t v_port_1299_; lean_object* v___y_1301_; 
lean_inc_ref(v_port_1274_);
v_host_1298_ = lean_ctor_get(v_host_1264_, 0);
lean_inc_ref(v_host_1298_);
lean_dec_ref(v_host_1264_);
v_port_1299_ = lean_ctor_get_uint16(v_port_1274_, 0);
lean_dec_ref_known(v_port_1274_, 0);
switch(lean_obj_tag(v_host_1298_))
{
case 0:
{
lean_object* v_name_1308_; 
v_name_1308_ = lean_ctor_get(v_host_1298_, 0);
lean_inc_ref(v_name_1308_);
lean_dec_ref_known(v_host_1298_, 1);
v___y_1301_ = v_name_1308_;
goto v___jp_1300_;
}
case 1:
{
lean_object* v_ipv4_1309_; lean_object* v___x_1310_; 
v_ipv4_1309_ = lean_ctor_get(v_host_1298_, 0);
lean_inc_ref(v_ipv4_1309_);
lean_dec_ref_known(v_host_1298_, 1);
v___x_1310_ = lean_uv_ntop_v4(v_ipv4_1309_);
lean_dec_ref(v_ipv4_1309_);
v___y_1301_ = v___x_1310_;
goto v___jp_1300_;
}
default: 
{
lean_object* v_ipv6_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_ipv6_1311_ = lean_ctor_get(v_host_1298_, 0);
lean_inc_ref(v_ipv6_1311_);
lean_dec_ref_known(v_host_1298_, 1);
v___x_1312_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__1));
v___x_1313_ = lean_uv_ntop_v6(v_ipv6_1311_);
lean_dec_ref(v_ipv6_1311_);
v___x_1314_ = lean_string_append(v___x_1312_, v___x_1313_);
lean_dec_ref(v___x_1313_);
v___x_1315_ = ((lean_object*)(l_Array_repr___at___00Std_Http_Header_instReprTransferEncoding_repr_spec__0___closed__4));
v___x_1316_ = lean_string_append(v___x_1314_, v___x_1315_);
v___y_1301_ = v___x_1316_;
goto v___jp_1300_;
}
}
v___jp_1300_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1302_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1303_ = lean_string_append(v___y_1301_, v___x_1302_);
v___x_1304_ = lean_uint16_to_nat(v_port_1299_);
v___x_1305_ = l_Nat_reprFast(v___x_1304_);
v___x_1306_ = lean_string_append(v___x_1303_, v___x_1305_);
lean_dec_ref(v___x_1305_);
v___x_1307_ = l_Std_Http_Header_Value_ofString_x21(v___x_1306_);
v___y_1266_ = v___x_1307_;
goto v___jp_1265_;
}
}
}
v___jp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = ((lean_object*)(l_Std_Http_Header_instReprHost_repr___redArg___closed__0));
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v___y_1266_);
return v___x_1268_;
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((lean_object*)(l_Std_Http_Header_Host_serialize___closed__0));
v___x_1272_ = lean_string_append(v___y_1270_, v___x_1271_);
v___x_1273_ = l_Std_Http_Header_Value_ofString_x21(v___x_1272_);
v___y_1266_ = v___x_1273_;
goto v___jp_1265_;
}
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((lean_object*)(l_Std_Http_Header_instReprExpect_repr___redArg___closed__1));
v___x_1330_ = lean_obj_once(&l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10, &l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10_once, _init_l_Std_Http_Header_instReprContentLength_repr___redArg___closed__10);
v___x_1331_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
lean_ctor_set(v___x_1331_, 1, v___x_1329_);
return v___x_1331_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3(void){
_start:
{
uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = 0;
v___x_1333_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__2, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__2_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__2);
v___x_1334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set_uint8(v___x_1334_, sizeof(void*)*1, v___x_1332_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg(){
_start:
{
lean_object* v___x_1336_; 
v___x_1336_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___redArg___closed__3, &l_Std_Http_Header_instReprExpect_repr___redArg___closed__3_once, _init_l_Std_Http_Header_instReprExpect_repr___redArg___closed__3);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___redArg___boxed(lean_object* v___dummy_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v_res_1338_;
}
}
static lean_object* _init_l_Std_Http_Header_instReprExpect_repr___closed__0(void){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Std_Http_Header_instReprExpect_repr___redArg();
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr(lean_object* v_x_1340_, lean_object* v_prec_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_obj_once(&l_Std_Http_Header_instReprExpect_repr___closed__0, &l_Std_Http_Header_instReprExpect_repr___closed__0_once, _init_l_Std_Http_Header_instReprExpect_repr___closed__0);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instReprExpect_repr___boxed(lean_object* v_x_1343_, lean_object* v_prec_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Std_Http_Header_instReprExpect_repr(v_x_1343_, v_prec_1344_);
lean_dec(v_prec_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq___redArg(){
_start:
{
uint8_t v___x_1349_; 
v___x_1349_ = 1;
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___redArg___boxed(lean_object* v___dummy_1350_){
_start:
{
uint8_t v_res_1351_; lean_object* v_r_1352_; 
v_res_1351_ = l_Std_Http_Header_instBEqExpect_beq___redArg();
v_r_1352_ = lean_box(v_res_1351_);
return v_r_1352_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Header_instBEqExpect_beq(lean_object* v_x_1353_, lean_object* v_y_1354_){
_start:
{
uint8_t v___x_1355_; 
v___x_1355_ = 1;
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_instBEqExpect_beq___boxed(lean_object* v_x_1356_, lean_object* v_y_1357_){
_start:
{
uint8_t v_res_1358_; lean_object* v_r_1359_; 
v_res_1358_ = l_Std_Http_Header_instBEqExpect_beq(v_x_1356_, v_y_1357_);
v_r_1359_ = lean_box(v_res_1358_);
return v_r_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_parse(lean_object* v_v_1365_){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v_normalized_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_string_utf8_byte_size(v_v_1365_);
v___x_1368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1368_, 0, v_v_1365_);
lean_ctor_set(v___x_1368_, 1, v___x_1366_);
lean_ctor_set(v___x_1368_, 2, v___x_1367_);
v___x_1369_ = l_String_Slice_trimAscii(v___x_1368_);
v___x_1370_ = l_String_Slice_toString(v___x_1369_);
lean_dec_ref(v___x_1369_);
v_normalized_1371_ = l_String_mapAux___at___00__private_Std_Http_Data_Headers_Basic_0__Std_Http_Header_parseTokenList_spec__0(v___x_1370_, v___x_1366_);
v___x_1372_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1373_ = lean_string_dec_eq(v_normalized_1371_, v___x_1372_);
lean_dec_ref(v_normalized_1371_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_box(0);
return v___x_1374_;
}
else
{
lean_object* v___x_1375_; 
v___x_1375_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__1));
return v___x_1375_;
}
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l_Std_Http_Header_Expect_parse___closed__0));
v___x_1377_ = l_Std_Http_Header_Value_ofString_x21(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__0, &l_Std_Http_Header_Expect_serialize___redArg___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__0);
v___x_1379_ = l_Std_Http_Header_Name_expect;
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
lean_ctor_set(v___x_1380_, 1, v___x_1378_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg(){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___redArg___closed__1, &l_Std_Http_Header_Expect_serialize___redArg___closed__1_once, _init_l_Std_Http_Header_Expect_serialize___redArg___closed__1);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize___redArg___boxed(lean_object* v___dummy_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Std_Http_Header_Expect_serialize___redArg();
return v_res_1384_;
}
}
static lean_object* _init_l_Std_Http_Header_Expect_serialize___closed__0(void){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Std_Http_Header_Expect_serialize___redArg();
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Header_Expect_serialize(lean_object* v_x_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = lean_obj_once(&l_Std_Http_Header_Expect_serialize___closed__0, &l_Std_Http_Header_Expect_serialize___closed__0_once, _init_l_Std_Http_Header_Expect_serialize___closed__0);
return v___x_1387_;
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

// Lean compiler output
// Module: Lean.Data.Lsp.Communication
// Imports: public import Lean.Data.JsonRpc import Init.Data.String.TakeDrop import Init.Data.String.Search import Init.Data.Iterators.Consumers.Collect
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_beq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_Slice_intercalate(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_Lean_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IO_FS_Stream_readMessage(lean_object*, lean_object*);
lean_object* l_Lean_IO_FS_Stream_readUTF8(lean_object*, lean_object*);
lean_object* l_Lean_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0_value;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__1;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__4;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__5;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__6;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__7 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__7_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__7_value)}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__8 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0_value;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2;
static const lean_array_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__4 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "seq_num"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___boxed(lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Invalid header field: "};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 176, .m_capacity = 176, .m_length = 175, .m_data = "A Lean 3 request was received. Please ensure that your editor has a Lean 4 compatible extension installed. For VSCode, this is\n\n    https://github.com/leanprover/vscode-lean4 "};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__1_value;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Stream was closed"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__3 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__3_value;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__0 = (const lean_object*)&l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__0_value;
static const lean_string_object l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1 = (const lean_object*)&l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1_value;
static const lean_string_object l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__2 = (const lean_object*)&l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Content-Length"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "No Content-Length field in header: "};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__1_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Content-Length header field value '"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__2 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__2_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "' is not a Nat"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__3 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_readLspMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Cannot read LSP message: "};
static const lean_object* l_Lean_IO_FS_Stream_readLspMessage___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_readLspMessage___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_readLspRequestAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Cannot read LSP request: "};
static const lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_readLspRequestAs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Cannot read LSP notification: "};
static const lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_readLspResponseAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Cannot read LSP response: "};
static const lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_readLspResponseAs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Content-Length: "};
static const lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__0_value;
static const lean_string_object l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\r\n\r\n"};
static const lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__1 = (const lean_object*)&l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_IO_FS_Stream_writeLspMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "jsonrpc"};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__0 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__0_value;
static const lean_string_object l_Lean_IO_FS_Stream_writeLspMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "2.0"};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__1 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__1_value;
static const lean_ctor_object l_Lean_IO_FS_Stream_writeLspMessage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__1_value)}};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__2 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__2_value;
static const lean_ctor_object l_Lean_IO_FS_Stream_writeLspMessage___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__0_value),((lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__2_value)}};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__3 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__3_value;
static const lean_string_object l_Lean_IO_FS_Stream_writeLspMessage___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__4 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__4_value;
static const lean_string_object l_Lean_IO_FS_Stream_writeLspMessage___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__5 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__5_value;
static const lean_string_object l_Lean_IO_FS_Stream_writeLspMessage___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "params"};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__6 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__6_value;
static const lean_string_object l_Lean_IO_FS_Stream_writeLspMessage___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__7 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__7_value;
static const lean_string_object l_Lean_IO_FS_Stream_writeLspMessage___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__8 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__8_value;
static const lean_string_object l_Lean_IO_FS_Stream_writeLspMessage___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__9 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__9_value;
static const lean_string_object l_Lean_IO_FS_Stream_writeLspMessage___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__10 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__10_value;
static const lean_string_object l_Lean_IO_FS_Stream_writeLspMessage___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__11 = (const lean_object*)&l_Lean_IO_FS_Stream_writeLspMessage___closed__11_value;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__12;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__13;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__14;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__15;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__16;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__17;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__18;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__19;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__20;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__21;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__22;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__23;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__24;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__25;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__26;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__27;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__28;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__29;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__30;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__31;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__32;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__33;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__34;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__35;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__36;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__37;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__38;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__39;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__40;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__41;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__42;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__43;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__44;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__45;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__46;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__47;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__48;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__49;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__50;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__51;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__52;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__53;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__54;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__55;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__56;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__57;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__58;
static lean_once_cell_t l_Lean_IO_FS_Stream_writeLspMessage___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_IO_FS_Stream_writeLspMessage___closed__59;
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0));
v___x_3_ = lean_string_utf8_byte_size(v___x_2_);
return v___x_3_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__1);
v___x_6_ = lean_nat_dec_eq(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__1);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0));
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_7_);
return v___x_10_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3);
v___x_12_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__5(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__4);
v___x_15_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3);
v___x_16_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_13_);
lean_ctor_set(v___x_16_, 3, v___x_13_);
return v___x_16_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__6(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__5, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__5);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(lean_object* v_s_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__2);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__6, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__6_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__6);
return v___x_27_;
}
else
{
lean_object* v___x_28_; 
v___x_28_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__8));
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object* v_s_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(v_s_29_);
lean_dec_ref(v_s_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object* v_s_31_, lean_object* v___x_32_, lean_object* v___x_33_, lean_object* v_a_34_, lean_object* v_b_35_){
_start:
{
lean_object* v_it_37_; lean_object* v_startInclusive_38_; lean_object* v_endExclusive_39_; 
if (lean_obj_tag(v_a_34_) == 0)
{
lean_object* v_currPos_43_; lean_object* v_searcher_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_150_; 
v_currPos_43_ = lean_ctor_get(v_a_34_, 0);
v_searcher_44_ = lean_ctor_get(v_a_34_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_a_34_);
if (v_isSharedCheck_150_ == 0)
{
v___x_46_ = v_a_34_;
v_isShared_47_ = v_isSharedCheck_150_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_searcher_44_);
lean_inc(v_currPos_43_);
lean_dec(v_a_34_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_150_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v_it_49_; lean_object* v_it_55_; lean_object* v_startPos_56_; lean_object* v_endPos_57_; 
switch(lean_obj_tag(v_searcher_44_))
{
case 0:
{
lean_object* v_pos_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_82_; 
lean_del_object(v___x_46_);
v_pos_70_ = lean_ctor_get(v_searcher_44_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v_searcher_44_);
if (v_isSharedCheck_82_ == 0)
{
v___x_72_ = v_searcher_44_;
v_isShared_73_ = v_isSharedCheck_82_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_pos_70_);
lean_dec(v_searcher_44_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_82_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_startInclusive_74_; lean_object* v_endExclusive_75_; lean_object* v___x_76_; uint8_t v_decide_77_; 
v_startInclusive_74_ = lean_ctor_get(v___x_32_, 1);
v_endExclusive_75_ = lean_ctor_get(v___x_32_, 2);
v___x_76_ = lean_nat_sub(v_endExclusive_75_, v_startInclusive_74_);
v_decide_77_ = lean_nat_dec_eq(v_pos_70_, v___x_76_);
lean_dec(v___x_76_);
if (v_decide_77_ == 0)
{
lean_object* v___x_79_; 
lean_inc(v_pos_70_);
if (v_isShared_73_ == 0)
{
lean_ctor_set_tag(v___x_72_, 1);
v___x_79_ = v___x_72_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_pos_70_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_inc(v_pos_70_);
v_it_55_ = v___x_79_;
v_startPos_56_ = v_pos_70_;
v_endPos_57_ = v_pos_70_;
goto v___jp_54_;
}
}
else
{
lean_object* v___x_81_; 
lean_del_object(v___x_72_);
v___x_81_ = lean_box(3);
lean_inc(v_pos_70_);
v_it_55_ = v___x_81_;
v_startPos_56_ = v_pos_70_;
v_endPos_57_ = v_pos_70_;
goto v___jp_54_;
}
}
}
case 1:
{
lean_object* v_pos_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_91_; 
v_pos_83_ = lean_ctor_get(v_searcher_44_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v_searcher_44_);
if (v_isSharedCheck_91_ == 0)
{
v___x_85_ = v_searcher_44_;
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_pos_83_);
lean_dec(v_searcher_44_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_87_ = lean_string_utf8_next_fast(v_s_31_, v_pos_83_);
lean_dec(v_pos_83_);
if (v_isShared_86_ == 0)
{
lean_ctor_set_tag(v___x_85_, 0);
lean_ctor_set(v___x_85_, 0, v___x_87_);
v___x_89_ = v___x_85_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
v_it_49_ = v___x_89_;
goto v___jp_48_;
}
}
}
case 2:
{
lean_object* v_needle_92_; lean_object* v_table_93_; lean_object* v_stackPos_94_; lean_object* v_needlePos_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_149_; 
v_needle_92_ = lean_ctor_get(v_searcher_44_, 0);
v_table_93_ = lean_ctor_get(v_searcher_44_, 1);
v_stackPos_94_ = lean_ctor_get(v_searcher_44_, 2);
v_needlePos_95_ = lean_ctor_get(v_searcher_44_, 3);
v_isSharedCheck_149_ = !lean_is_exclusive(v_searcher_44_);
if (v_isSharedCheck_149_ == 0)
{
v___x_97_ = v_searcher_44_;
v_isShared_98_ = v_isSharedCheck_149_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_needlePos_95_);
lean_inc(v_stackPos_94_);
lean_inc(v_table_93_);
lean_inc(v_needle_92_);
lean_dec(v_searcher_44_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_149_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v_str_99_; lean_object* v_startInclusive_100_; lean_object* v_endExclusive_101_; lean_object* v_basePos_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_str_99_ = lean_ctor_get(v_needle_92_, 0);
v_startInclusive_100_ = lean_ctor_get(v_needle_92_, 1);
v_endExclusive_101_ = lean_ctor_get(v_needle_92_, 2);
v_basePos_102_ = lean_nat_sub(v_stackPos_94_, v_needlePos_95_);
v___x_103_ = lean_nat_sub(v_endExclusive_101_, v_startInclusive_100_);
v___x_104_ = lean_nat_add(v_basePos_102_, v___x_103_);
v___x_105_ = lean_nat_dec_le(v___x_104_, v___x_33_);
lean_dec(v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
lean_dec(v___x_103_);
lean_del_object(v___x_97_);
lean_dec(v_needlePos_95_);
lean_dec(v_stackPos_94_);
lean_dec_ref(v_table_93_);
lean_dec_ref(v_needle_92_);
v___x_106_ = lean_unsigned_to_nat(1u);
v___x_107_ = lean_nat_add(v_basePos_102_, v___x_106_);
lean_dec(v_basePos_102_);
v___x_108_ = lean_nat_dec_le(v___x_107_, v___x_33_);
lean_dec(v___x_107_);
if (v___x_108_ == 0)
{
lean_del_object(v___x_46_);
goto v___jp_68_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(3);
v_it_49_ = v___x_109_;
goto v___jp_48_;
}
}
else
{
uint8_t v_stackByte_110_; lean_object* v___x_111_; uint8_t v_patByte_112_; uint8_t v___x_113_; 
lean_dec(v_basePos_102_);
lean_inc(v_stackPos_94_);
v_stackByte_110_ = lean_string_get_byte_fast(v_s_31_, v_stackPos_94_);
v___x_111_ = lean_nat_add(v_startInclusive_100_, v_needlePos_95_);
v_patByte_112_ = lean_string_get_byte_fast(v_str_99_, v___x_111_);
v___x_113_ = lean_uint8_dec_eq(v_stackByte_110_, v_patByte_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; uint8_t v_decide_115_; 
lean_dec(v___x_103_);
v___x_114_ = lean_unsigned_to_nat(0u);
v_decide_115_ = lean_nat_dec_eq(v_needlePos_95_, v___x_114_);
if (v_decide_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_newNeedlePos_118_; uint8_t v___x_119_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = lean_nat_sub(v_needlePos_95_, v___x_116_);
lean_dec(v_needlePos_95_);
v_newNeedlePos_118_ = lean_array_fget_borrowed(v_table_93_, v___x_117_);
lean_dec(v___x_117_);
v___x_119_ = lean_nat_dec_eq(v_newNeedlePos_118_, v___x_114_);
if (v___x_119_ == 0)
{
lean_object* v___x_121_; 
lean_inc(v_newNeedlePos_118_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v_newNeedlePos_118_);
v___x_121_ = v___x_97_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_needle_92_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_table_93_);
lean_ctor_set(v_reuseFailAlloc_122_, 2, v_stackPos_94_);
lean_ctor_set(v_reuseFailAlloc_122_, 3, v_newNeedlePos_118_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
v_it_49_ = v___x_121_;
goto v___jp_48_;
}
}
else
{
lean_object* v_nextStackPos_123_; lean_object* v___x_125_; 
v_nextStackPos_123_ = l_String_Slice_posGE___redArg(v___x_32_, v_stackPos_94_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v___x_114_);
lean_ctor_set(v___x_97_, 2, v_nextStackPos_123_);
v___x_125_ = v___x_97_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_needle_92_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_table_93_);
lean_ctor_set(v_reuseFailAlloc_126_, 2, v_nextStackPos_123_);
lean_ctor_set(v_reuseFailAlloc_126_, 3, v___x_114_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
v_it_49_ = v___x_125_;
goto v___jp_48_;
}
}
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_nextStackPos_129_; lean_object* v___x_131_; 
lean_dec(v_needlePos_95_);
v___x_127_ = lean_unsigned_to_nat(1u);
v___x_128_ = lean_nat_add(v_stackPos_94_, v___x_127_);
lean_dec(v_stackPos_94_);
v_nextStackPos_129_ = l_String_Slice_posGE___redArg(v___x_32_, v___x_128_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v___x_114_);
lean_ctor_set(v___x_97_, 2, v_nextStackPos_129_);
v___x_131_ = v___x_97_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_needle_92_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v_table_93_);
lean_ctor_set(v_reuseFailAlloc_132_, 2, v_nextStackPos_129_);
lean_ctor_set(v_reuseFailAlloc_132_, 3, v___x_114_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
v_it_49_ = v___x_131_;
goto v___jp_48_;
}
}
}
else
{
lean_object* v___x_133_; lean_object* v_nextStackPos_134_; lean_object* v_nextNeedlePos_135_; uint8_t v_decide_136_; 
lean_del_object(v___x_46_);
v___x_133_ = lean_unsigned_to_nat(1u);
v_nextStackPos_134_ = lean_nat_add(v_stackPos_94_, v___x_133_);
lean_dec(v_stackPos_94_);
v_nextNeedlePos_135_ = lean_nat_add(v_needlePos_95_, v___x_133_);
lean_dec(v_needlePos_95_);
v_decide_136_ = lean_nat_dec_eq(v_nextNeedlePos_135_, v___x_103_);
lean_dec(v___x_103_);
if (v_decide_136_ == 0)
{
lean_object* v___x_138_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v_nextNeedlePos_135_);
lean_ctor_set(v___x_97_, 2, v_nextStackPos_134_);
v___x_138_ = v___x_97_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_needle_92_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_table_93_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_nextStackPos_134_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v_nextNeedlePos_135_);
v___x_138_ = v_reuseFailAlloc_141_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; 
v___x_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_139_, 0, v_currPos_43_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
v_a_34_ = v___x_139_;
goto _start;
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_142_ = lean_nat_sub(v_nextStackPos_134_, v_nextNeedlePos_135_);
lean_dec(v_nextNeedlePos_135_);
v___x_143_ = l_String_Slice_pos_x21(v___x_32_, v___x_142_);
lean_dec(v___x_142_);
v___x_144_ = l_String_Slice_pos_x21(v___x_32_, v_nextStackPos_134_);
v___x_145_ = lean_unsigned_to_nat(0u);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v___x_145_);
lean_ctor_set(v___x_97_, 2, v_nextStackPos_134_);
v___x_147_ = v___x_97_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_needle_92_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_table_93_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_nextStackPos_134_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
v_it_55_ = v___x_147_;
v_startPos_56_ = v___x_143_;
v_endPos_57_ = v___x_144_;
goto v___jp_54_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_46_);
goto v___jp_68_;
}
}
v___jp_48_:
{
lean_object* v___x_51_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v_it_49_);
v___x_51_ = v___x_46_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_currPos_43_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_it_49_);
v___x_51_ = v_reuseFailAlloc_53_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
v_a_34_ = v___x_51_;
goto _start;
}
}
v___jp_54_:
{
lean_object* v_slice_58_; lean_object* v_startInclusive_59_; lean_object* v_endExclusive_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
v_slice_58_ = l_String_Slice_subslice_x21(v___x_32_, v_currPos_43_, v_startPos_56_);
v_startInclusive_59_ = lean_ctor_get(v_slice_58_, 0);
v_endExclusive_60_ = lean_ctor_get(v_slice_58_, 1);
v_isSharedCheck_67_ = !lean_is_exclusive(v_slice_58_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v_slice_58_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_endExclusive_60_);
lean_inc(v_startInclusive_59_);
lean_dec(v_slice_58_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v_nextIt_65_; 
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v_it_55_);
lean_ctor_set(v___x_62_, 0, v_endPos_57_);
v_nextIt_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_endPos_57_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_it_55_);
v_nextIt_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
v_it_37_ = v_nextIt_65_;
v_startInclusive_38_ = v_startInclusive_59_;
v_endExclusive_39_ = v_endExclusive_60_;
goto v___jp_36_;
}
}
}
v___jp_68_:
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(1);
lean_inc(v___x_33_);
v_it_37_ = v___x_69_;
v_startInclusive_38_ = v_currPos_43_;
v_endExclusive_39_ = v___x_33_;
goto v___jp_36_;
}
}
}
else
{
lean_dec(v___x_33_);
lean_dec_ref(v_s_31_);
return v_b_35_;
}
v___jp_36_:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_inc_ref(v_s_31_);
v___x_40_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_40_, 0, v_s_31_);
lean_ctor_set(v___x_40_, 1, v_startInclusive_38_);
lean_ctor_set(v___x_40_, 2, v_endExclusive_39_);
v___x_41_ = lean_array_push(v_b_35_, v___x_40_);
v_a_34_ = v_it_37_;
v_b_35_ = v___x_41_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object* v_s_151_, lean_object* v___x_152_, lean_object* v___x_153_, lean_object* v_a_154_, lean_object* v_b_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_151_, v___x_152_, v___x_153_, v_a_154_, v_b_155_);
lean_dec_ref(v___x_152_);
return v_res_156_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0));
v___x_159_ = lean_string_utf8_byte_size(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0));
v___x_163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_160_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField(lean_object* v_s_167_){
_start:
{
uint8_t v___y_169_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__4));
v___x_206_ = lean_string_dec_eq(v_s_167_, v___x_205_);
if (v___x_206_ == 0)
{
uint8_t v___x_207_; 
v___x_207_ = 1;
v___y_169_ = v___x_207_;
goto v___jp_168_;
}
else
{
uint8_t v___x_208_; 
v___x_208_ = 0;
v___y_169_ = v___x_208_;
goto v___jp_168_;
}
v___jp_168_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = lean_string_utf8_byte_size(v_s_167_);
lean_inc_ref(v_s_167_);
v___x_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_172_, 0, v_s_167_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
lean_ctor_set(v___x_172_, 2, v___x_171_);
if (v___y_169_ == 0)
{
lean_object* v___x_173_; 
lean_dec_ref_known(v___x_172_, 3);
lean_dec_ref(v_s_167_);
v___x_173_ = lean_box(0);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_174_ = lean_unsigned_to_nat(2u);
v___x_175_ = l_String_Slice_Pos_prevn(v___x_172_, v___x_171_, v___x_174_);
lean_dec_ref_known(v___x_172_, 3);
lean_inc(v___x_175_);
lean_inc_ref(v_s_167_);
v___x_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_176_, 0, v_s_167_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
lean_ctor_set(v___x_176_, 2, v___x_171_);
v___x_177_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2);
v___x_178_ = l_String_Slice_beq(v___x_176_, v___x_177_);
lean_dec_ref_known(v___x_176_, 3);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; 
lean_dec(v___x_175_);
lean_dec_ref(v_s_167_);
v___x_179_ = lean_box(0);
return v___x_179_;
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
lean_inc(v___x_175_);
lean_inc_ref(v_s_167_);
v___x_180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_180_, 0, v_s_167_);
lean_ctor_set(v___x_180_, 1, v___x_170_);
lean_ctor_set(v___x_180_, 2, v___x_175_);
v___x_181_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(v___x_180_);
v___x_182_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3));
v___x_183_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_167_, v___x_180_, v___x_175_, v___x_181_, v___x_182_);
lean_dec_ref_known(v___x_180_, 3);
v___x_184_ = lean_array_to_list(v___x_183_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(0);
return v___x_185_;
}
else
{
lean_object* v_tail_186_; 
v_tail_186_ = lean_ctor_get(v___x_184_, 1);
lean_inc(v_tail_186_);
if (lean_obj_tag(v_tail_186_) == 0)
{
lean_object* v___x_187_; 
lean_dec_ref_known(v___x_184_, 2);
v___x_187_ = lean_box(0);
return v___x_187_;
}
else
{
lean_object* v_head_188_; lean_object* v_str_189_; lean_object* v_startInclusive_190_; lean_object* v_endExclusive_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_202_; 
v_head_188_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_head_188_);
lean_dec_ref_known(v___x_184_, 2);
v_str_189_ = lean_ctor_get(v_head_188_, 0);
lean_inc_ref(v_str_189_);
v_startInclusive_190_ = lean_ctor_get(v_head_188_, 1);
lean_inc(v_startInclusive_190_);
v_endExclusive_191_ = lean_ctor_get(v_head_188_, 2);
lean_inc(v_endExclusive_191_);
lean_dec(v_head_188_);
v___x_192_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__3);
v___x_193_ = l_String_Slice_intercalate(v___x_192_, v_tail_186_);
v_isSharedCheck_202_ = !lean_is_exclusive(v_tail_186_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; lean_object* v_unused_204_; 
v_unused_203_ = lean_ctor_get(v_tail_186_, 1);
lean_dec(v_unused_203_);
v_unused_204_ = lean_ctor_get(v_tail_186_, 0);
lean_dec(v_unused_204_);
v___x_195_ = v_tail_186_;
v_isShared_196_ = v_isSharedCheck_202_;
goto v_resetjp_194_;
}
else
{
lean_dec(v_tail_186_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_202_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_string_utf8_extract_fast(v_str_189_, v_startInclusive_190_, v_endExclusive_191_);
lean_dec(v_endExclusive_191_);
lean_dec(v_startInclusive_190_);
lean_dec_ref(v_str_189_);
if (v_isShared_196_ == 0)
{
lean_ctor_set_tag(v___x_195_, 0);
lean_ctor_set(v___x_195_, 1, v___x_193_);
lean_ctor_set(v___x_195_, 0, v___x_197_);
v___x_199_ = v___x_195_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_193_);
v___x_199_ = v_reuseFailAlloc_201_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(lean_object* v_s_209_, lean_object* v___x_210_, lean_object* v___x_211_, lean_object* v_inst_212_, lean_object* v_R_213_, lean_object* v_a_214_, lean_object* v_b_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_209_, v___x_210_, v___x_211_, v_a_214_, v_b_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object* v_s_217_, lean_object* v___x_218_, lean_object* v___x_219_, lean_object* v_inst_220_, lean_object* v_R_221_, lean_object* v_a_222_, lean_object* v_b_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(v_s_217_, v___x_218_, v___x_219_, v_inst_220_, v_R_221_, v_a_222_, v_b_223_);
lean_dec_ref(v___x_218_);
return v_res_224_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(lean_object* v_s_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_Json_parse(v_s_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
uint8_t v___x_229_; 
lean_dec_ref_known(v___x_228_, 1);
v___x_229_ = 0;
return v___x_229_;
}
else
{
lean_object* v_a_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_a_230_ = lean_ctor_get(v___x_228_, 0);
lean_inc_n(v_a_230_, 2);
lean_dec_ref_known(v___x_228_, 1);
v___x_231_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__0));
v___x_232_ = l_Lean_Json_getObjVal_x3f(v_a_230_, v___x_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
uint8_t v___x_233_; 
lean_dec_ref_known(v___x_232_, 1);
lean_dec(v_a_230_);
v___x_233_ = 0;
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec_ref_known(v___x_232_, 1);
v___x_234_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__1));
v___x_235_ = l_Lean_Json_getObjVal_x3f(v_a_230_, v___x_234_);
if (lean_obj_tag(v___x_235_) == 0)
{
uint8_t v___x_236_; 
lean_dec_ref_known(v___x_235_, 1);
v___x_236_ = 0;
return v___x_236_;
}
else
{
uint8_t v___x_237_; 
lean_dec_ref_known(v___x_235_, 1);
v___x_237_ = 1;
return v___x_237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___boxed(lean_object* v_s_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_s_238_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__1));
v___x_244_ = lean_mk_io_user_error(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__3));
v___x_247_ = lean_mk_io_user_error(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(lean_object* v_h_248_){
_start:
{
lean_object* v_getLine_250_; lean_object* v___x_251_; 
v_getLine_250_ = lean_ctor_get(v_h_248_, 3);
lean_inc_ref(v_getLine_250_);
v___x_251_ = lean_apply_1(v_getLine_250_, lean_box(0));
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_296_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_296_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_296_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_296_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = lean_string_utf8_byte_size(v_a_252_);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_nat_dec_eq(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0));
v___x_260_ = lean_string_dec_eq(v_a_252_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_inc(v_a_252_);
v___x_261_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField(v_a_252_);
if (lean_obj_tag(v___x_261_) == 0)
{
uint8_t v___x_262_; 
lean_dec_ref(v_h_248_);
lean_inc(v_a_252_);
v___x_262_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_a_252_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__0));
v___x_264_ = l_String_quote(v_a_252_);
v___x_265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
v___x_266_ = l_Std_Format_defWidth;
v___x_267_ = l_Std_Format_pretty(v___x_265_, v___x_266_, v___x_257_, v___x_257_);
v___x_268_ = lean_string_append(v___x_263_, v___x_267_);
lean_dec_ref(v___x_267_);
v___x_269_ = lean_mk_io_user_error(v___x_268_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 1);
lean_ctor_set(v___x_254_, 0, v___x_269_);
v___x_271_ = v___x_254_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
else
{
lean_object* v___x_273_; lean_object* v___x_275_; 
lean_dec(v_a_252_);
v___x_273_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 1);
lean_ctor_set(v___x_254_, 0, v___x_273_);
v___x_275_ = v___x_254_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
else
{
lean_object* v_val_277_; lean_object* v___x_278_; 
lean_del_object(v___x_254_);
lean_dec(v_a_252_);
v_val_277_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_val_277_);
lean_dec_ref_known(v___x_261_, 1);
v___x_278_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_248_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_287_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_283_, 0, v_val_277_);
lean_ctor_set(v___x_283_, 1, v_a_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
else
{
lean_dec(v_val_277_);
return v___x_278_;
}
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_290_; 
lean_dec(v_a_252_);
lean_dec_ref(v_h_248_);
v___x_288_ = lean_box(0);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_288_);
v___x_290_ = v___x_254_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_294_; 
lean_dec(v_a_252_);
lean_dec_ref(v_h_248_);
v___x_292_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 1);
lean_ctor_set(v___x_254_, 0, v___x_292_);
v___x_294_ = v___x_254_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec_ref(v_h_248_);
v_a_297_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_251_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_251_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___boxed(lean_object* v_h_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_object* v___x_310_; 
v___x_310_ = lean_box(0);
return v___x_310_;
}
else
{
lean_object* v_head_311_; lean_object* v_tail_312_; lean_object* v_fst_313_; lean_object* v_snd_314_; uint8_t v___x_315_; 
v_head_311_ = lean_ctor_get(v_x_309_, 0);
v_tail_312_ = lean_ctor_get(v_x_309_, 1);
v_fst_313_ = lean_ctor_get(v_head_311_, 0);
v_snd_314_ = lean_ctor_get(v_head_311_, 1);
v___x_315_ = lean_string_dec_eq(v_x_308_, v_fst_313_);
if (v___x_315_ == 0)
{
v_x_309_ = v_tail_312_;
goto _start;
}
else
{
lean_object* v___x_317_; 
lean_inc(v_snd_314_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v_snd_314_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object* v_x_318_, lean_object* v_x_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_318_, v_x_319_);
lean_dec(v_x_319_);
lean_dec_ref(v_x_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
return v_x_324_;
}
else
{
lean_object* v_head_326_; lean_object* v_tail_327_; lean_object* v_fst_328_; lean_object* v_snd_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_head_326_ = lean_ctor_get(v_x_325_, 0);
v_tail_327_ = lean_ctor_get(v_x_325_, 1);
v_fst_328_ = lean_ctor_get(v_head_326_, 0);
v_snd_329_ = lean_ctor_get(v_head_326_, 1);
v___x_330_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_331_ = lean_string_append(v_x_324_, v___x_330_);
v___x_332_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_333_ = lean_string_append(v___x_332_, v_fst_328_);
v___x_334_ = lean_string_append(v___x_333_, v___x_330_);
v___x_335_ = lean_string_append(v___x_334_, v_snd_329_);
v___x_336_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_337_ = lean_string_append(v___x_335_, v___x_336_);
v___x_338_ = lean_string_append(v___x_331_, v___x_337_);
lean_dec_ref(v___x_337_);
v_x_324_ = v___x_338_;
v_x_325_ = v_tail_327_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(v_x_340_, v_x_341_);
lean_dec(v_x_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_346_) == 0)
{
lean_object* v___x_347_; 
v___x_347_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__0));
return v___x_347_;
}
else
{
lean_object* v_tail_348_; 
v_tail_348_ = lean_ctor_get(v_x_346_, 1);
if (lean_obj_tag(v_tail_348_) == 0)
{
lean_object* v_head_349_; lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_head_349_ = lean_ctor_get(v_x_346_, 0);
v_fst_350_ = lean_ctor_get(v_head_349_, 0);
v_snd_351_ = lean_ctor_get(v_head_349_, 1);
v___x_352_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_353_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_354_ = lean_string_append(v___x_353_, v_fst_350_);
v___x_355_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_356_ = lean_string_append(v___x_354_, v___x_355_);
v___x_357_ = lean_string_append(v___x_356_, v_snd_351_);
v___x_358_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_359_ = lean_string_append(v___x_357_, v___x_358_);
v___x_360_ = lean_string_append(v___x_352_, v___x_359_);
lean_dec_ref(v___x_359_);
v___x_361_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__2));
v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
return v___x_362_;
}
else
{
lean_object* v_head_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint32_t v___x_376_; lean_object* v___x_377_; 
v_head_363_ = lean_ctor_get(v_x_346_, 0);
v_fst_364_ = lean_ctor_get(v_head_363_, 0);
v_snd_365_ = lean_ctor_get(v_head_363_, 1);
v___x_366_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_367_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_368_ = lean_string_append(v___x_367_, v_fst_364_);
v___x_369_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_370_ = lean_string_append(v___x_368_, v___x_369_);
v___x_371_ = lean_string_append(v___x_370_, v_snd_365_);
v___x_372_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_373_ = lean_string_append(v___x_371_, v___x_372_);
v___x_374_ = lean_string_append(v___x_366_, v___x_373_);
lean_dec_ref(v___x_373_);
v___x_375_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(v___x_374_, v_tail_348_);
v___x_376_ = 93;
v___x_377_ = lean_string_push(v___x_375_, v___x_376_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object* v_x_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(v_x_378_);
lean_dec(v_x_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(lean_object* v_h_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_384_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v_a_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_417_; 
v_a_387_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_417_ == 0)
{
v___x_389_ = v___x_386_;
v_isShared_390_ = v_isSharedCheck_417_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_a_387_);
lean_dec(v___x_386_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_417_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__0));
v___x_392_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v___x_391_, v_a_387_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_393_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__1));
v___x_394_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(v_a_387_);
lean_dec(v_a_387_);
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
lean_dec_ref(v___x_394_);
v___x_396_ = lean_mk_io_user_error(v___x_395_);
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 1);
lean_ctor_set(v___x_389_, 0, v___x_396_);
v___x_398_ = v___x_389_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
else
{
lean_object* v_val_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_a_387_);
v_val_400_ = lean_ctor_get(v___x_392_, 0);
lean_inc_n(v_val_400_, 2);
lean_dec_ref_known(v___x_392_, 1);
v___x_401_ = lean_unsigned_to_nat(0u);
v___x_402_ = lean_string_utf8_byte_size(v_val_400_);
v___x_403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_403_, 0, v_val_400_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
lean_ctor_set(v___x_403_, 2, v___x_402_);
v___x_404_ = l_String_Slice_toNat_x3f(v___x_403_);
lean_dec_ref_known(v___x_403_, 3);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__2));
v___x_406_ = lean_string_append(v___x_405_, v_val_400_);
lean_dec(v_val_400_);
v___x_407_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__3));
v___x_408_ = lean_string_append(v___x_406_, v___x_407_);
v___x_409_ = lean_mk_io_user_error(v___x_408_);
if (v_isShared_390_ == 0)
{
lean_ctor_set_tag(v___x_389_, 1);
lean_ctor_set(v___x_389_, 0, v___x_409_);
v___x_411_ = v___x_389_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
else
{
lean_object* v_val_413_; lean_object* v___x_415_; 
lean_dec(v_val_400_);
v_val_413_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_val_413_);
lean_dec_ref_known(v___x_404_, 1);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v_val_413_);
v___x_415_ = v___x_389_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_val_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
v_a_418_ = lean_ctor_get(v___x_386_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_386_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_386_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___boxed(lean_object* v_h_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0(lean_object* v_00_u03b2_429_, lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_430_, v_x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object* v_00_u03b2_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0(v_00_u03b2_433_, v_x_434_, v_x_435_);
lean_dec(v_x_435_);
lean_dec_ref(v_x_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage(lean_object* v_h_438_){
_start:
{
lean_object* v_a_441_; lean_object* v___x_447_; 
lean_inc_ref(v_h_438_);
v___x_447_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_438_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = l_Lean_IO_FS_Stream_readMessage(v_h_438_, v_a_448_);
lean_dec(v_a_448_);
if (lean_obj_tag(v___x_449_) == 0)
{
return v___x_449_;
}
else
{
lean_object* v_a_450_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v_a_441_ = v_a_450_;
goto v___jp_440_;
}
}
else
{
lean_object* v_a_451_; 
lean_dec_ref(v_h_438_);
v_a_451_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_447_, 1);
v_a_441_ = v_a_451_;
goto v___jp_440_;
}
v___jp_440_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_442_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspMessage___closed__0));
v___x_443_ = lean_io_error_to_string(v_a_441_);
v___x_444_ = lean_string_append(v___x_442_, v___x_443_);
lean_dec_ref(v___x_443_);
v___x_445_ = lean_mk_io_user_error(v___x_444_);
v___x_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage___boxed(lean_object* v_h_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_IO_FS_Stream_readLspMessage(v_h_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString(lean_object* v_h_455_){
_start:
{
lean_object* v_a_458_; lean_object* v___x_464_; 
lean_inc_ref(v_h_455_);
v___x_464_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_455_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v___x_466_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = l_Lean_IO_FS_Stream_readUTF8(v_h_455_, v_a_465_);
lean_dec(v_a_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
return v___x_466_;
}
else
{
lean_object* v_a_467_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
lean_dec_ref_known(v___x_466_, 1);
v_a_458_ = v_a_467_;
goto v___jp_457_;
}
}
else
{
lean_object* v_a_468_; 
lean_dec_ref(v_h_455_);
v_a_468_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_464_, 1);
v_a_458_ = v_a_468_;
goto v___jp_457_;
}
v___jp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_459_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspMessage___closed__0));
v___x_460_ = lean_io_error_to_string(v_a_458_);
v___x_461_ = lean_string_append(v___x_459_, v___x_460_);
lean_dec_ref(v___x_460_);
v___x_462_ = lean_mk_io_user_error(v___x_461_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
return v___x_463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString___boxed(lean_object* v_h_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_IO_FS_Stream_readLspMessageAsString(v_h_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg(lean_object* v_h_473_, lean_object* v_expectedMethod_474_, lean_object* v_inst_475_){
_start:
{
lean_object* v_a_478_; lean_object* v___x_484_; 
lean_inc_ref(v_h_473_);
v___x_484_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_473_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_486_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v___x_486_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_473_, v_a_485_, v_expectedMethod_474_, v_inst_475_);
lean_dec(v_a_485_);
if (lean_obj_tag(v___x_486_) == 0)
{
return v___x_486_;
}
else
{
lean_object* v_a_487_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref_known(v___x_486_, 1);
v_a_478_ = v_a_487_;
goto v___jp_477_;
}
}
else
{
lean_object* v_a_488_; 
lean_dec_ref(v_inst_475_);
lean_dec_ref(v_expectedMethod_474_);
lean_dec_ref(v_h_473_);
v_a_488_ = lean_ctor_get(v___x_484_, 0);
lean_inc(v_a_488_);
lean_dec_ref_known(v___x_484_, 1);
v_a_478_ = v_a_488_;
goto v___jp_477_;
}
v___jp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_479_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspRequestAs___redArg___closed__0));
v___x_480_ = lean_io_error_to_string(v_a_478_);
v___x_481_ = lean_string_append(v___x_479_, v___x_480_);
lean_dec_ref(v___x_480_);
v___x_482_ = lean_mk_io_user_error(v___x_481_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object* v_h_489_, lean_object* v_expectedMethod_490_, lean_object* v_inst_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_489_, v_expectedMethod_490_, v_inst_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs(lean_object* v_h_494_, lean_object* v_expectedMethod_495_, lean_object* v_00_u03b1_496_, lean_object* v_inst_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_494_, v_expectedMethod_495_, v_inst_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___boxed(lean_object* v_h_500_, lean_object* v_expectedMethod_501_, lean_object* v_00_u03b1_502_, lean_object* v_inst_503_, lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_IO_FS_Stream_readLspRequestAs(v_h_500_, v_expectedMethod_501_, v_00_u03b1_502_, v_inst_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(lean_object* v_h_507_, lean_object* v_expectedMethod_508_, lean_object* v_inst_509_){
_start:
{
lean_object* v_a_512_; lean_object* v___x_518_; 
lean_inc_ref(v_h_507_);
v___x_518_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_507_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_520_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v___x_520_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_507_, v_a_519_, v_expectedMethod_508_, v_inst_509_);
lean_dec(v_a_519_);
if (lean_obj_tag(v___x_520_) == 0)
{
return v___x_520_;
}
else
{
lean_object* v_a_521_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_520_, 1);
v_a_512_ = v_a_521_;
goto v___jp_511_;
}
}
else
{
lean_object* v_a_522_; 
lean_dec_ref(v_inst_509_);
lean_dec_ref(v_expectedMethod_508_);
lean_dec_ref(v_h_507_);
v_a_522_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_518_, 1);
v_a_512_ = v_a_522_;
goto v___jp_511_;
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_513_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___closed__0));
v___x_514_ = lean_io_error_to_string(v_a_512_);
v___x_515_ = lean_string_append(v___x_513_, v___x_514_);
lean_dec_ref(v___x_514_);
v___x_516_ = lean_mk_io_user_error(v___x_515_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object* v_h_523_, lean_object* v_expectedMethod_524_, lean_object* v_inst_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_523_, v_expectedMethod_524_, v_inst_525_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs(lean_object* v_h_528_, lean_object* v_expectedMethod_529_, lean_object* v_00_u03b1_530_, lean_object* v_inst_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_528_, v_expectedMethod_529_, v_inst_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___boxed(lean_object* v_h_534_, lean_object* v_expectedMethod_535_, lean_object* v_00_u03b1_536_, lean_object* v_inst_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lean_IO_FS_Stream_readLspNotificationAs(v_h_534_, v_expectedMethod_535_, v_00_u03b1_536_, v_inst_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg(lean_object* v_h_541_, lean_object* v_expectedID_542_, lean_object* v_inst_543_){
_start:
{
lean_object* v_a_546_; lean_object* v___x_552_; 
lean_inc_ref(v_h_541_);
v___x_552_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_541_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_552_, 1);
v___x_554_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_541_, v_a_553_, v_expectedID_542_, v_inst_543_);
lean_dec(v_a_553_);
if (lean_obj_tag(v___x_554_) == 0)
{
return v___x_554_;
}
else
{
lean_object* v_a_555_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v_a_546_ = v_a_555_;
goto v___jp_545_;
}
}
else
{
lean_object* v_a_556_; 
lean_dec_ref(v_inst_543_);
lean_dec(v_expectedID_542_);
lean_dec_ref(v_h_541_);
v_a_556_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v___x_552_, 1);
v_a_546_ = v_a_556_;
goto v___jp_545_;
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_547_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspResponseAs___redArg___closed__0));
v___x_548_ = lean_io_error_to_string(v_a_546_);
v___x_549_ = lean_string_append(v___x_547_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_550_ = lean_mk_io_user_error(v___x_549_);
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object* v_h_557_, lean_object* v_expectedID_558_, lean_object* v_inst_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_557_, v_expectedID_558_, v_inst_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs(lean_object* v_h_562_, lean_object* v_expectedID_563_, lean_object* v_00_u03b1_564_, lean_object* v_inst_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_562_, v_expectedID_563_, v_inst_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___boxed(lean_object* v_h_568_, lean_object* v_expectedID_569_, lean_object* v_00_u03b1_570_, lean_object* v_inst_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_IO_FS_Stream_readLspResponseAs(v_h_568_, v_expectedID_569_, v_00_u03b1_570_, v_inst_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage(lean_object* v_h_576_, lean_object* v_msg_577_){
_start:
{
lean_object* v_flush_579_; lean_object* v_putStr_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v_header_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_flush_579_ = lean_ctor_get(v_h_576_, 0);
lean_inc_ref(v_flush_579_);
v_putStr_580_ = lean_ctor_get(v_h_576_, 4);
lean_inc_ref(v_putStr_580_);
lean_dec_ref(v_h_576_);
v___x_581_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__0));
v___x_582_ = lean_string_utf8_byte_size(v_msg_577_);
v___x_583_ = l_Nat_reprFast(v___x_582_);
v___x_584_ = lean_string_append(v___x_581_, v___x_583_);
lean_dec_ref(v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__1));
v_header_586_ = lean_string_append(v___x_584_, v___x_585_);
v___x_587_ = lean_string_append(v_header_586_, v_msg_577_);
v___x_588_ = lean_apply_2(v_putStr_580_, v___x_587_, lean_box(0));
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_589_; 
lean_dec_ref_known(v___x_588_, 1);
v___x_589_ = lean_apply_1(v_flush_579_, lean_box(0));
return v___x_589_;
}
else
{
lean_dec_ref(v_flush_579_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object* v_h_590_, lean_object* v_msg_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_IO_FS_Stream_writeSerializedLspMessage(v_h_590_, v_msg_591_);
lean_dec_ref(v_msg_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(lean_object* v_k_594_, lean_object* v_x_595_){
_start:
{
if (lean_obj_tag(v_x_595_) == 0)
{
lean_object* v___x_596_; 
lean_dec_ref(v_k_594_);
v___x_596_ = lean_box(0);
return v___x_596_;
}
else
{
lean_object* v_val_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_val_597_ = lean_ctor_get(v_x_595_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v_x_595_, 1);
v___x_598_ = l_Lean_Json_Structured_toJson(v_val_597_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_k_594_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = lean_box(0);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(lean_object* v_k_602_, lean_object* v_x_603_){
_start:
{
if (lean_obj_tag(v_x_603_) == 0)
{
lean_object* v___x_604_; 
lean_dec_ref(v_k_602_);
v___x_604_ = lean_box(0);
return v___x_604_;
}
else
{
lean_object* v_val_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_val_605_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_val_605_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v_k_602_);
lean_ctor_set(v___x_606_, 1, v_val_605_);
v___x_607_ = lean_box(0);
v___x_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1___boxed(lean_object* v_k_609_, lean_object* v_x_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(v_k_609_, v_x_610_);
lean_dec(v_x_610_);
return v_res_611_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__12(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(32700u);
v___x_628_ = lean_nat_to_int(v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__13(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__12, &l_Lean_IO_FS_Stream_writeLspMessage___closed__12_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__12);
v___x_630_ = lean_int_neg(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__14(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__13, &l_Lean_IO_FS_Stream_writeLspMessage___closed__13_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__13);
v___x_632_ = l_Lean_JsonNumber_fromInt(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__15(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__14, &l_Lean_IO_FS_Stream_writeLspMessage___closed__14_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__14);
v___x_634_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__16(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_unsigned_to_nat(32600u);
v___x_636_ = lean_nat_to_int(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__17(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__16, &l_Lean_IO_FS_Stream_writeLspMessage___closed__16_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__16);
v___x_638_ = lean_int_neg(v___x_637_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__18(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__17, &l_Lean_IO_FS_Stream_writeLspMessage___closed__17_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__17);
v___x_640_ = l_Lean_JsonNumber_fromInt(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__19(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__18, &l_Lean_IO_FS_Stream_writeLspMessage___closed__18_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__18);
v___x_642_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__20(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_unsigned_to_nat(32601u);
v___x_644_ = lean_nat_to_int(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__21(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__20, &l_Lean_IO_FS_Stream_writeLspMessage___closed__20_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__20);
v___x_646_ = lean_int_neg(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__22(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__21, &l_Lean_IO_FS_Stream_writeLspMessage___closed__21_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__21);
v___x_648_ = l_Lean_JsonNumber_fromInt(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__23(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__22, &l_Lean_IO_FS_Stream_writeLspMessage___closed__22_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__22);
v___x_650_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__24(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_unsigned_to_nat(32602u);
v___x_652_ = lean_nat_to_int(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__25(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__24, &l_Lean_IO_FS_Stream_writeLspMessage___closed__24_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__24);
v___x_654_ = lean_int_neg(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__26(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__25, &l_Lean_IO_FS_Stream_writeLspMessage___closed__25_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__25);
v___x_656_ = l_Lean_JsonNumber_fromInt(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__27(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__26, &l_Lean_IO_FS_Stream_writeLspMessage___closed__26_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__26);
v___x_658_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__28(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_unsigned_to_nat(32603u);
v___x_660_ = lean_nat_to_int(v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__29(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__28, &l_Lean_IO_FS_Stream_writeLspMessage___closed__28_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__28);
v___x_662_ = lean_int_neg(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__30(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__29, &l_Lean_IO_FS_Stream_writeLspMessage___closed__29_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__29);
v___x_664_ = l_Lean_JsonNumber_fromInt(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__31(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__30, &l_Lean_IO_FS_Stream_writeLspMessage___closed__30_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__30);
v___x_666_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__32(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_unsigned_to_nat(32002u);
v___x_668_ = lean_nat_to_int(v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__33(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__32, &l_Lean_IO_FS_Stream_writeLspMessage___closed__32_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__32);
v___x_670_ = lean_int_neg(v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__34(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__33, &l_Lean_IO_FS_Stream_writeLspMessage___closed__33_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__33);
v___x_672_ = l_Lean_JsonNumber_fromInt(v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__35(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__34, &l_Lean_IO_FS_Stream_writeLspMessage___closed__34_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__34);
v___x_674_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__36(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_unsigned_to_nat(32001u);
v___x_676_ = lean_nat_to_int(v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__37(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__36, &l_Lean_IO_FS_Stream_writeLspMessage___closed__36_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__36);
v___x_678_ = lean_int_neg(v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__38(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__37, &l_Lean_IO_FS_Stream_writeLspMessage___closed__37_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__37);
v___x_680_ = l_Lean_JsonNumber_fromInt(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__39(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__38, &l_Lean_IO_FS_Stream_writeLspMessage___closed__38_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__38);
v___x_682_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__40(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_unsigned_to_nat(32801u);
v___x_684_ = lean_nat_to_int(v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__41(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__40, &l_Lean_IO_FS_Stream_writeLspMessage___closed__40_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__40);
v___x_686_ = lean_int_neg(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__42(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__41, &l_Lean_IO_FS_Stream_writeLspMessage___closed__41_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__41);
v___x_688_ = l_Lean_JsonNumber_fromInt(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__43(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__42, &l_Lean_IO_FS_Stream_writeLspMessage___closed__42_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__42);
v___x_690_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__44(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_unsigned_to_nat(32800u);
v___x_692_ = lean_nat_to_int(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__45(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__44, &l_Lean_IO_FS_Stream_writeLspMessage___closed__44_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__44);
v___x_694_ = lean_int_neg(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__46(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__45, &l_Lean_IO_FS_Stream_writeLspMessage___closed__45_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__45);
v___x_696_ = l_Lean_JsonNumber_fromInt(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__47(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__46, &l_Lean_IO_FS_Stream_writeLspMessage___closed__46_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__46);
v___x_698_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__48(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_unsigned_to_nat(32900u);
v___x_700_ = lean_nat_to_int(v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__49(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__48, &l_Lean_IO_FS_Stream_writeLspMessage___closed__48_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__48);
v___x_702_ = lean_int_neg(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__50(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__49, &l_Lean_IO_FS_Stream_writeLspMessage___closed__49_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__49);
v___x_704_ = l_Lean_JsonNumber_fromInt(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__51(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__50, &l_Lean_IO_FS_Stream_writeLspMessage___closed__50_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__50);
v___x_706_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__52(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_unsigned_to_nat(32901u);
v___x_708_ = lean_nat_to_int(v___x_707_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__53(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__52, &l_Lean_IO_FS_Stream_writeLspMessage___closed__52_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__52);
v___x_710_ = lean_int_neg(v___x_709_);
return v___x_710_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__54(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__53, &l_Lean_IO_FS_Stream_writeLspMessage___closed__53_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__53);
v___x_712_ = l_Lean_JsonNumber_fromInt(v___x_711_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__55(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__54, &l_Lean_IO_FS_Stream_writeLspMessage___closed__54_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__54);
v___x_714_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__56(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_unsigned_to_nat(32902u);
v___x_716_ = lean_nat_to_int(v___x_715_);
return v___x_716_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__57(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__56, &l_Lean_IO_FS_Stream_writeLspMessage___closed__56_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__56);
v___x_718_ = lean_int_neg(v___x_717_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__58(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__57, &l_Lean_IO_FS_Stream_writeLspMessage___closed__57_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__57);
v___x_720_ = l_Lean_JsonNumber_fromInt(v___x_719_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__59(void){
_start:
{
lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_721_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__58, &l_Lean_IO_FS_Stream_writeLspMessage___closed__58_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__58);
v___x_722_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage(lean_object* v_h_723_, lean_object* v_msg_724_){
_start:
{
lean_object* v___x_726_; lean_object* v___y_728_; 
v___x_726_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__3));
switch(lean_obj_tag(v_msg_724_))
{
case 0:
{
lean_object* v_id_733_; lean_object* v_method_734_; lean_object* v_params_x3f_735_; lean_object* v___x_736_; lean_object* v___y_738_; 
v_id_733_ = lean_ctor_get(v_msg_724_, 0);
lean_inc(v_id_733_);
v_method_734_ = lean_ctor_get(v_msg_724_, 1);
lean_inc_ref(v_method_734_);
v_params_x3f_735_ = lean_ctor_get(v_msg_724_, 2);
lean_inc(v_params_x3f_735_);
lean_dec_ref_known(v_msg_724_, 3);
v___x_736_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_733_))
{
case 0:
{
lean_object* v_s_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
v_s_749_ = lean_ctor_get(v_id_733_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v_id_733_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v_id_733_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_s_749_);
lean_dec(v_id_733_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 3);
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_s_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
v___y_738_ = v___x_754_;
goto v___jp_737_;
}
}
}
case 1:
{
lean_object* v_n_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
v_n_757_ = lean_ctor_get(v_id_733_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_id_733_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v_id_733_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_n_757_);
lean_dec(v_id_733_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
lean_ctor_set_tag(v___x_759_, 2);
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_n_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
v___y_738_ = v___x_762_;
goto v___jp_737_;
}
}
}
default: 
{
lean_object* v___x_765_; 
v___x_765_ = lean_box(0);
v___y_738_ = v___x_765_;
goto v___jp_737_;
}
}
v___jp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_736_);
lean_ctor_set(v___x_739_, 1, v___y_738_);
v___x_740_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__5));
v___x_741_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_741_, 0, v_method_734_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_box(0);
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_739_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v___x_746_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__6));
v___x_747_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(v___x_746_, v_params_x3f_735_);
v___x_748_ = l_List_appendTR___redArg(v___x_745_, v___x_747_);
v___y_728_ = v___x_748_;
goto v___jp_727_;
}
}
case 1:
{
lean_object* v_method_766_; lean_object* v_params_x3f_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_779_; 
v_method_766_ = lean_ctor_get(v_msg_724_, 0);
v_params_x3f_767_ = lean_ctor_get(v_msg_724_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_msg_724_);
if (v_isSharedCheck_779_ == 0)
{
v___x_769_ = v_msg_724_;
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_params_x3f_767_);
lean_inc(v_method_766_);
lean_dec(v_msg_724_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_771_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__5));
v___x_772_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_772_, 0, v_method_766_);
if (v_isShared_770_ == 0)
{
lean_ctor_set_tag(v___x_769_, 0);
lean_ctor_set(v___x_769_, 1, v___x_772_);
lean_ctor_set(v___x_769_, 0, v___x_771_);
v___x_774_ = v___x_769_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__6));
v___x_776_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(v___x_775_, v_params_x3f_767_);
v___x_777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_774_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___y_728_ = v___x_777_;
goto v___jp_727_;
}
}
}
case 2:
{
lean_object* v_id_780_; lean_object* v_result_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_813_; 
v_id_780_ = lean_ctor_get(v_msg_724_, 0);
v_result_781_ = lean_ctor_get(v_msg_724_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_msg_724_);
if (v_isSharedCheck_813_ == 0)
{
v___x_783_ = v_msg_724_;
v_isShared_784_ = v_isSharedCheck_813_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_result_781_);
lean_inc(v_id_780_);
lean_dec(v_msg_724_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_813_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; lean_object* v___y_787_; 
v___x_785_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_780_))
{
case 0:
{
lean_object* v_s_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_803_; 
v_s_796_ = lean_ctor_get(v_id_780_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v_id_780_);
if (v_isSharedCheck_803_ == 0)
{
v___x_798_ = v_id_780_;
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_s_796_);
lean_dec(v_id_780_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_803_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 3);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_s_796_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
v___y_787_ = v___x_801_;
goto v___jp_786_;
}
}
}
case 1:
{
lean_object* v_n_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
v_n_804_ = lean_ctor_get(v_id_780_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_id_780_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v_id_780_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_n_804_);
lean_dec(v_id_780_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 2);
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_n_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v___y_787_ = v___x_809_;
goto v___jp_786_;
}
}
}
default: 
{
lean_object* v___x_812_; 
v___x_812_ = lean_box(0);
v___y_787_ = v___x_812_;
goto v___jp_786_;
}
}
v___jp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set_tag(v___x_783_, 0);
lean_ctor_set(v___x_783_, 1, v___y_787_);
lean_ctor_set(v___x_783_, 0, v___x_785_);
v___x_789_ = v___x_783_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v___y_787_);
v___x_789_ = v_reuseFailAlloc_795_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_790_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__7));
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v_result_781_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_789_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___y_728_ = v___x_794_;
goto v___jp_727_;
}
}
}
}
default: 
{
lean_object* v_id_814_; uint8_t v_code_815_; lean_object* v_message_816_; lean_object* v_data_x3f_817_; lean_object* v___y_819_; lean_object* v___y_820_; lean_object* v___y_821_; lean_object* v___y_822_; lean_object* v___x_837_; lean_object* v___y_839_; 
v_id_814_ = lean_ctor_get(v_msg_724_, 0);
lean_inc(v_id_814_);
v_code_815_ = lean_ctor_get_uint8(v_msg_724_, sizeof(void*)*3);
v_message_816_ = lean_ctor_get(v_msg_724_, 1);
lean_inc_ref(v_message_816_);
v_data_x3f_817_ = lean_ctor_get(v_msg_724_, 2);
lean_inc(v_data_x3f_817_);
lean_dec_ref_known(v_msg_724_, 3);
v___x_837_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_814_))
{
case 0:
{
lean_object* v_s_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_s_855_ = lean_ctor_get(v_id_814_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v_id_814_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v_id_814_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_s_855_);
lean_dec(v_id_814_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
lean_ctor_set_tag(v___x_857_, 3);
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_s_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
v___y_839_ = v___x_860_;
goto v___jp_838_;
}
}
}
case 1:
{
lean_object* v_n_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
v_n_863_ = lean_ctor_get(v_id_814_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v_id_814_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v_id_814_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_n_863_);
lean_dec(v_id_814_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set_tag(v___x_865_, 2);
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_n_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
v___y_839_ = v___x_868_;
goto v___jp_838_;
}
}
}
default: 
{
lean_object* v___x_871_; 
v___x_871_ = lean_box(0);
v___y_839_ = v___x_871_;
goto v___jp_838_;
}
}
v___jp_818_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
lean_inc(v___y_822_);
lean_inc_ref(v___y_820_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___y_820_);
lean_ctor_set(v___x_823_, 1, v___y_822_);
v___x_824_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__8));
v___x_825_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_825_, 0, v_message_816_);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_823_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__9));
v___x_831_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(v___x_830_, v_data_x3f_817_);
lean_dec(v_data_x3f_817_);
v___x_832_ = l_List_appendTR___redArg(v___x_829_, v___x_831_);
v___x_833_ = l_Lean_Json_mkObj(v___x_832_);
lean_dec(v___x_832_);
lean_inc_ref(v___y_821_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___y_821_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v___x_827_);
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v___y_819_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___y_728_ = v___x_836_;
goto v___jp_727_;
}
v___jp_838_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_837_);
lean_ctor_set(v___x_840_, 1, v___y_839_);
v___x_841_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__10));
v___x_842_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__11));
switch(v_code_815_)
{
case 0:
{
lean_object* v___x_843_; 
v___x_843_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__15, &l_Lean_IO_FS_Stream_writeLspMessage___closed__15_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__15);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_843_;
goto v___jp_818_;
}
case 1:
{
lean_object* v___x_844_; 
v___x_844_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__19, &l_Lean_IO_FS_Stream_writeLspMessage___closed__19_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__19);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_844_;
goto v___jp_818_;
}
case 2:
{
lean_object* v___x_845_; 
v___x_845_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__23, &l_Lean_IO_FS_Stream_writeLspMessage___closed__23_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__23);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_845_;
goto v___jp_818_;
}
case 3:
{
lean_object* v___x_846_; 
v___x_846_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__27, &l_Lean_IO_FS_Stream_writeLspMessage___closed__27_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__27);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_846_;
goto v___jp_818_;
}
case 4:
{
lean_object* v___x_847_; 
v___x_847_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__31, &l_Lean_IO_FS_Stream_writeLspMessage___closed__31_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__31);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_847_;
goto v___jp_818_;
}
case 5:
{
lean_object* v___x_848_; 
v___x_848_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__35, &l_Lean_IO_FS_Stream_writeLspMessage___closed__35_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__35);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_848_;
goto v___jp_818_;
}
case 6:
{
lean_object* v___x_849_; 
v___x_849_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__39, &l_Lean_IO_FS_Stream_writeLspMessage___closed__39_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__39);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_849_;
goto v___jp_818_;
}
case 7:
{
lean_object* v___x_850_; 
v___x_850_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__43, &l_Lean_IO_FS_Stream_writeLspMessage___closed__43_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__43);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_850_;
goto v___jp_818_;
}
case 8:
{
lean_object* v___x_851_; 
v___x_851_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__47, &l_Lean_IO_FS_Stream_writeLspMessage___closed__47_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__47);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_851_;
goto v___jp_818_;
}
case 9:
{
lean_object* v___x_852_; 
v___x_852_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__51, &l_Lean_IO_FS_Stream_writeLspMessage___closed__51_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__51);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_852_;
goto v___jp_818_;
}
case 10:
{
lean_object* v___x_853_; 
v___x_853_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__55, &l_Lean_IO_FS_Stream_writeLspMessage___closed__55_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__55);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_853_;
goto v___jp_818_;
}
default: 
{
lean_object* v___x_854_; 
v___x_854_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__59, &l_Lean_IO_FS_Stream_writeLspMessage___closed__59_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__59);
v___y_819_ = v___x_840_;
v___y_820_ = v___x_842_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_854_;
goto v___jp_818_;
}
}
}
}
}
v___jp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_726_);
lean_ctor_set(v___x_729_, 1, v___y_728_);
v___x_730_ = l_Lean_Json_mkObj(v___x_729_);
lean_dec_ref_known(v___x_729_, 2);
v___x_731_ = l_Lean_Json_compress(v___x_730_);
v___x_732_ = l_Lean_IO_FS_Stream_writeSerializedLspMessage(v_h_723_, v___x_731_);
lean_dec_ref(v___x_731_);
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage___boxed(lean_object* v_h_872_, lean_object* v_msg_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_872_, v_msg_873_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg(lean_object* v_inst_876_, lean_object* v_h_877_, lean_object* v_r_878_){
_start:
{
lean_object* v_id_880_; lean_object* v_method_881_; lean_object* v_param_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_902_; 
v_id_880_ = lean_ctor_get(v_r_878_, 0);
v_method_881_ = lean_ctor_get(v_r_878_, 1);
v_param_882_ = lean_ctor_get(v_r_878_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v_r_878_);
if (v_isSharedCheck_902_ == 0)
{
v___x_884_ = v_r_878_;
v_isShared_885_ = v_isSharedCheck_902_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_param_882_);
lean_inc(v_method_881_);
lean_inc(v_id_880_);
lean_dec(v_r_878_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_902_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___y_887_; lean_object* v___x_892_; 
v___x_892_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_876_, v_param_882_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v___x_893_; 
lean_dec_ref_known(v___x_892_, 1);
v___x_893_ = lean_box(0);
v___y_887_ = v___x_893_;
goto v___jp_886_;
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
v_a_894_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_892_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_892_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
v___y_887_ = v___x_899_;
goto v___jp_886_;
}
}
}
v___jp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 2, v___y_887_);
v___x_889_ = v___x_884_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_id_880_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_method_881_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v___y_887_);
v___x_889_ = v_reuseFailAlloc_891_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_877_, v___x_889_);
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object* v_inst_903_, lean_object* v_h_904_, lean_object* v_r_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_903_, v_h_904_, v_r_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest(lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_h_910_, lean_object* v_r_911_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_909_, v_h_910_, v_r_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___boxed(lean_object* v_00_u03b1_914_, lean_object* v_inst_915_, lean_object* v_h_916_, lean_object* v_r_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_IO_FS_Stream_writeLspRequest(v_00_u03b1_914_, v_inst_915_, v_h_916_, v_r_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg(lean_object* v_inst_920_, lean_object* v_h_921_, lean_object* v_n_922_){
_start:
{
lean_object* v_method_924_; lean_object* v_param_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_945_; 
v_method_924_ = lean_ctor_get(v_n_922_, 0);
v_param_925_ = lean_ctor_get(v_n_922_, 1);
v_isSharedCheck_945_ = !lean_is_exclusive(v_n_922_);
if (v_isSharedCheck_945_ == 0)
{
v___x_927_ = v_n_922_;
v_isShared_928_ = v_isSharedCheck_945_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_param_925_);
lean_inc(v_method_924_);
lean_dec(v_n_922_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_945_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___y_930_; lean_object* v___x_935_; 
v___x_935_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_920_, v_param_925_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v___x_936_; 
lean_dec_ref_known(v___x_935_, 1);
v___x_936_ = lean_box(0);
v___y_930_ = v___x_936_;
goto v___jp_929_;
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
v_a_937_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_935_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_935_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
v___y_930_ = v___x_942_;
goto v___jp_929_;
}
}
}
v___jp_929_:
{
lean_object* v___x_932_; 
if (v_isShared_928_ == 0)
{
lean_ctor_set_tag(v___x_927_, 1);
lean_ctor_set(v___x_927_, 1, v___y_930_);
v___x_932_ = v___x_927_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_method_924_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v___y_930_);
v___x_932_ = v_reuseFailAlloc_934_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_921_, v___x_932_);
return v___x_933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object* v_inst_946_, lean_object* v_h_947_, lean_object* v_n_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_946_, v_h_947_, v_n_948_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification(lean_object* v_00_u03b1_951_, lean_object* v_inst_952_, lean_object* v_h_953_, lean_object* v_n_954_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_952_, v_h_953_, v_n_954_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___boxed(lean_object* v_00_u03b1_957_, lean_object* v_inst_958_, lean_object* v_h_959_, lean_object* v_n_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_IO_FS_Stream_writeLspNotification(v_00_u03b1_957_, v_inst_958_, v_h_959_, v_n_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg(lean_object* v_inst_963_, lean_object* v_h_964_, lean_object* v_r_965_){
_start:
{
lean_object* v_id_967_; lean_object* v_result_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_977_; 
v_id_967_ = lean_ctor_get(v_r_965_, 0);
v_result_968_ = lean_ctor_get(v_r_965_, 1);
v_isSharedCheck_977_ = !lean_is_exclusive(v_r_965_);
if (v_isSharedCheck_977_ == 0)
{
v___x_970_ = v_r_965_;
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_result_968_);
lean_inc(v_id_967_);
lean_dec(v_r_965_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_977_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_972_ = lean_apply_1(v_inst_963_, v_result_968_);
if (v_isShared_971_ == 0)
{
lean_ctor_set_tag(v___x_970_, 2);
lean_ctor_set(v___x_970_, 1, v___x_972_);
v___x_974_ = v___x_970_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_id_967_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v___x_972_);
v___x_974_ = v_reuseFailAlloc_976_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_964_, v___x_974_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object* v_inst_978_, lean_object* v_h_979_, lean_object* v_r_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_978_, v_h_979_, v_r_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse(lean_object* v_00_u03b1_983_, lean_object* v_inst_984_, lean_object* v_h_985_, lean_object* v_r_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_984_, v_h_985_, v_r_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___boxed(lean_object* v_00_u03b1_989_, lean_object* v_inst_990_, lean_object* v_h_991_, lean_object* v_r_992_, lean_object* v_a_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_IO_FS_Stream_writeLspResponse(v_00_u03b1_989_, v_inst_990_, v_h_991_, v_r_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError(lean_object* v_h_995_, lean_object* v_e_996_){
_start:
{
lean_object* v_id_998_; uint8_t v_code_999_; lean_object* v_message_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1009_; 
v_id_998_ = lean_ctor_get(v_e_996_, 0);
v_code_999_ = lean_ctor_get_uint8(v_e_996_, sizeof(void*)*3);
v_message_1000_ = lean_ctor_get(v_e_996_, 1);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_e_996_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v_e_996_, 2);
lean_dec(v_unused_1010_);
v___x_1002_ = v_e_996_;
v_isShared_1003_ = v_isSharedCheck_1009_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_message_1000_);
lean_inc(v_id_998_);
lean_dec(v_e_996_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1009_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_box(0);
if (v_isShared_1003_ == 0)
{
lean_ctor_set_tag(v___x_1002_, 3);
lean_ctor_set(v___x_1002_, 2, v___x_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_id_998_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_message_1000_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v___x_1004_);
lean_ctor_set_uint8(v_reuseFailAlloc_1008_, sizeof(void*)*3, v_code_999_);
v___x_1006_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_995_, v___x_1006_);
return v___x_1007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError___boxed(lean_object* v_h_1011_, lean_object* v_e_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_IO_FS_Stream_writeLspResponseError(v_h_1011_, v_e_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object* v_inst_1015_, lean_object* v_h_1016_, lean_object* v_e_1017_){
_start:
{
lean_object* v_id_1019_; uint8_t v_code_1020_; lean_object* v_message_1021_; lean_object* v_data_x3f_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1042_; 
v_id_1019_ = lean_ctor_get(v_e_1017_, 0);
v_code_1020_ = lean_ctor_get_uint8(v_e_1017_, sizeof(void*)*3);
v_message_1021_ = lean_ctor_get(v_e_1017_, 1);
v_data_x3f_1022_ = lean_ctor_get(v_e_1017_, 2);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_e_1017_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1024_ = v_e_1017_;
v_isShared_1025_ = v_isSharedCheck_1042_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_data_x3f_1022_);
lean_inc(v_message_1021_);
lean_inc(v_id_1019_);
lean_dec(v_e_1017_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1042_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___y_1027_; 
if (lean_obj_tag(v_data_x3f_1022_) == 0)
{
lean_object* v___x_1032_; 
lean_dec_ref(v_inst_1015_);
v___x_1032_ = lean_box(0);
v___y_1027_ = v___x_1032_;
goto v___jp_1026_;
}
else
{
lean_object* v_val_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1041_; 
v_val_1033_ = lean_ctor_get(v_data_x3f_1022_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_data_x3f_1022_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1035_ = v_data_x3f_1022_;
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_val_1033_);
lean_dec(v_data_x3f_1022_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1037_ = lean_apply_1(v_inst_1015_, v_val_1033_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v___x_1037_);
v___x_1039_ = v___x_1035_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
v___y_1027_ = v___x_1039_;
goto v___jp_1026_;
}
}
}
v___jp_1026_:
{
lean_object* v___x_1029_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set_tag(v___x_1024_, 3);
lean_ctor_set(v___x_1024_, 2, v___y_1027_);
v___x_1029_ = v___x_1024_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_id_1019_);
lean_ctor_set(v_reuseFailAlloc_1031_, 1, v_message_1021_);
lean_ctor_set(v_reuseFailAlloc_1031_, 2, v___y_1027_);
lean_ctor_set_uint8(v_reuseFailAlloc_1031_, sizeof(void*)*3, v_code_1020_);
v___x_1029_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_1016_, v___x_1029_);
return v___x_1030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object* v_inst_1043_, lean_object* v_h_1044_, lean_object* v_e_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1043_, v_h_1044_, v_e_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* v_00_u03b1_1048_, lean_object* v_inst_1049_, lean_object* v_h_1050_, lean_object* v_e_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1049_, v_h_1050_, v_e_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object* v_00_u03b1_1054_, lean_object* v_inst_1055_, lean_object* v_h_1056_, lean_object* v_e_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(v_00_u03b1_1054_, v_inst_1055_, v_h_1056_, v_e_1057_);
return v_res_1059_;
}
}
lean_object* runtime_initialize_Lean_Data_JsonRpc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Communication(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Communication(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Communication(builtin);
}
#ifdef __cplusplus
}
#endif

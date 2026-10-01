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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
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
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
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
static const lean_string_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1_value;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0_value;
static const lean_ctor_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1_value;
static const lean_array_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3_value;
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
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1));
v___x_7_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2);
v___x_10_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1));
v___x_11_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
lean_ctor_set(v___x_11_, 2, v___x_8_);
lean_ctor_set(v___x_11_, 3, v___x_8_);
return v___x_11_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg(){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___boxed(lean_object* v___dummy_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg();
return v_res_18_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg();
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(lean_object* v_s_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object* v_s_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(v_s_22_);
lean_dec_ref(v_s_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object* v_s_24_, lean_object* v___x_25_, lean_object* v___x_26_, lean_object* v_a_27_, lean_object* v_b_28_){
_start:
{
lean_object* v_it_30_; lean_object* v_startInclusive_31_; lean_object* v_endExclusive_32_; 
if (lean_obj_tag(v_a_27_) == 0)
{
lean_object* v_currPos_36_; lean_object* v_searcher_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_143_; 
v_currPos_36_ = lean_ctor_get(v_a_27_, 0);
v_searcher_37_ = lean_ctor_get(v_a_27_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_a_27_);
if (v_isSharedCheck_143_ == 0)
{
v___x_39_ = v_a_27_;
v_isShared_40_ = v_isSharedCheck_143_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_searcher_37_);
lean_inc(v_currPos_36_);
lean_dec(v_a_27_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_143_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v_it_42_; lean_object* v_it_48_; lean_object* v_startPos_49_; lean_object* v_endPos_50_; 
switch(lean_obj_tag(v_searcher_37_))
{
case 0:
{
lean_object* v_pos_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_75_; 
lean_del_object(v___x_39_);
v_pos_63_ = lean_ctor_get(v_searcher_37_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v_searcher_37_);
if (v_isSharedCheck_75_ == 0)
{
v___x_65_ = v_searcher_37_;
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_pos_63_);
lean_dec(v_searcher_37_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_75_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v_startInclusive_67_; lean_object* v_endExclusive_68_; lean_object* v___x_69_; uint8_t v_decide_70_; 
v_startInclusive_67_ = lean_ctor_get(v___x_25_, 1);
v_endExclusive_68_ = lean_ctor_get(v___x_25_, 2);
v___x_69_ = lean_nat_sub(v_endExclusive_68_, v_startInclusive_67_);
v_decide_70_ = lean_nat_dec_eq(v_pos_63_, v___x_69_);
lean_dec(v___x_69_);
if (v_decide_70_ == 0)
{
lean_object* v___x_72_; 
lean_inc(v_pos_63_);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 1);
v___x_72_ = v___x_65_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_pos_63_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_inc(v_pos_63_);
v_it_48_ = v___x_72_;
v_startPos_49_ = v_pos_63_;
v_endPos_50_ = v_pos_63_;
goto v___jp_47_;
}
}
else
{
lean_object* v___x_74_; 
lean_del_object(v___x_65_);
v___x_74_ = lean_box(3);
lean_inc(v_pos_63_);
v_it_48_ = v___x_74_;
v_startPos_49_ = v_pos_63_;
v_endPos_50_ = v_pos_63_;
goto v___jp_47_;
}
}
}
case 1:
{
lean_object* v_pos_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v_pos_76_ = lean_ctor_get(v_searcher_37_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v_searcher_37_);
if (v_isSharedCheck_84_ == 0)
{
v___x_78_ = v_searcher_37_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_pos_76_);
lean_dec(v_searcher_37_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_string_utf8_next_fast(v_s_24_, v_pos_76_);
lean_dec(v_pos_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 0);
lean_ctor_set(v___x_78_, 0, v___x_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
v_it_42_ = v___x_82_;
goto v___jp_41_;
}
}
}
case 2:
{
lean_object* v_needle_85_; lean_object* v_table_86_; lean_object* v_stackPos_87_; lean_object* v_needlePos_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_142_; 
v_needle_85_ = lean_ctor_get(v_searcher_37_, 0);
v_table_86_ = lean_ctor_get(v_searcher_37_, 1);
v_stackPos_87_ = lean_ctor_get(v_searcher_37_, 2);
v_needlePos_88_ = lean_ctor_get(v_searcher_37_, 3);
v_isSharedCheck_142_ = !lean_is_exclusive(v_searcher_37_);
if (v_isSharedCheck_142_ == 0)
{
v___x_90_ = v_searcher_37_;
v_isShared_91_ = v_isSharedCheck_142_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_needlePos_88_);
lean_inc(v_stackPos_87_);
lean_inc(v_table_86_);
lean_inc(v_needle_85_);
lean_dec(v_searcher_37_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_142_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v_str_92_; lean_object* v_startInclusive_93_; lean_object* v_endExclusive_94_; lean_object* v_basePos_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_str_92_ = lean_ctor_get(v_needle_85_, 0);
v_startInclusive_93_ = lean_ctor_get(v_needle_85_, 1);
v_endExclusive_94_ = lean_ctor_get(v_needle_85_, 2);
v_basePos_95_ = lean_nat_sub(v_stackPos_87_, v_needlePos_88_);
v___x_96_ = lean_nat_sub(v_endExclusive_94_, v_startInclusive_93_);
v___x_97_ = lean_nat_add(v_basePos_95_, v___x_96_);
v___x_98_ = lean_nat_dec_le(v___x_97_, v___x_26_);
lean_dec(v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
lean_dec(v___x_96_);
lean_del_object(v___x_90_);
lean_dec(v_needlePos_88_);
lean_dec(v_stackPos_87_);
lean_dec_ref(v_table_86_);
lean_dec_ref(v_needle_85_);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_basePos_95_, v___x_99_);
lean_dec(v_basePos_95_);
v___x_101_ = lean_nat_dec_le(v___x_100_, v___x_26_);
lean_dec(v___x_100_);
if (v___x_101_ == 0)
{
lean_del_object(v___x_39_);
goto v___jp_61_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(3);
v_it_42_ = v___x_102_;
goto v___jp_41_;
}
}
else
{
uint8_t v_stackByte_103_; lean_object* v___x_104_; uint8_t v_patByte_105_; uint8_t v___x_106_; 
lean_dec(v_basePos_95_);
lean_inc(v_stackPos_87_);
v_stackByte_103_ = lean_string_get_byte_fast(v_s_24_, v_stackPos_87_);
v___x_104_ = lean_nat_add(v_startInclusive_93_, v_needlePos_88_);
v_patByte_105_ = lean_string_get_byte_fast(v_str_92_, v___x_104_);
v___x_106_ = lean_uint8_dec_eq(v_stackByte_103_, v_patByte_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; uint8_t v_decide_108_; 
lean_dec(v___x_96_);
v___x_107_ = lean_unsigned_to_nat(0u);
v_decide_108_ = lean_nat_dec_eq(v_needlePos_88_, v___x_107_);
if (v_decide_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_newNeedlePos_111_; uint8_t v___x_112_; 
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_sub(v_needlePos_88_, v___x_109_);
lean_dec(v_needlePos_88_);
v_newNeedlePos_111_ = lean_array_fget_borrowed(v_table_86_, v___x_110_);
lean_dec(v___x_110_);
v___x_112_ = lean_nat_dec_eq(v_newNeedlePos_111_, v___x_107_);
if (v___x_112_ == 0)
{
lean_object* v___x_114_; 
lean_inc(v_newNeedlePos_111_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 3, v_newNeedlePos_111_);
v___x_114_ = v___x_90_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_needle_85_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_table_86_);
lean_ctor_set(v_reuseFailAlloc_115_, 2, v_stackPos_87_);
lean_ctor_set(v_reuseFailAlloc_115_, 3, v_newNeedlePos_111_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
v_it_42_ = v___x_114_;
goto v___jp_41_;
}
}
else
{
lean_object* v_nextStackPos_116_; lean_object* v___x_118_; 
v_nextStackPos_116_ = l_String_Slice_posGE___redArg(v___x_25_, v_stackPos_87_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 3, v___x_107_);
lean_ctor_set(v___x_90_, 2, v_nextStackPos_116_);
v___x_118_ = v___x_90_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_needle_85_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_table_86_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_nextStackPos_116_);
lean_ctor_set(v_reuseFailAlloc_119_, 3, v___x_107_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
v_it_42_ = v___x_118_;
goto v___jp_41_;
}
}
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v_nextStackPos_122_; lean_object* v___x_124_; 
lean_dec(v_needlePos_88_);
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_add(v_stackPos_87_, v___x_120_);
lean_dec(v_stackPos_87_);
v_nextStackPos_122_ = l_String_Slice_posGE___redArg(v___x_25_, v___x_121_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 3, v___x_107_);
lean_ctor_set(v___x_90_, 2, v_nextStackPos_122_);
v___x_124_ = v___x_90_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_needle_85_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_table_86_);
lean_ctor_set(v_reuseFailAlloc_125_, 2, v_nextStackPos_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 3, v___x_107_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
v_it_42_ = v___x_124_;
goto v___jp_41_;
}
}
}
else
{
lean_object* v___x_126_; lean_object* v_nextStackPos_127_; lean_object* v_nextNeedlePos_128_; uint8_t v_decide_129_; 
lean_del_object(v___x_39_);
v___x_126_ = lean_unsigned_to_nat(1u);
v_nextStackPos_127_ = lean_nat_add(v_stackPos_87_, v___x_126_);
lean_dec(v_stackPos_87_);
v_nextNeedlePos_128_ = lean_nat_add(v_needlePos_88_, v___x_126_);
lean_dec(v_needlePos_88_);
v_decide_129_ = lean_nat_dec_eq(v_nextNeedlePos_128_, v___x_96_);
lean_dec(v___x_96_);
if (v_decide_129_ == 0)
{
lean_object* v___x_131_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 3, v_nextNeedlePos_128_);
lean_ctor_set(v___x_90_, 2, v_nextStackPos_127_);
v___x_131_ = v___x_90_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_needle_85_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_table_86_);
lean_ctor_set(v_reuseFailAlloc_134_, 2, v_nextStackPos_127_);
lean_ctor_set(v_reuseFailAlloc_134_, 3, v_nextNeedlePos_128_);
v___x_131_ = v_reuseFailAlloc_134_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; 
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_currPos_36_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v_a_27_ = v___x_132_;
goto _start;
}
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_135_ = lean_nat_sub(v_nextStackPos_127_, v_nextNeedlePos_128_);
lean_dec(v_nextNeedlePos_128_);
v___x_136_ = l_String_Slice_pos_x21(v___x_25_, v___x_135_);
lean_dec(v___x_135_);
v___x_137_ = l_String_Slice_pos_x21(v___x_25_, v_nextStackPos_127_);
v___x_138_ = lean_unsigned_to_nat(0u);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 3, v___x_138_);
lean_ctor_set(v___x_90_, 2, v_nextStackPos_127_);
v___x_140_ = v___x_90_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_needle_85_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_table_86_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_nextStackPos_127_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
v_it_48_ = v___x_140_;
v_startPos_49_ = v___x_136_;
v_endPos_50_ = v___x_137_;
goto v___jp_47_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_39_);
goto v___jp_61_;
}
}
v___jp_41_:
{
lean_object* v___x_44_; 
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 1, v_it_42_);
v___x_44_ = v___x_39_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_currPos_36_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_it_42_);
v___x_44_ = v_reuseFailAlloc_46_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
v_a_27_ = v___x_44_;
goto _start;
}
}
v___jp_47_:
{
lean_object* v_slice_51_; lean_object* v_startInclusive_52_; lean_object* v_endExclusive_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
v_slice_51_ = l_String_Slice_subslice_x21(v___x_25_, v_currPos_36_, v_startPos_49_);
v_startInclusive_52_ = lean_ctor_get(v_slice_51_, 0);
v_endExclusive_53_ = lean_ctor_get(v_slice_51_, 1);
v_isSharedCheck_60_ = !lean_is_exclusive(v_slice_51_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v_slice_51_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_endExclusive_53_);
lean_inc(v_startInclusive_52_);
lean_dec(v_slice_51_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v_nextIt_58_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v_it_48_);
lean_ctor_set(v___x_55_, 0, v_endPos_50_);
v_nextIt_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_endPos_50_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v_it_48_);
v_nextIt_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
v_it_30_ = v_nextIt_58_;
v_startInclusive_31_ = v_startInclusive_52_;
v_endExclusive_32_ = v_endExclusive_53_;
goto v___jp_29_;
}
}
}
v___jp_61_:
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(1);
lean_inc(v___x_26_);
v_it_30_ = v___x_62_;
v_startInclusive_31_ = v_currPos_36_;
v_endExclusive_32_ = v___x_26_;
goto v___jp_29_;
}
}
}
else
{
lean_dec(v___x_26_);
lean_dec_ref(v_s_24_);
return v_b_28_;
}
v___jp_29_:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_inc_ref(v_s_24_);
v___x_33_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_33_, 0, v_s_24_);
lean_ctor_set(v___x_33_, 1, v_startInclusive_31_);
lean_ctor_set(v___x_33_, 2, v_endExclusive_32_);
v___x_34_ = lean_array_push(v_b_28_, v___x_33_);
v_a_27_ = v_it_30_;
v_b_28_ = v___x_34_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object* v_s_144_, lean_object* v___x_145_, lean_object* v___x_146_, lean_object* v_a_147_, lean_object* v_b_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_144_, v___x_145_, v___x_146_, v_a_147_, v_b_148_);
lean_dec_ref(v___x_145_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField(lean_object* v_s_158_){
_start:
{
uint8_t v___y_160_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3));
v___x_197_ = lean_string_dec_eq(v_s_158_, v___x_196_);
if (v___x_197_ == 0)
{
uint8_t v___x_198_; 
v___x_198_ = 1;
v___y_160_ = v___x_198_;
goto v___jp_159_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = 0;
v___y_160_ = v___x_199_;
goto v___jp_159_;
}
v___jp_159_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_string_utf8_byte_size(v_s_158_);
lean_inc_ref(v_s_158_);
v___x_163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_163_, 0, v_s_158_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_162_);
if (v___y_160_ == 0)
{
lean_object* v___x_164_; 
lean_dec_ref_known(v___x_163_, 3);
lean_dec_ref(v_s_158_);
v___x_164_ = lean_box(0);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_165_ = lean_unsigned_to_nat(2u);
v___x_166_ = l_String_Slice_Pos_prevn(v___x_163_, v___x_162_, v___x_165_);
lean_dec_ref_known(v___x_163_, 3);
lean_inc(v___x_166_);
lean_inc_ref(v_s_158_);
v___x_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_167_, 0, v_s_158_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
lean_ctor_set(v___x_167_, 2, v___x_162_);
v___x_168_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1));
v___x_169_ = l_String_Slice_beq(v___x_167_, v___x_168_);
lean_dec_ref_known(v___x_167_, 3);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_dec(v___x_166_);
lean_dec_ref(v_s_158_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
lean_inc(v___x_166_);
lean_inc_ref(v_s_158_);
v___x_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_171_, 0, v_s_158_);
lean_ctor_set(v___x_171_, 1, v___x_161_);
lean_ctor_set(v___x_171_, 2, v___x_166_);
v___x_172_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0);
v___x_173_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2));
v___x_174_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_158_, v___x_171_, v___x_166_, v___x_172_, v___x_173_);
lean_dec_ref_known(v___x_171_, 3);
v___x_175_ = lean_array_to_list(v___x_174_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v_tail_177_; 
v_tail_177_ = lean_ctor_get(v___x_175_, 1);
lean_inc(v_tail_177_);
if (lean_obj_tag(v_tail_177_) == 0)
{
lean_object* v___x_178_; 
lean_dec_ref_known(v___x_175_, 2);
v___x_178_ = lean_box(0);
return v___x_178_;
}
else
{
lean_object* v_head_179_; lean_object* v_str_180_; lean_object* v_startInclusive_181_; lean_object* v_endExclusive_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_193_; 
v_head_179_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_head_179_);
lean_dec_ref_known(v___x_175_, 2);
v_str_180_ = lean_ctor_get(v_head_179_, 0);
lean_inc_ref(v_str_180_);
v_startInclusive_181_ = lean_ctor_get(v_head_179_, 1);
lean_inc(v_startInclusive_181_);
v_endExclusive_182_ = lean_ctor_get(v_head_179_, 2);
lean_inc(v_endExclusive_182_);
lean_dec(v_head_179_);
v___x_183_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1));
v___x_184_ = l_String_Slice_intercalate(v___x_183_, v_tail_177_);
v_isSharedCheck_193_ = !lean_is_exclusive(v_tail_177_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; lean_object* v_unused_195_; 
v_unused_194_ = lean_ctor_get(v_tail_177_, 1);
lean_dec(v_unused_194_);
v_unused_195_ = lean_ctor_get(v_tail_177_, 0);
lean_dec(v_unused_195_);
v___x_186_ = v_tail_177_;
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
else
{
lean_dec(v_tail_177_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = lean_string_utf8_extract_fast(v_str_180_, v_startInclusive_181_, v_endExclusive_182_);
lean_dec(v_endExclusive_182_);
lean_dec(v_startInclusive_181_);
lean_dec_ref(v_str_180_);
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 0);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_184_);
v___x_190_ = v_reuseFailAlloc_192_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; 
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(lean_object* v_s_200_, lean_object* v___x_201_, lean_object* v___x_202_, lean_object* v_inst_203_, lean_object* v_R_204_, lean_object* v_a_205_, lean_object* v_b_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_200_, v___x_201_, v___x_202_, v_a_205_, v_b_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object* v_s_208_, lean_object* v___x_209_, lean_object* v___x_210_, lean_object* v_inst_211_, lean_object* v_R_212_, lean_object* v_a_213_, lean_object* v_b_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(v_s_208_, v___x_209_, v___x_210_, v_inst_211_, v_R_212_, v_a_213_, v_b_214_);
lean_dec_ref(v___x_209_);
return v_res_215_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(lean_object* v_s_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Json_parse(v_s_218_);
if (lean_obj_tag(v___x_219_) == 0)
{
uint8_t v___x_220_; 
lean_dec_ref_known(v___x_219_, 1);
v___x_220_ = 0;
return v___x_220_;
}
else
{
lean_object* v_a_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_a_221_ = lean_ctor_get(v___x_219_, 0);
lean_inc_n(v_a_221_, 2);
lean_dec_ref_known(v___x_219_, 1);
v___x_222_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__0));
v___x_223_ = l_Lean_Json_getObjVal_x3f(v_a_221_, v___x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
uint8_t v___x_224_; 
lean_dec_ref_known(v___x_223_, 1);
lean_dec(v_a_221_);
v___x_224_ = 0;
return v___x_224_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__1));
v___x_226_ = l_Lean_Json_getObjVal_x3f(v_a_221_, v___x_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
uint8_t v___x_227_; 
lean_dec_ref_known(v___x_226_, 1);
v___x_227_ = 0;
return v___x_227_;
}
else
{
uint8_t v___x_228_; 
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = 1;
return v___x_228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___boxed(lean_object* v_s_229_){
_start:
{
uint8_t v_res_230_; lean_object* v_r_231_; 
v_res_230_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_s_229_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__1));
v___x_235_ = lean_mk_io_user_error(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__3));
v___x_238_ = lean_mk_io_user_error(v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(lean_object* v_h_239_){
_start:
{
lean_object* v_getLine_241_; lean_object* v___x_242_; 
v_getLine_241_ = lean_ctor_get(v_h_239_, 3);
lean_inc_ref(v_getLine_241_);
v___x_242_ = lean_apply_1(v_getLine_241_, lean_box(0));
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_287_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_287_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_287_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_287_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = lean_string_utf8_byte_size(v_a_243_);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_nat_dec_eq(v___x_247_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0));
v___x_251_ = lean_string_dec_eq(v_a_243_, v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_inc(v_a_243_);
v___x_252_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField(v_a_243_);
if (lean_obj_tag(v___x_252_) == 0)
{
uint8_t v___x_253_; 
lean_dec_ref(v_h_239_);
lean_inc(v_a_243_);
v___x_253_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_a_243_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_254_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__0));
v___x_255_ = l_String_quote(v_a_243_);
v___x_256_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
v___x_257_ = l_Std_Format_defWidth;
v___x_258_ = l_Std_Format_pretty(v___x_256_, v___x_257_, v___x_248_, v___x_248_);
v___x_259_ = lean_string_append(v___x_254_, v___x_258_);
lean_dec_ref(v___x_258_);
v___x_260_ = lean_mk_io_user_error(v___x_259_);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 1);
lean_ctor_set(v___x_245_, 0, v___x_260_);
v___x_262_ = v___x_245_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_266_; 
lean_dec(v_a_243_);
v___x_264_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 1);
lean_ctor_set(v___x_245_, 0, v___x_264_);
v___x_266_ = v___x_245_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_object* v_val_268_; lean_object* v___x_269_; 
lean_del_object(v___x_245_);
lean_dec(v_a_243_);
v_val_268_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_val_268_);
lean_dec_ref_known(v___x_252_, 1);
v___x_269_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_239_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_278_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_278_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_278_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_274_, 0, v_val_268_);
lean_ctor_set(v___x_274_, 1, v_a_270_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_274_);
v___x_276_ = v___x_272_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
else
{
lean_dec(v_val_268_);
return v___x_269_;
}
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_281_; 
lean_dec(v_a_243_);
lean_dec_ref(v_h_239_);
v___x_279_ = lean_box(0);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_279_);
v___x_281_ = v___x_245_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_285_; 
lean_dec(v_a_243_);
lean_dec_ref(v_h_239_);
v___x_283_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4);
if (v_isShared_246_ == 0)
{
lean_ctor_set_tag(v___x_245_, 1);
lean_ctor_set(v___x_245_, 0, v___x_283_);
v___x_285_ = v___x_245_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec_ref(v_h_239_);
v_a_288_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_242_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_242_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___boxed(lean_object* v_h_296_, lean_object* v_a_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object* v_x_299_, lean_object* v_x_300_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_box(0);
return v___x_301_;
}
else
{
lean_object* v_head_302_; lean_object* v_tail_303_; lean_object* v_fst_304_; lean_object* v_snd_305_; uint8_t v___x_306_; 
v_head_302_ = lean_ctor_get(v_x_300_, 0);
v_tail_303_ = lean_ctor_get(v_x_300_, 1);
v_fst_304_ = lean_ctor_get(v_head_302_, 0);
v_snd_305_ = lean_ctor_get(v_head_302_, 1);
v___x_306_ = lean_string_dec_eq(v_x_299_, v_fst_304_);
if (v___x_306_ == 0)
{
v_x_300_ = v_tail_303_;
goto _start;
}
else
{
lean_object* v___x_308_; 
lean_inc(v_snd_305_);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v_snd_305_);
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_309_, v_x_310_);
lean_dec(v_x_310_);
lean_dec_ref(v_x_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
if (lean_obj_tag(v_x_316_) == 0)
{
return v_x_315_;
}
else
{
lean_object* v_head_317_; lean_object* v_tail_318_; lean_object* v_fst_319_; lean_object* v_snd_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_head_317_ = lean_ctor_get(v_x_316_, 0);
v_tail_318_ = lean_ctor_get(v_x_316_, 1);
v_fst_319_ = lean_ctor_get(v_head_317_, 0);
v_snd_320_ = lean_ctor_get(v_head_317_, 1);
v___x_321_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_322_ = lean_string_append(v_x_315_, v___x_321_);
v___x_323_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_324_ = lean_string_append(v___x_323_, v_fst_319_);
v___x_325_ = lean_string_append(v___x_324_, v___x_321_);
v___x_326_ = lean_string_append(v___x_325_, v_snd_320_);
v___x_327_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_328_ = lean_string_append(v___x_326_, v___x_327_);
v___x_329_ = lean_string_append(v___x_322_, v___x_328_);
lean_dec_ref(v___x_328_);
v_x_315_ = v___x_329_;
v_x_316_ = v_tail_318_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(v_x_331_, v_x_332_);
lean_dec(v_x_332_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(lean_object* v_x_337_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v___x_338_; 
v___x_338_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__0));
return v___x_338_;
}
else
{
lean_object* v_tail_339_; 
v_tail_339_ = lean_ctor_get(v_x_337_, 1);
if (lean_obj_tag(v_tail_339_) == 0)
{
lean_object* v_head_340_; lean_object* v_fst_341_; lean_object* v_snd_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_head_340_ = lean_ctor_get(v_x_337_, 0);
v_fst_341_ = lean_ctor_get(v_head_340_, 0);
v_snd_342_ = lean_ctor_get(v_head_340_, 1);
v___x_343_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_344_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_345_ = lean_string_append(v___x_344_, v_fst_341_);
v___x_346_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_347_ = lean_string_append(v___x_345_, v___x_346_);
v___x_348_ = lean_string_append(v___x_347_, v_snd_342_);
v___x_349_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_350_ = lean_string_append(v___x_348_, v___x_349_);
v___x_351_ = lean_string_append(v___x_343_, v___x_350_);
lean_dec_ref(v___x_350_);
v___x_352_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__2));
v___x_353_ = lean_string_append(v___x_351_, v___x_352_);
return v___x_353_;
}
else
{
lean_object* v_head_354_; lean_object* v_fst_355_; lean_object* v_snd_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint32_t v___x_367_; lean_object* v___x_368_; 
v_head_354_ = lean_ctor_get(v_x_337_, 0);
v_fst_355_ = lean_ctor_get(v_head_354_, 0);
v_snd_356_ = lean_ctor_get(v_head_354_, 1);
v___x_357_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_358_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_359_ = lean_string_append(v___x_358_, v_fst_355_);
v___x_360_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_361_ = lean_string_append(v___x_359_, v___x_360_);
v___x_362_ = lean_string_append(v___x_361_, v_snd_356_);
v___x_363_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_364_ = lean_string_append(v___x_362_, v___x_363_);
v___x_365_ = lean_string_append(v___x_357_, v___x_364_);
lean_dec_ref(v___x_364_);
v___x_366_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(v___x_365_, v_tail_339_);
v___x_367_ = 93;
v___x_368_ = lean_string_push(v___x_366_, v___x_367_);
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object* v_x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(v_x_369_);
lean_dec(v_x_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(lean_object* v_h_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_375_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_408_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_408_ == 0)
{
v___x_380_ = v___x_377_;
v_isShared_381_ = v_isSharedCheck_408_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_408_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__0));
v___x_383_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v___x_382_, v_a_378_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__1));
v___x_385_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(v_a_378_);
lean_dec(v_a_378_);
v___x_386_ = lean_string_append(v___x_384_, v___x_385_);
lean_dec_ref(v___x_385_);
v___x_387_ = lean_mk_io_user_error(v___x_386_);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 1);
lean_ctor_set(v___x_380_, 0, v___x_387_);
v___x_389_ = v___x_380_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
else
{
lean_object* v_val_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec(v_a_378_);
v_val_391_ = lean_ctor_get(v___x_383_, 0);
lean_inc_n(v_val_391_, 2);
lean_dec_ref_known(v___x_383_, 1);
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_string_utf8_byte_size(v_val_391_);
v___x_394_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_394_, 0, v_val_391_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set(v___x_394_, 2, v___x_393_);
v___x_395_ = l_String_Slice_toNat_x3f(v___x_394_);
lean_dec_ref_known(v___x_394_, 3);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_396_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__2));
v___x_397_ = lean_string_append(v___x_396_, v_val_391_);
lean_dec(v_val_391_);
v___x_398_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__3));
v___x_399_ = lean_string_append(v___x_397_, v___x_398_);
v___x_400_ = lean_mk_io_user_error(v___x_399_);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 1);
lean_ctor_set(v___x_380_, 0, v___x_400_);
v___x_402_ = v___x_380_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
else
{
lean_object* v_val_404_; lean_object* v___x_406_; 
lean_dec(v_val_391_);
v_val_404_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_404_);
lean_dec_ref_known(v___x_395_, 1);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v_val_404_);
v___x_406_ = v___x_380_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_val_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
v_a_409_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_377_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_377_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___boxed(lean_object* v_h_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0(lean_object* v_00_u03b2_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_421_, v_x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object* v_00_u03b2_424_, lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0(v_00_u03b2_424_, v_x_425_, v_x_426_);
lean_dec(v_x_426_);
lean_dec_ref(v_x_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage(lean_object* v_h_429_){
_start:
{
lean_object* v_a_432_; lean_object* v___x_438_; 
lean_inc_ref(v_h_429_);
v___x_438_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_429_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_440_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v___x_438_, 1);
v___x_440_ = l_Lean_IO_FS_Stream_readMessage(v_h_429_, v_a_439_);
lean_dec(v_a_439_);
if (lean_obj_tag(v___x_440_) == 0)
{
return v___x_440_;
}
else
{
lean_object* v_a_441_; 
v_a_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_a_441_);
lean_dec_ref_known(v___x_440_, 1);
v_a_432_ = v_a_441_;
goto v___jp_431_;
}
}
else
{
lean_object* v_a_442_; 
lean_dec_ref(v_h_429_);
v_a_442_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_438_, 1);
v_a_432_ = v_a_442_;
goto v___jp_431_;
}
v___jp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_433_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspMessage___closed__0));
v___x_434_ = lean_io_error_to_string(v_a_432_);
v___x_435_ = lean_string_append(v___x_433_, v___x_434_);
lean_dec_ref(v___x_434_);
v___x_436_ = lean_mk_io_user_error(v___x_435_);
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage___boxed(lean_object* v_h_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_IO_FS_Stream_readLspMessage(v_h_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString(lean_object* v_h_446_){
_start:
{
lean_object* v_a_449_; lean_object* v___x_455_; 
lean_inc_ref(v_h_446_);
v___x_455_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_446_);
if (lean_obj_tag(v___x_455_) == 0)
{
lean_object* v_a_456_; lean_object* v___x_457_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_455_, 1);
v___x_457_ = l_Lean_IO_FS_Stream_readUTF8(v_h_446_, v_a_456_);
lean_dec(v_a_456_);
if (lean_obj_tag(v___x_457_) == 0)
{
return v___x_457_;
}
else
{
lean_object* v_a_458_; 
v_a_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc(v_a_458_);
lean_dec_ref_known(v___x_457_, 1);
v_a_449_ = v_a_458_;
goto v___jp_448_;
}
}
else
{
lean_object* v_a_459_; 
lean_dec_ref(v_h_446_);
v_a_459_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_455_, 1);
v_a_449_ = v_a_459_;
goto v___jp_448_;
}
v___jp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_450_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspMessage___closed__0));
v___x_451_ = lean_io_error_to_string(v_a_449_);
v___x_452_ = lean_string_append(v___x_450_, v___x_451_);
lean_dec_ref(v___x_451_);
v___x_453_ = lean_mk_io_user_error(v___x_452_);
v___x_454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString___boxed(lean_object* v_h_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_IO_FS_Stream_readLspMessageAsString(v_h_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg(lean_object* v_h_464_, lean_object* v_expectedMethod_465_, lean_object* v_inst_466_){
_start:
{
lean_object* v_a_469_; lean_object* v___x_475_; 
lean_inc_ref(v_h_464_);
v___x_475_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_464_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v___x_477_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_464_, v_a_476_, v_expectedMethod_465_, v_inst_466_);
lean_dec(v_a_476_);
if (lean_obj_tag(v___x_477_) == 0)
{
return v___x_477_;
}
else
{
lean_object* v_a_478_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
v_a_469_ = v_a_478_;
goto v___jp_468_;
}
}
else
{
lean_object* v_a_479_; 
lean_dec_ref(v_inst_466_);
lean_dec_ref(v_expectedMethod_465_);
lean_dec_ref(v_h_464_);
v_a_479_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v___x_475_, 1);
v_a_469_ = v_a_479_;
goto v___jp_468_;
}
v___jp_468_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_470_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspRequestAs___redArg___closed__0));
v___x_471_ = lean_io_error_to_string(v_a_469_);
v___x_472_ = lean_string_append(v___x_470_, v___x_471_);
lean_dec_ref(v___x_471_);
v___x_473_ = lean_mk_io_user_error(v___x_472_);
v___x_474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object* v_h_480_, lean_object* v_expectedMethod_481_, lean_object* v_inst_482_, lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_480_, v_expectedMethod_481_, v_inst_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs(lean_object* v_h_485_, lean_object* v_expectedMethod_486_, lean_object* v_00_u03b1_487_, lean_object* v_inst_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_485_, v_expectedMethod_486_, v_inst_488_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___boxed(lean_object* v_h_491_, lean_object* v_expectedMethod_492_, lean_object* v_00_u03b1_493_, lean_object* v_inst_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_IO_FS_Stream_readLspRequestAs(v_h_491_, v_expectedMethod_492_, v_00_u03b1_493_, v_inst_494_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(lean_object* v_h_498_, lean_object* v_expectedMethod_499_, lean_object* v_inst_500_){
_start:
{
lean_object* v_a_503_; lean_object* v___x_509_; 
lean_inc_ref(v_h_498_);
v___x_509_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_498_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_498_, v_a_510_, v_expectedMethod_499_, v_inst_500_);
lean_dec(v_a_510_);
if (lean_obj_tag(v___x_511_) == 0)
{
return v___x_511_;
}
else
{
lean_object* v_a_512_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v_a_503_ = v_a_512_;
goto v___jp_502_;
}
}
else
{
lean_object* v_a_513_; 
lean_dec_ref(v_inst_500_);
lean_dec_ref(v_expectedMethod_499_);
lean_dec_ref(v_h_498_);
v_a_513_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_513_);
lean_dec_ref_known(v___x_509_, 1);
v_a_503_ = v_a_513_;
goto v___jp_502_;
}
v___jp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_504_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___closed__0));
v___x_505_ = lean_io_error_to_string(v_a_503_);
v___x_506_ = lean_string_append(v___x_504_, v___x_505_);
lean_dec_ref(v___x_505_);
v___x_507_ = lean_mk_io_user_error(v___x_506_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object* v_h_514_, lean_object* v_expectedMethod_515_, lean_object* v_inst_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_514_, v_expectedMethod_515_, v_inst_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs(lean_object* v_h_519_, lean_object* v_expectedMethod_520_, lean_object* v_00_u03b1_521_, lean_object* v_inst_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_519_, v_expectedMethod_520_, v_inst_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___boxed(lean_object* v_h_525_, lean_object* v_expectedMethod_526_, lean_object* v_00_u03b1_527_, lean_object* v_inst_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_IO_FS_Stream_readLspNotificationAs(v_h_525_, v_expectedMethod_526_, v_00_u03b1_527_, v_inst_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg(lean_object* v_h_532_, lean_object* v_expectedID_533_, lean_object* v_inst_534_){
_start:
{
lean_object* v_a_537_; lean_object* v___x_543_; 
lean_inc_ref(v_h_532_);
v___x_543_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_532_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
v___x_545_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_532_, v_a_544_, v_expectedID_533_, v_inst_534_);
lean_dec(v_a_544_);
if (lean_obj_tag(v___x_545_) == 0)
{
return v___x_545_;
}
else
{
lean_object* v_a_546_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
v_a_537_ = v_a_546_;
goto v___jp_536_;
}
}
else
{
lean_object* v_a_547_; 
lean_dec_ref(v_inst_534_);
lean_dec(v_expectedID_533_);
lean_dec_ref(v_h_532_);
v_a_547_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_543_, 1);
v_a_537_ = v_a_547_;
goto v___jp_536_;
}
v___jp_536_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_538_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspResponseAs___redArg___closed__0));
v___x_539_ = lean_io_error_to_string(v_a_537_);
v___x_540_ = lean_string_append(v___x_538_, v___x_539_);
lean_dec_ref(v___x_539_);
v___x_541_ = lean_mk_io_user_error(v___x_540_);
v___x_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object* v_h_548_, lean_object* v_expectedID_549_, lean_object* v_inst_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_548_, v_expectedID_549_, v_inst_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs(lean_object* v_h_553_, lean_object* v_expectedID_554_, lean_object* v_00_u03b1_555_, lean_object* v_inst_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_553_, v_expectedID_554_, v_inst_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___boxed(lean_object* v_h_559_, lean_object* v_expectedID_560_, lean_object* v_00_u03b1_561_, lean_object* v_inst_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_IO_FS_Stream_readLspResponseAs(v_h_559_, v_expectedID_560_, v_00_u03b1_561_, v_inst_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage(lean_object* v_h_567_, lean_object* v_msg_568_){
_start:
{
lean_object* v_flush_570_; lean_object* v_putStr_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_header_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_flush_570_ = lean_ctor_get(v_h_567_, 0);
lean_inc_ref(v_flush_570_);
v_putStr_571_ = lean_ctor_get(v_h_567_, 4);
lean_inc_ref(v_putStr_571_);
lean_dec_ref(v_h_567_);
v___x_572_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__0));
v___x_573_ = lean_string_utf8_byte_size(v_msg_568_);
v___x_574_ = l_Nat_reprFast(v___x_573_);
v___x_575_ = lean_string_append(v___x_572_, v___x_574_);
lean_dec_ref(v___x_574_);
v___x_576_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__1));
v_header_577_ = lean_string_append(v___x_575_, v___x_576_);
v___x_578_ = lean_string_append(v_header_577_, v_msg_568_);
v___x_579_ = lean_apply_2(v_putStr_571_, v___x_578_, lean_box(0));
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_580_; 
lean_dec_ref_known(v___x_579_, 1);
v___x_580_ = lean_apply_1(v_flush_570_, lean_box(0));
return v___x_580_;
}
else
{
lean_dec_ref(v_flush_570_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object* v_h_581_, lean_object* v_msg_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_IO_FS_Stream_writeSerializedLspMessage(v_h_581_, v_msg_582_);
lean_dec_ref(v_msg_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(lean_object* v_k_585_, lean_object* v_x_586_){
_start:
{
if (lean_obj_tag(v_x_586_) == 0)
{
lean_object* v___x_587_; 
lean_dec_ref(v_k_585_);
v___x_587_ = lean_box(0);
return v___x_587_;
}
else
{
lean_object* v_val_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_val_588_ = lean_ctor_get(v_x_586_, 0);
lean_inc(v_val_588_);
lean_dec_ref_known(v_x_586_, 1);
v___x_589_ = l_Lean_Json_Structured_toJson(v_val_588_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_k_585_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(lean_object* v_k_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v___x_595_; 
lean_dec_ref(v_k_593_);
v___x_595_ = lean_box(0);
return v___x_595_;
}
else
{
lean_object* v_val_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_val_596_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_val_596_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_k_593_);
lean_ctor_set(v___x_597_, 1, v_val_596_);
v___x_598_ = lean_box(0);
v___x_599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
return v___x_599_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1___boxed(lean_object* v_k_600_, lean_object* v_x_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(v_k_600_, v_x_601_);
lean_dec(v_x_601_);
return v_res_602_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__12(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_unsigned_to_nat(32700u);
v___x_619_ = lean_nat_to_int(v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__13(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__12, &l_Lean_IO_FS_Stream_writeLspMessage___closed__12_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__12);
v___x_621_ = lean_int_neg(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__14(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__13, &l_Lean_IO_FS_Stream_writeLspMessage___closed__13_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__13);
v___x_623_ = l_Lean_JsonNumber_fromInt(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__15(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__14, &l_Lean_IO_FS_Stream_writeLspMessage___closed__14_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__14);
v___x_625_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__16(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(32600u);
v___x_627_ = lean_nat_to_int(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__17(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__16, &l_Lean_IO_FS_Stream_writeLspMessage___closed__16_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__16);
v___x_629_ = lean_int_neg(v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__18(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__17, &l_Lean_IO_FS_Stream_writeLspMessage___closed__17_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__17);
v___x_631_ = l_Lean_JsonNumber_fromInt(v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__19(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__18, &l_Lean_IO_FS_Stream_writeLspMessage___closed__18_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__18);
v___x_633_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__20(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_unsigned_to_nat(32601u);
v___x_635_ = lean_nat_to_int(v___x_634_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__21(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__20, &l_Lean_IO_FS_Stream_writeLspMessage___closed__20_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__20);
v___x_637_ = lean_int_neg(v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__22(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__21, &l_Lean_IO_FS_Stream_writeLspMessage___closed__21_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__21);
v___x_639_ = l_Lean_JsonNumber_fromInt(v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__23(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__22, &l_Lean_IO_FS_Stream_writeLspMessage___closed__22_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__22);
v___x_641_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__24(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_unsigned_to_nat(32602u);
v___x_643_ = lean_nat_to_int(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__25(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__24, &l_Lean_IO_FS_Stream_writeLspMessage___closed__24_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__24);
v___x_645_ = lean_int_neg(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__26(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__25, &l_Lean_IO_FS_Stream_writeLspMessage___closed__25_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__25);
v___x_647_ = l_Lean_JsonNumber_fromInt(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__27(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__26, &l_Lean_IO_FS_Stream_writeLspMessage___closed__26_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__26);
v___x_649_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__28(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_unsigned_to_nat(32603u);
v___x_651_ = lean_nat_to_int(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__29(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__28, &l_Lean_IO_FS_Stream_writeLspMessage___closed__28_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__28);
v___x_653_ = lean_int_neg(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__30(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__29, &l_Lean_IO_FS_Stream_writeLspMessage___closed__29_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__29);
v___x_655_ = l_Lean_JsonNumber_fromInt(v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__31(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__30, &l_Lean_IO_FS_Stream_writeLspMessage___closed__30_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__30);
v___x_657_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__32(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_unsigned_to_nat(32002u);
v___x_659_ = lean_nat_to_int(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__33(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__32, &l_Lean_IO_FS_Stream_writeLspMessage___closed__32_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__32);
v___x_661_ = lean_int_neg(v___x_660_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__34(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__33, &l_Lean_IO_FS_Stream_writeLspMessage___closed__33_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__33);
v___x_663_ = l_Lean_JsonNumber_fromInt(v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__35(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__34, &l_Lean_IO_FS_Stream_writeLspMessage___closed__34_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__34);
v___x_665_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__36(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_unsigned_to_nat(32001u);
v___x_667_ = lean_nat_to_int(v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__37(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__36, &l_Lean_IO_FS_Stream_writeLspMessage___closed__36_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__36);
v___x_669_ = lean_int_neg(v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__38(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__37, &l_Lean_IO_FS_Stream_writeLspMessage___closed__37_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__37);
v___x_671_ = l_Lean_JsonNumber_fromInt(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__39(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__38, &l_Lean_IO_FS_Stream_writeLspMessage___closed__38_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__38);
v___x_673_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__40(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(32801u);
v___x_675_ = lean_nat_to_int(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__41(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__40, &l_Lean_IO_FS_Stream_writeLspMessage___closed__40_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__40);
v___x_677_ = lean_int_neg(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__42(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__41, &l_Lean_IO_FS_Stream_writeLspMessage___closed__41_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__41);
v___x_679_ = l_Lean_JsonNumber_fromInt(v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__43(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__42, &l_Lean_IO_FS_Stream_writeLspMessage___closed__42_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__42);
v___x_681_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__44(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_unsigned_to_nat(32800u);
v___x_683_ = lean_nat_to_int(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__45(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__44, &l_Lean_IO_FS_Stream_writeLspMessage___closed__44_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__44);
v___x_685_ = lean_int_neg(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__46(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__45, &l_Lean_IO_FS_Stream_writeLspMessage___closed__45_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__45);
v___x_687_ = l_Lean_JsonNumber_fromInt(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__47(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__46, &l_Lean_IO_FS_Stream_writeLspMessage___closed__46_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__46);
v___x_689_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__48(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_unsigned_to_nat(32900u);
v___x_691_ = lean_nat_to_int(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__49(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__48, &l_Lean_IO_FS_Stream_writeLspMessage___closed__48_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__48);
v___x_693_ = lean_int_neg(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__50(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__49, &l_Lean_IO_FS_Stream_writeLspMessage___closed__49_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__49);
v___x_695_ = l_Lean_JsonNumber_fromInt(v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__51(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__50, &l_Lean_IO_FS_Stream_writeLspMessage___closed__50_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__50);
v___x_697_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__52(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_unsigned_to_nat(32901u);
v___x_699_ = lean_nat_to_int(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__53(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__52, &l_Lean_IO_FS_Stream_writeLspMessage___closed__52_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__52);
v___x_701_ = lean_int_neg(v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__54(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__53, &l_Lean_IO_FS_Stream_writeLspMessage___closed__53_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__53);
v___x_703_ = l_Lean_JsonNumber_fromInt(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__55(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__54, &l_Lean_IO_FS_Stream_writeLspMessage___closed__54_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__54);
v___x_705_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__56(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_unsigned_to_nat(32902u);
v___x_707_ = lean_nat_to_int(v___x_706_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__57(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__56, &l_Lean_IO_FS_Stream_writeLspMessage___closed__56_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__56);
v___x_709_ = lean_int_neg(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__58(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__57, &l_Lean_IO_FS_Stream_writeLspMessage___closed__57_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__57);
v___x_711_ = l_Lean_JsonNumber_fromInt(v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__59(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__58, &l_Lean_IO_FS_Stream_writeLspMessage___closed__58_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__58);
v___x_713_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage(lean_object* v_h_714_, lean_object* v_msg_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___y_719_; 
v___x_717_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__3));
switch(lean_obj_tag(v_msg_715_))
{
case 0:
{
lean_object* v_id_724_; lean_object* v_method_725_; lean_object* v_params_x3f_726_; lean_object* v___x_727_; lean_object* v___y_729_; 
v_id_724_ = lean_ctor_get(v_msg_715_, 0);
lean_inc(v_id_724_);
v_method_725_ = lean_ctor_get(v_msg_715_, 1);
lean_inc_ref(v_method_725_);
v_params_x3f_726_ = lean_ctor_get(v_msg_715_, 2);
lean_inc(v_params_x3f_726_);
lean_dec_ref_known(v_msg_715_, 3);
v___x_727_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_724_))
{
case 0:
{
lean_object* v_s_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
v_s_740_ = lean_ctor_get(v_id_724_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v_id_724_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v_id_724_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_s_740_);
lean_dec(v_id_724_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 3);
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_s_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
v___y_729_ = v___x_745_;
goto v___jp_728_;
}
}
}
case 1:
{
lean_object* v_n_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
v_n_748_ = lean_ctor_get(v_id_724_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v_id_724_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v_id_724_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_n_748_);
lean_dec(v_id_724_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 2);
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_n_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
v___y_729_ = v___x_753_;
goto v___jp_728_;
}
}
}
default: 
{
lean_object* v___x_756_; 
v___x_756_ = lean_box(0);
v___y_729_ = v___x_756_;
goto v___jp_728_;
}
}
v___jp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_727_);
lean_ctor_set(v___x_730_, 1, v___y_729_);
v___x_731_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__5));
v___x_732_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_732_, 0, v_method_725_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = lean_box(0);
v___x_735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_730_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__6));
v___x_738_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(v___x_737_, v_params_x3f_726_);
v___x_739_ = l_List_appendTR___redArg(v___x_736_, v___x_738_);
v___y_719_ = v___x_739_;
goto v___jp_718_;
}
}
case 1:
{
lean_object* v_method_757_; lean_object* v_params_x3f_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_770_; 
v_method_757_ = lean_ctor_get(v_msg_715_, 0);
v_params_x3f_758_ = lean_ctor_get(v_msg_715_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_msg_715_);
if (v_isSharedCheck_770_ == 0)
{
v___x_760_ = v_msg_715_;
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_params_x3f_758_);
lean_inc(v_method_757_);
lean_dec(v_msg_715_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_770_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_762_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__5));
v___x_763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_763_, 0, v_method_757_);
if (v_isShared_761_ == 0)
{
lean_ctor_set_tag(v___x_760_, 0);
lean_ctor_set(v___x_760_, 1, v___x_763_);
lean_ctor_set(v___x_760_, 0, v___x_762_);
v___x_765_ = v___x_760_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_763_);
v___x_765_ = v_reuseFailAlloc_769_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__6));
v___x_767_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(v___x_766_, v_params_x3f_758_);
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_765_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v___y_719_ = v___x_768_;
goto v___jp_718_;
}
}
}
case 2:
{
lean_object* v_id_771_; lean_object* v_result_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_804_; 
v_id_771_ = lean_ctor_get(v_msg_715_, 0);
v_result_772_ = lean_ctor_get(v_msg_715_, 1);
v_isSharedCheck_804_ = !lean_is_exclusive(v_msg_715_);
if (v_isSharedCheck_804_ == 0)
{
v___x_774_ = v_msg_715_;
v_isShared_775_ = v_isSharedCheck_804_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_result_772_);
lean_inc(v_id_771_);
lean_dec(v_msg_715_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_804_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___y_778_; 
v___x_776_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_771_))
{
case 0:
{
lean_object* v_s_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_s_787_ = lean_ctor_get(v_id_771_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_id_771_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v_id_771_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_s_787_);
lean_dec(v_id_771_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set_tag(v___x_789_, 3);
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_s_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v___y_778_ = v___x_792_;
goto v___jp_777_;
}
}
}
case 1:
{
lean_object* v_n_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
v_n_795_ = lean_ctor_get(v_id_771_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v_id_771_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v_id_771_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_n_795_);
lean_dec(v_id_771_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set_tag(v___x_797_, 2);
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_n_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v___y_778_ = v___x_800_;
goto v___jp_777_;
}
}
}
default: 
{
lean_object* v___x_803_; 
v___x_803_ = lean_box(0);
v___y_778_ = v___x_803_;
goto v___jp_777_;
}
}
v___jp_777_:
{
lean_object* v___x_780_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 0);
lean_ctor_set(v___x_774_, 1, v___y_778_);
lean_ctor_set(v___x_774_, 0, v___x_776_);
v___x_780_ = v___x_774_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___y_778_);
v___x_780_ = v_reuseFailAlloc_786_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_781_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__7));
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_result_772_);
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_780_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___y_719_ = v___x_785_;
goto v___jp_718_;
}
}
}
}
default: 
{
lean_object* v_id_805_; uint8_t v_code_806_; lean_object* v_message_807_; lean_object* v_data_x3f_808_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___x_828_; lean_object* v___y_830_; 
v_id_805_ = lean_ctor_get(v_msg_715_, 0);
lean_inc(v_id_805_);
v_code_806_ = lean_ctor_get_uint8(v_msg_715_, sizeof(void*)*3);
v_message_807_ = lean_ctor_get(v_msg_715_, 1);
lean_inc_ref(v_message_807_);
v_data_x3f_808_ = lean_ctor_get(v_msg_715_, 2);
lean_inc(v_data_x3f_808_);
lean_dec_ref_known(v_msg_715_, 3);
v___x_828_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_805_))
{
case 0:
{
lean_object* v_s_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_s_846_ = lean_ctor_get(v_id_805_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v_id_805_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v_id_805_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_s_846_);
lean_dec(v_id_805_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set_tag(v___x_848_, 3);
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_s_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
v___y_830_ = v___x_851_;
goto v___jp_829_;
}
}
}
case 1:
{
lean_object* v_n_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v_n_854_ = lean_ctor_get(v_id_805_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v_id_805_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v_id_805_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_n_854_);
lean_dec(v_id_805_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 2);
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_n_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
v___y_830_ = v___x_859_;
goto v___jp_829_;
}
}
}
default: 
{
lean_object* v___x_862_; 
v___x_862_ = lean_box(0);
v___y_830_ = v___x_862_;
goto v___jp_829_;
}
}
v___jp_809_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
lean_inc(v___y_813_);
lean_inc_ref(v___y_810_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___y_810_);
lean_ctor_set(v___x_814_, 1, v___y_813_);
v___x_815_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__8));
v___x_816_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_816_, 0, v_message_807_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = lean_box(0);
v___x_819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_814_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__9));
v___x_822_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(v___x_821_, v_data_x3f_808_);
lean_dec(v_data_x3f_808_);
v___x_823_ = l_List_appendTR___redArg(v___x_820_, v___x_822_);
v___x_824_ = l_Lean_Json_mkObj(v___x_823_);
lean_dec(v___x_823_);
lean_inc_ref(v___y_812_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v___y_812_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v___x_818_);
v___x_827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_827_, 0, v___y_811_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___y_719_ = v___x_827_;
goto v___jp_718_;
}
v___jp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_828_);
lean_ctor_set(v___x_831_, 1, v___y_830_);
v___x_832_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__10));
v___x_833_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__11));
switch(v_code_806_)
{
case 0:
{
lean_object* v___x_834_; 
v___x_834_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__15, &l_Lean_IO_FS_Stream_writeLspMessage___closed__15_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__15);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_834_;
goto v___jp_809_;
}
case 1:
{
lean_object* v___x_835_; 
v___x_835_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__19, &l_Lean_IO_FS_Stream_writeLspMessage___closed__19_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__19);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_835_;
goto v___jp_809_;
}
case 2:
{
lean_object* v___x_836_; 
v___x_836_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__23, &l_Lean_IO_FS_Stream_writeLspMessage___closed__23_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__23);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_836_;
goto v___jp_809_;
}
case 3:
{
lean_object* v___x_837_; 
v___x_837_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__27, &l_Lean_IO_FS_Stream_writeLspMessage___closed__27_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__27);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_837_;
goto v___jp_809_;
}
case 4:
{
lean_object* v___x_838_; 
v___x_838_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__31, &l_Lean_IO_FS_Stream_writeLspMessage___closed__31_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__31);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_838_;
goto v___jp_809_;
}
case 5:
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__35, &l_Lean_IO_FS_Stream_writeLspMessage___closed__35_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__35);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_839_;
goto v___jp_809_;
}
case 6:
{
lean_object* v___x_840_; 
v___x_840_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__39, &l_Lean_IO_FS_Stream_writeLspMessage___closed__39_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__39);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_840_;
goto v___jp_809_;
}
case 7:
{
lean_object* v___x_841_; 
v___x_841_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__43, &l_Lean_IO_FS_Stream_writeLspMessage___closed__43_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__43);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_841_;
goto v___jp_809_;
}
case 8:
{
lean_object* v___x_842_; 
v___x_842_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__47, &l_Lean_IO_FS_Stream_writeLspMessage___closed__47_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__47);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_842_;
goto v___jp_809_;
}
case 9:
{
lean_object* v___x_843_; 
v___x_843_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__51, &l_Lean_IO_FS_Stream_writeLspMessage___closed__51_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__51);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_843_;
goto v___jp_809_;
}
case 10:
{
lean_object* v___x_844_; 
v___x_844_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__55, &l_Lean_IO_FS_Stream_writeLspMessage___closed__55_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__55);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_844_;
goto v___jp_809_;
}
default: 
{
lean_object* v___x_845_; 
v___x_845_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__59, &l_Lean_IO_FS_Stream_writeLspMessage___closed__59_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__59);
v___y_810_ = v___x_833_;
v___y_811_ = v___x_831_;
v___y_812_ = v___x_832_;
v___y_813_ = v___x_845_;
goto v___jp_809_;
}
}
}
}
}
v___jp_718_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_717_);
lean_ctor_set(v___x_720_, 1, v___y_719_);
v___x_721_ = l_Lean_Json_mkObj(v___x_720_);
lean_dec_ref_known(v___x_720_, 2);
v___x_722_ = l_Lean_Json_compress(v___x_721_);
v___x_723_ = l_Lean_IO_FS_Stream_writeSerializedLspMessage(v_h_714_, v___x_722_);
lean_dec_ref(v___x_722_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage___boxed(lean_object* v_h_863_, lean_object* v_msg_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_863_, v_msg_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg(lean_object* v_inst_867_, lean_object* v_h_868_, lean_object* v_r_869_){
_start:
{
lean_object* v_id_871_; lean_object* v_method_872_; lean_object* v_param_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_893_; 
v_id_871_ = lean_ctor_get(v_r_869_, 0);
v_method_872_ = lean_ctor_get(v_r_869_, 1);
v_param_873_ = lean_ctor_get(v_r_869_, 2);
v_isSharedCheck_893_ = !lean_is_exclusive(v_r_869_);
if (v_isSharedCheck_893_ == 0)
{
v___x_875_ = v_r_869_;
v_isShared_876_ = v_isSharedCheck_893_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_param_873_);
lean_inc(v_method_872_);
lean_inc(v_id_871_);
lean_dec(v_r_869_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_893_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___y_878_; lean_object* v___x_883_; 
v___x_883_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_867_, v_param_873_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_884_; 
lean_dec_ref_known(v___x_883_, 1);
v___x_884_ = lean_box(0);
v___y_878_ = v___x_884_;
goto v___jp_877_;
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_885_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_883_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
v___y_878_ = v___x_890_;
goto v___jp_877_;
}
}
}
v___jp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 2, v___y_878_);
v___x_880_ = v___x_875_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_id_871_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_method_872_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v___y_878_);
v___x_880_ = v_reuseFailAlloc_882_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_868_, v___x_880_);
return v___x_881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object* v_inst_894_, lean_object* v_h_895_, lean_object* v_r_896_, lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_894_, v_h_895_, v_r_896_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest(lean_object* v_00_u03b1_899_, lean_object* v_inst_900_, lean_object* v_h_901_, lean_object* v_r_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_900_, v_h_901_, v_r_902_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___boxed(lean_object* v_00_u03b1_905_, lean_object* v_inst_906_, lean_object* v_h_907_, lean_object* v_r_908_, lean_object* v_a_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_IO_FS_Stream_writeLspRequest(v_00_u03b1_905_, v_inst_906_, v_h_907_, v_r_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg(lean_object* v_inst_911_, lean_object* v_h_912_, lean_object* v_n_913_){
_start:
{
lean_object* v_method_915_; lean_object* v_param_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_936_; 
v_method_915_ = lean_ctor_get(v_n_913_, 0);
v_param_916_ = lean_ctor_get(v_n_913_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_n_913_);
if (v_isSharedCheck_936_ == 0)
{
v___x_918_ = v_n_913_;
v_isShared_919_ = v_isSharedCheck_936_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_param_916_);
lean_inc(v_method_915_);
lean_dec(v_n_913_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_936_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___y_921_; lean_object* v___x_926_; 
v___x_926_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_911_, v_param_916_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_927_; 
lean_dec_ref_known(v___x_926_, 1);
v___x_927_ = lean_box(0);
v___y_921_ = v___x_927_;
goto v___jp_920_;
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
v_a_928_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_926_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_926_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
v___y_921_ = v___x_933_;
goto v___jp_920_;
}
}
}
v___jp_920_:
{
lean_object* v___x_923_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set_tag(v___x_918_, 1);
lean_ctor_set(v___x_918_, 1, v___y_921_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_method_915_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___y_921_);
v___x_923_ = v_reuseFailAlloc_925_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_912_, v___x_923_);
return v___x_924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object* v_inst_937_, lean_object* v_h_938_, lean_object* v_n_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_937_, v_h_938_, v_n_939_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification(lean_object* v_00_u03b1_942_, lean_object* v_inst_943_, lean_object* v_h_944_, lean_object* v_n_945_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_943_, v_h_944_, v_n_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___boxed(lean_object* v_00_u03b1_948_, lean_object* v_inst_949_, lean_object* v_h_950_, lean_object* v_n_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_IO_FS_Stream_writeLspNotification(v_00_u03b1_948_, v_inst_949_, v_h_950_, v_n_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg(lean_object* v_inst_954_, lean_object* v_h_955_, lean_object* v_r_956_){
_start:
{
lean_object* v_id_958_; lean_object* v_result_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_968_; 
v_id_958_ = lean_ctor_get(v_r_956_, 0);
v_result_959_ = lean_ctor_get(v_r_956_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_r_956_);
if (v_isSharedCheck_968_ == 0)
{
v___x_961_ = v_r_956_;
v_isShared_962_ = v_isSharedCheck_968_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_result_959_);
lean_inc(v_id_958_);
lean_dec(v_r_956_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_968_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; lean_object* v___x_965_; 
v___x_963_ = lean_apply_1(v_inst_954_, v_result_959_);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 2);
lean_ctor_set(v___x_961_, 1, v___x_963_);
v___x_965_ = v___x_961_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_id_958_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_963_);
v___x_965_ = v_reuseFailAlloc_967_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_955_, v___x_965_);
return v___x_966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object* v_inst_969_, lean_object* v_h_970_, lean_object* v_r_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_969_, v_h_970_, v_r_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse(lean_object* v_00_u03b1_974_, lean_object* v_inst_975_, lean_object* v_h_976_, lean_object* v_r_977_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_975_, v_h_976_, v_r_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___boxed(lean_object* v_00_u03b1_980_, lean_object* v_inst_981_, lean_object* v_h_982_, lean_object* v_r_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_IO_FS_Stream_writeLspResponse(v_00_u03b1_980_, v_inst_981_, v_h_982_, v_r_983_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError(lean_object* v_h_986_, lean_object* v_e_987_){
_start:
{
lean_object* v_id_989_; uint8_t v_code_990_; lean_object* v_message_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1000_; 
v_id_989_ = lean_ctor_get(v_e_987_, 0);
v_code_990_ = lean_ctor_get_uint8(v_e_987_, sizeof(void*)*3);
v_message_991_ = lean_ctor_get(v_e_987_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_e_987_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v_e_987_, 2);
lean_dec(v_unused_1001_);
v___x_993_ = v_e_987_;
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_message_991_);
lean_inc(v_id_989_);
lean_dec(v_e_987_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
if (v_isShared_994_ == 0)
{
lean_ctor_set_tag(v___x_993_, 3);
lean_ctor_set(v___x_993_, 2, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_id_989_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_message_991_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v___x_995_);
lean_ctor_set_uint8(v_reuseFailAlloc_999_, sizeof(void*)*3, v_code_990_);
v___x_997_ = v_reuseFailAlloc_999_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_986_, v___x_997_);
return v___x_998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError___boxed(lean_object* v_h_1002_, lean_object* v_e_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_IO_FS_Stream_writeLspResponseError(v_h_1002_, v_e_1003_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object* v_inst_1006_, lean_object* v_h_1007_, lean_object* v_e_1008_){
_start:
{
lean_object* v_id_1010_; uint8_t v_code_1011_; lean_object* v_message_1012_; lean_object* v_data_x3f_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1033_; 
v_id_1010_ = lean_ctor_get(v_e_1008_, 0);
v_code_1011_ = lean_ctor_get_uint8(v_e_1008_, sizeof(void*)*3);
v_message_1012_ = lean_ctor_get(v_e_1008_, 1);
v_data_x3f_1013_ = lean_ctor_get(v_e_1008_, 2);
v_isSharedCheck_1033_ = !lean_is_exclusive(v_e_1008_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1015_ = v_e_1008_;
v_isShared_1016_ = v_isSharedCheck_1033_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_data_x3f_1013_);
lean_inc(v_message_1012_);
lean_inc(v_id_1010_);
lean_dec(v_e_1008_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1033_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___y_1018_; 
if (lean_obj_tag(v_data_x3f_1013_) == 0)
{
lean_object* v___x_1023_; 
lean_dec_ref(v_inst_1006_);
v___x_1023_ = lean_box(0);
v___y_1018_ = v___x_1023_;
goto v___jp_1017_;
}
else
{
lean_object* v_val_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1032_; 
v_val_1024_ = lean_ctor_get(v_data_x3f_1013_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_data_x3f_1013_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1026_ = v_data_x3f_1013_;
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_val_1024_);
lean_dec(v_data_x3f_1013_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1032_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_apply_1(v_inst_1006_, v_val_1024_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1028_);
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
v___y_1018_ = v___x_1030_;
goto v___jp_1017_;
}
}
}
v___jp_1017_:
{
lean_object* v___x_1020_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set_tag(v___x_1015_, 3);
lean_ctor_set(v___x_1015_, 2, v___y_1018_);
v___x_1020_ = v___x_1015_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_id_1010_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_message_1012_);
lean_ctor_set(v_reuseFailAlloc_1022_, 2, v___y_1018_);
lean_ctor_set_uint8(v_reuseFailAlloc_1022_, sizeof(void*)*3, v_code_1011_);
v___x_1020_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_1007_, v___x_1020_);
return v___x_1021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object* v_inst_1034_, lean_object* v_h_1035_, lean_object* v_e_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1034_, v_h_1035_, v_e_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* v_00_u03b1_1039_, lean_object* v_inst_1040_, lean_object* v_h_1041_, lean_object* v_e_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1040_, v_h_1041_, v_e_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object* v_00_u03b1_1045_, lean_object* v_inst_1046_, lean_object* v_h_1047_, lean_object* v_e_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(v_00_u03b1_1045_, v_inst_1046_, v_h_1047_, v_e_1048_);
return v_res_1050_;
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

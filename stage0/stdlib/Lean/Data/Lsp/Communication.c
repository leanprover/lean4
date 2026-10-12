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
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1_value;
static const lean_ctor_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2_value;
static const lean_array_object l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
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
lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg(){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4);
return v___x_16_;
}
}
LEAN_EXPORT void l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_17_;
v_res_17_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg();
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___boxed(lean_object* v___dummy_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg();
return v_res_19_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0(void){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg();
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(lean_object* v_s_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object* v_s_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(v_s_23_);
lean_dec_ref(v_s_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object* v_s_25_, lean_object* v___x_26_, lean_object* v___x_27_, lean_object* v_a_28_, lean_object* v_b_29_){
_start:
{
lean_object* v_it_31_; lean_object* v_startInclusive_32_; lean_object* v_endExclusive_33_; 
if (lean_obj_tag(v_a_28_) == 0)
{
lean_object* v_currPos_37_; lean_object* v_searcher_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_144_; 
v_currPos_37_ = lean_ctor_get(v_a_28_, 0);
v_searcher_38_ = lean_ctor_get(v_a_28_, 1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_a_28_);
if (v_isSharedCheck_144_ == 0)
{
v___x_40_ = v_a_28_;
v_isShared_41_ = v_isSharedCheck_144_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_searcher_38_);
lean_inc(v_currPos_37_);
lean_dec(v_a_28_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_144_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v_it_43_; lean_object* v_it_49_; lean_object* v_startPos_50_; lean_object* v_endPos_51_; 
switch(lean_obj_tag(v_searcher_38_))
{
case 0:
{
lean_object* v_pos_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_76_; 
lean_del_object(v___x_40_);
v_pos_64_ = lean_ctor_get(v_searcher_38_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v_searcher_38_);
if (v_isSharedCheck_76_ == 0)
{
v___x_66_ = v_searcher_38_;
v_isShared_67_ = v_isSharedCheck_76_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_pos_64_);
lean_dec(v_searcher_38_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_76_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v_startInclusive_68_; lean_object* v_endExclusive_69_; lean_object* v___x_70_; uint8_t v_decide_71_; 
v_startInclusive_68_ = lean_ctor_get(v___x_26_, 1);
v_endExclusive_69_ = lean_ctor_get(v___x_26_, 2);
v___x_70_ = lean_nat_sub(v_endExclusive_69_, v_startInclusive_68_);
v_decide_71_ = lean_nat_dec_eq(v_pos_64_, v___x_70_);
lean_dec(v___x_70_);
if (v_decide_71_ == 0)
{
lean_object* v___x_73_; 
lean_inc(v_pos_64_);
if (v_isShared_67_ == 0)
{
lean_ctor_set_tag(v___x_66_, 1);
v___x_73_ = v___x_66_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_pos_64_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_inc(v_pos_64_);
v_it_49_ = v___x_73_;
v_startPos_50_ = v_pos_64_;
v_endPos_51_ = v_pos_64_;
goto v___jp_48_;
}
}
else
{
lean_object* v___x_75_; 
lean_del_object(v___x_66_);
v___x_75_ = lean_box(3);
lean_inc(v_pos_64_);
v_it_49_ = v___x_75_;
v_startPos_50_ = v_pos_64_;
v_endPos_51_ = v_pos_64_;
goto v___jp_48_;
}
}
}
case 1:
{
lean_object* v_pos_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_85_; 
v_pos_77_ = lean_ctor_get(v_searcher_38_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v_searcher_38_);
if (v_isSharedCheck_85_ == 0)
{
v___x_79_ = v_searcher_38_;
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_pos_77_);
lean_dec(v_searcher_38_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_85_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_83_; 
v___x_81_ = lean_string_utf8_next_fast(v_s_25_, v_pos_77_);
lean_dec(v_pos_77_);
if (v_isShared_80_ == 0)
{
lean_ctor_set_tag(v___x_79_, 0);
lean_ctor_set(v___x_79_, 0, v___x_81_);
v___x_83_ = v___x_79_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
v_it_43_ = v___x_83_;
goto v___jp_42_;
}
}
}
case 2:
{
lean_object* v_needle_86_; lean_object* v_table_87_; lean_object* v_stackPos_88_; lean_object* v_needlePos_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_143_; 
v_needle_86_ = lean_ctor_get(v_searcher_38_, 0);
v_table_87_ = lean_ctor_get(v_searcher_38_, 1);
v_stackPos_88_ = lean_ctor_get(v_searcher_38_, 2);
v_needlePos_89_ = lean_ctor_get(v_searcher_38_, 3);
v_isSharedCheck_143_ = !lean_is_exclusive(v_searcher_38_);
if (v_isSharedCheck_143_ == 0)
{
v___x_91_ = v_searcher_38_;
v_isShared_92_ = v_isSharedCheck_143_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_needlePos_89_);
lean_inc(v_stackPos_88_);
lean_inc(v_table_87_);
lean_inc(v_needle_86_);
lean_dec(v_searcher_38_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_143_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v_str_93_; lean_object* v_startInclusive_94_; lean_object* v_endExclusive_95_; lean_object* v_basePos_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_str_93_ = lean_ctor_get(v_needle_86_, 0);
v_startInclusive_94_ = lean_ctor_get(v_needle_86_, 1);
v_endExclusive_95_ = lean_ctor_get(v_needle_86_, 2);
v_basePos_96_ = lean_nat_sub(v_stackPos_88_, v_needlePos_89_);
v___x_97_ = lean_nat_sub(v_endExclusive_95_, v_startInclusive_94_);
v___x_98_ = lean_nat_add(v_basePos_96_, v___x_97_);
v___x_99_ = lean_nat_dec_le(v___x_98_, v___x_27_);
lean_dec(v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
lean_dec(v___x_97_);
lean_del_object(v___x_91_);
lean_dec(v_needlePos_89_);
lean_dec(v_stackPos_88_);
lean_dec_ref(v_table_87_);
lean_dec_ref(v_needle_86_);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_add(v_basePos_96_, v___x_100_);
lean_dec(v_basePos_96_);
v___x_102_ = lean_nat_dec_le(v___x_101_, v___x_27_);
lean_dec(v___x_101_);
if (v___x_102_ == 0)
{
lean_del_object(v___x_40_);
goto v___jp_62_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_box(3);
v_it_43_ = v___x_103_;
goto v___jp_42_;
}
}
else
{
uint8_t v_stackByte_104_; lean_object* v___x_105_; uint8_t v_patByte_106_; uint8_t v___x_107_; 
lean_dec(v_basePos_96_);
lean_inc(v_stackPos_88_);
v_stackByte_104_ = lean_string_get_byte_fast(v_s_25_, v_stackPos_88_);
v___x_105_ = lean_nat_add(v_startInclusive_94_, v_needlePos_89_);
v_patByte_106_ = lean_string_get_byte_fast(v_str_93_, v___x_105_);
v___x_107_ = lean_uint8_dec_eq(v_stackByte_104_, v_patByte_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; uint8_t v_decide_109_; 
lean_dec(v___x_97_);
v___x_108_ = lean_unsigned_to_nat(0u);
v_decide_109_ = lean_nat_dec_eq(v_needlePos_89_, v___x_108_);
if (v_decide_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v_newNeedlePos_112_; uint8_t v___x_113_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_sub(v_needlePos_89_, v___x_110_);
lean_dec(v_needlePos_89_);
v_newNeedlePos_112_ = lean_array_fget_borrowed(v_table_87_, v___x_111_);
lean_dec(v___x_111_);
v___x_113_ = lean_nat_dec_eq(v_newNeedlePos_112_, v___x_108_);
if (v___x_113_ == 0)
{
lean_object* v___x_115_; 
lean_inc(v_newNeedlePos_112_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 3, v_newNeedlePos_112_);
v___x_115_ = v___x_91_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_needle_86_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_table_87_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_stackPos_88_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_newNeedlePos_112_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
v_it_43_ = v___x_115_;
goto v___jp_42_;
}
}
else
{
lean_object* v_nextStackPos_117_; lean_object* v___x_119_; 
v_nextStackPos_117_ = l_String_Slice_posGE___redArg(v___x_26_, v_stackPos_88_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 3, v___x_108_);
lean_ctor_set(v___x_91_, 2, v_nextStackPos_117_);
v___x_119_ = v___x_91_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_needle_86_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_table_87_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_nextStackPos_117_);
lean_ctor_set(v_reuseFailAlloc_120_, 3, v___x_108_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v_it_43_ = v___x_119_;
goto v___jp_42_;
}
}
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_nextStackPos_123_; lean_object* v___x_125_; 
lean_dec(v_needlePos_89_);
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_add(v_stackPos_88_, v___x_121_);
lean_dec(v_stackPos_88_);
v_nextStackPos_123_ = l_String_Slice_posGE___redArg(v___x_26_, v___x_122_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 3, v___x_108_);
lean_ctor_set(v___x_91_, 2, v_nextStackPos_123_);
v___x_125_ = v___x_91_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_needle_86_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_table_87_);
lean_ctor_set(v_reuseFailAlloc_126_, 2, v_nextStackPos_123_);
lean_ctor_set(v_reuseFailAlloc_126_, 3, v___x_108_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
v_it_43_ = v___x_125_;
goto v___jp_42_;
}
}
}
else
{
lean_object* v___x_127_; lean_object* v_nextStackPos_128_; lean_object* v_nextNeedlePos_129_; uint8_t v_decide_130_; 
lean_del_object(v___x_40_);
v___x_127_ = lean_unsigned_to_nat(1u);
v_nextStackPos_128_ = lean_nat_add(v_stackPos_88_, v___x_127_);
lean_dec(v_stackPos_88_);
v_nextNeedlePos_129_ = lean_nat_add(v_needlePos_89_, v___x_127_);
lean_dec(v_needlePos_89_);
v_decide_130_ = lean_nat_dec_eq(v_nextNeedlePos_129_, v___x_97_);
lean_dec(v___x_97_);
if (v_decide_130_ == 0)
{
lean_object* v___x_132_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 3, v_nextNeedlePos_129_);
lean_ctor_set(v___x_91_, 2, v_nextStackPos_128_);
v___x_132_ = v___x_91_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_needle_86_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_table_87_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_nextStackPos_128_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v_nextNeedlePos_129_);
v___x_132_ = v_reuseFailAlloc_135_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; 
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v_currPos_37_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v_a_28_ = v___x_133_;
goto _start;
}
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_136_ = lean_nat_sub(v_nextStackPos_128_, v_nextNeedlePos_129_);
lean_dec(v_nextNeedlePos_129_);
v___x_137_ = l_String_Slice_pos_x21(v___x_26_, v___x_136_);
lean_dec(v___x_136_);
v___x_138_ = l_String_Slice_pos_x21(v___x_26_, v_nextStackPos_128_);
v___x_139_ = lean_unsigned_to_nat(0u);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 3, v___x_139_);
lean_ctor_set(v___x_91_, 2, v_nextStackPos_128_);
v___x_141_ = v___x_91_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_needle_86_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_table_87_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_nextStackPos_128_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v___x_139_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
v_it_49_ = v___x_141_;
v_startPos_50_ = v___x_137_;
v_endPos_51_ = v___x_138_;
goto v___jp_48_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_40_);
goto v___jp_62_;
}
}
v___jp_42_:
{
lean_object* v___x_45_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 1, v_it_43_);
v___x_45_ = v___x_40_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_currPos_37_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_it_43_);
v___x_45_ = v_reuseFailAlloc_47_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
v_a_28_ = v___x_45_;
goto _start;
}
}
v___jp_48_:
{
lean_object* v_slice_52_; lean_object* v_startInclusive_53_; lean_object* v_endExclusive_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
v_slice_52_ = l_String_Slice_subslice_x21(v___x_26_, v_currPos_37_, v_startPos_50_);
v_startInclusive_53_ = lean_ctor_get(v_slice_52_, 0);
v_endExclusive_54_ = lean_ctor_get(v_slice_52_, 1);
v_isSharedCheck_61_ = !lean_is_exclusive(v_slice_52_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v_slice_52_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_endExclusive_54_);
lean_inc(v_startInclusive_53_);
lean_dec(v_slice_52_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v_nextIt_59_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v_it_49_);
lean_ctor_set(v___x_56_, 0, v_endPos_51_);
v_nextIt_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_endPos_51_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v_it_49_);
v_nextIt_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
v_it_31_ = v_nextIt_59_;
v_startInclusive_32_ = v_startInclusive_53_;
v_endExclusive_33_ = v_endExclusive_54_;
goto v___jp_30_;
}
}
}
v___jp_62_:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(1);
lean_inc(v___x_27_);
v_it_31_ = v___x_63_;
v_startInclusive_32_ = v_currPos_37_;
v_endExclusive_33_ = v___x_27_;
goto v___jp_30_;
}
}
}
else
{
lean_dec(v___x_27_);
lean_dec_ref(v_s_25_);
return v_b_29_;
}
v___jp_30_:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_inc_ref(v_s_25_);
v___x_34_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_34_, 0, v_s_25_);
lean_ctor_set(v___x_34_, 1, v_startInclusive_32_);
lean_ctor_set(v___x_34_, 2, v_endExclusive_33_);
v___x_35_ = lean_array_push(v_b_29_, v___x_34_);
v_a_28_ = v_it_31_;
v_b_29_ = v___x_35_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object* v_s_145_, lean_object* v___x_146_, lean_object* v___x_147_, lean_object* v_a_148_, lean_object* v_b_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_145_, v___x_146_, v___x_147_, v_a_148_, v_b_149_);
lean_dec_ref(v___x_146_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField(lean_object* v_s_159_){
_start:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0));
v___x_161_ = lean_string_dec_eq(v_s_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_162_ = lean_unsigned_to_nat(2u);
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_string_utf8_byte_size(v_s_159_);
lean_inc_ref_n(v_s_159_, 2);
v___x_165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_165_, 0, v_s_159_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
lean_ctor_set(v___x_165_, 2, v___x_164_);
v___x_166_ = l_String_Slice_Pos_prevn(v___x_165_, v___x_164_, v___x_162_);
lean_dec_ref_known(v___x_165_, 3);
lean_inc(v___x_166_);
v___x_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_167_, 0, v_s_159_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
lean_ctor_set(v___x_167_, 2, v___x_164_);
v___x_168_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2));
v___x_169_ = l_String_Slice_beq(v___x_167_, v___x_168_);
lean_dec_ref_known(v___x_167_, 3);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_dec(v___x_166_);
lean_dec_ref(v_s_159_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
lean_inc(v___x_166_);
lean_inc_ref(v_s_159_);
v___x_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_171_, 0, v_s_159_);
lean_ctor_set(v___x_171_, 1, v___x_163_);
lean_ctor_set(v___x_171_, 2, v___x_166_);
v___x_172_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0);
v___x_173_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3));
v___x_174_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_159_, v___x_171_, v___x_166_, v___x_172_, v___x_173_);
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
else
{
lean_object* v___x_196_; 
lean_dec_ref(v_s_159_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(lean_object* v_s_197_, lean_object* v___x_198_, lean_object* v___x_199_, lean_object* v_inst_200_, lean_object* v_R_201_, lean_object* v_a_202_, lean_object* v_b_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_197_, v___x_198_, v___x_199_, v_a_202_, v_b_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object* v_s_205_, lean_object* v___x_206_, lean_object* v___x_207_, lean_object* v_inst_208_, lean_object* v_R_209_, lean_object* v_a_210_, lean_object* v_b_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(v_s_205_, v___x_206_, v___x_207_, v_inst_208_, v_R_209_, v_a_210_, v_b_211_);
lean_dec_ref(v___x_206_);
return v_res_212_;
}
}
uint8_t l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(lean_object* v_s_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Json_parse(v_s_215_);
if (lean_obj_tag(v___x_216_) == 0)
{
uint8_t v___x_217_; 
lean_dec_ref_known(v___x_216_, 1);
v___x_217_ = 0;
return v___x_217_;
}
else
{
lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_a_218_ = lean_ctor_get(v___x_216_, 0);
lean_inc_n(v_a_218_, 2);
lean_dec_ref_known(v___x_216_, 1);
v___x_219_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__0));
v___x_220_ = l_Lean_Json_getObjVal_x3f(v_a_218_, v___x_219_);
if (lean_obj_tag(v___x_220_) == 0)
{
uint8_t v___x_221_; 
lean_dec_ref_known(v___x_220_, 1);
lean_dec(v_a_218_);
v___x_221_ = 0;
return v___x_221_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec_ref_known(v___x_220_, 1);
v___x_222_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__1));
v___x_223_ = l_Lean_Json_getObjVal_x3f(v_a_218_, v___x_222_);
if (lean_obj_tag(v___x_223_) == 0)
{
uint8_t v___x_224_; 
lean_dec_ref_known(v___x_223_, 1);
v___x_224_ = 0;
return v___x_224_;
}
else
{
uint8_t v___x_225_; 
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = 1;
return v___x_225_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_215_ = stack[0].m_obj;
uint8_t v_res_226_;
v_res_226_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_s_215_);
stack->m_num = v_res_226_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___boxed(lean_object* v_s_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_s_227_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__1));
v___x_233_ = lean_mk_io_user_error(v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__3));
v___x_236_ = lean_mk_io_user_error(v___x_235_);
return v___x_236_;
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(lean_object* v_h_237_){
_start:
{
lean_object* v_getLine_239_; lean_object* v___x_240_; 
v_getLine_239_ = lean_ctor_get(v_h_237_, 3);
lean_inc_ref(v_getLine_239_);
v___x_240_ = lean_apply_1(v_getLine_239_, lean_box(0));
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_285_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_285_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_285_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_285_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = lean_string_utf8_byte_size(v_a_241_);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_nat_dec_eq(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1));
v___x_249_ = lean_string_dec_eq(v_a_241_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_inc(v_a_241_);
v___x_250_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField(v_a_241_);
if (lean_obj_tag(v___x_250_) == 0)
{
uint8_t v___x_251_; 
lean_dec_ref(v_h_237_);
lean_inc(v_a_241_);
v___x_251_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_a_241_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_252_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__0));
v___x_253_ = l_String_quote(v_a_241_);
v___x_254_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
v___x_255_ = l_Std_Format_defWidth;
v___x_256_ = l_Std_Format_pretty(v___x_254_, v___x_255_, v___x_246_, v___x_246_);
v___x_257_ = lean_string_append(v___x_252_, v___x_256_);
lean_dec_ref(v___x_256_);
v___x_258_ = lean_mk_io_user_error(v___x_257_);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 1);
lean_ctor_set(v___x_243_, 0, v___x_258_);
v___x_260_ = v___x_243_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
else
{
lean_object* v___x_262_; lean_object* v___x_264_; 
lean_dec(v_a_241_);
v___x_262_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 1);
lean_ctor_set(v___x_243_, 0, v___x_262_);
v___x_264_ = v___x_243_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_object* v_val_266_; lean_object* v___x_267_; 
lean_del_object(v___x_243_);
lean_dec(v_a_241_);
v_val_266_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_val_266_);
lean_dec_ref_known(v___x_250_, 1);
v___x_267_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_237_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_276_; 
v_a_268_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_276_ == 0)
{
v___x_270_ = v___x_267_;
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_267_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_276_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v_val_266_);
lean_ctor_set(v___x_272_, 1, v_a_268_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
lean_dec(v_val_266_);
return v___x_267_;
}
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_279_; 
lean_dec(v_a_241_);
lean_dec_ref(v_h_237_);
v___x_277_ = lean_box(0);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_277_);
v___x_279_ = v___x_243_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_283_; 
lean_dec(v_a_241_);
lean_dec_ref(v_h_237_);
v___x_281_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4);
if (v_isShared_244_ == 0)
{
lean_ctor_set_tag(v___x_243_, 1);
lean_ctor_set(v___x_243_, 0, v___x_281_);
v___x_283_ = v___x_243_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
lean_dec_ref(v_h_237_);
v_a_286_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_293_ == 0)
{
v___x_288_ = v___x_240_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_240_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_286_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_237_ = stack[0].m_obj;
lean_object* v_res_294_;
v_res_294_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_237_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___boxed(lean_object* v_h_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_295_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v_head_301_; lean_object* v_tail_302_; lean_object* v_fst_303_; lean_object* v_snd_304_; uint8_t v___x_305_; 
v_head_301_ = lean_ctor_get(v_x_299_, 0);
v_tail_302_ = lean_ctor_get(v_x_299_, 1);
v_fst_303_ = lean_ctor_get(v_head_301_, 0);
v_snd_304_ = lean_ctor_get(v_head_301_, 1);
v___x_305_ = lean_string_dec_eq(v_x_298_, v_fst_303_);
if (v___x_305_ == 0)
{
v_x_299_ = v_tail_302_;
goto _start;
}
else
{
lean_object* v___x_307_; 
lean_inc(v_snd_304_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v_snd_304_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_308_, v_x_309_);
lean_dec(v_x_309_);
lean_dec_ref(v_x_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
return v_x_314_;
}
else
{
lean_object* v_head_316_; lean_object* v_tail_317_; lean_object* v_fst_318_; lean_object* v_snd_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_head_316_ = lean_ctor_get(v_x_315_, 0);
v_tail_317_ = lean_ctor_get(v_x_315_, 1);
v_fst_318_ = lean_ctor_get(v_head_316_, 0);
v_snd_319_ = lean_ctor_get(v_head_316_, 1);
v___x_320_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_321_ = lean_string_append(v_x_314_, v___x_320_);
v___x_322_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_323_ = lean_string_append(v___x_322_, v_fst_318_);
v___x_324_ = lean_string_append(v___x_323_, v___x_320_);
v___x_325_ = lean_string_append(v___x_324_, v_snd_319_);
v___x_326_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_327_ = lean_string_append(v___x_325_, v___x_326_);
v___x_328_ = lean_string_append(v___x_321_, v___x_327_);
lean_dec_ref(v___x_327_);
v_x_314_ = v___x_328_;
v_x_315_ = v_tail_317_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(v_x_330_, v_x_331_);
lean_dec(v_x_331_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_336_) == 0)
{
lean_object* v___x_337_; 
v___x_337_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__0));
return v___x_337_;
}
else
{
lean_object* v_tail_338_; 
v_tail_338_ = lean_ctor_get(v_x_336_, 1);
if (lean_obj_tag(v_tail_338_) == 0)
{
lean_object* v_head_339_; lean_object* v_fst_340_; lean_object* v_snd_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_head_339_ = lean_ctor_get(v_x_336_, 0);
v_fst_340_ = lean_ctor_get(v_head_339_, 0);
v_snd_341_ = lean_ctor_get(v_head_339_, 1);
v___x_342_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_343_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_344_ = lean_string_append(v___x_343_, v_fst_340_);
v___x_345_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_346_ = lean_string_append(v___x_344_, v___x_345_);
v___x_347_ = lean_string_append(v___x_346_, v_snd_341_);
v___x_348_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_349_ = lean_string_append(v___x_347_, v___x_348_);
v___x_350_ = lean_string_append(v___x_342_, v___x_349_);
lean_dec_ref(v___x_349_);
v___x_351_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__2));
v___x_352_ = lean_string_append(v___x_350_, v___x_351_);
return v___x_352_;
}
else
{
lean_object* v_head_353_; lean_object* v_fst_354_; lean_object* v_snd_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint32_t v___x_366_; lean_object* v___x_367_; 
v_head_353_ = lean_ctor_get(v_x_336_, 0);
v_fst_354_ = lean_ctor_get(v_head_353_, 0);
v_snd_355_ = lean_ctor_get(v_head_353_, 1);
v___x_356_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_357_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_358_ = lean_string_append(v___x_357_, v_fst_354_);
v___x_359_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_360_ = lean_string_append(v___x_358_, v___x_359_);
v___x_361_ = lean_string_append(v___x_360_, v_snd_355_);
v___x_362_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_363_ = lean_string_append(v___x_361_, v___x_362_);
v___x_364_ = lean_string_append(v___x_356_, v___x_363_);
lean_dec_ref(v___x_363_);
v___x_365_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(v___x_364_, v_tail_338_);
v___x_366_ = 93;
v___x_367_ = lean_string_push(v___x_365_, v___x_366_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object* v_x_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(v_x_368_);
lean_dec(v_x_368_);
return v_res_369_;
}
}
lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(lean_object* v_h_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_374_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_407_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_407_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_407_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_407_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__0));
v___x_382_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v___x_381_, v_a_377_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__1));
v___x_384_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(v_a_377_);
lean_dec(v_a_377_);
v___x_385_ = lean_string_append(v___x_383_, v___x_384_);
lean_dec_ref(v___x_384_);
v___x_386_ = lean_mk_io_user_error(v___x_385_);
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 1);
lean_ctor_set(v___x_379_, 0, v___x_386_);
v___x_388_ = v___x_379_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
else
{
lean_object* v_val_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_a_377_);
v_val_390_ = lean_ctor_get(v___x_382_, 0);
lean_inc_n(v_val_390_, 2);
lean_dec_ref_known(v___x_382_, 1);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_string_utf8_byte_size(v_val_390_);
v___x_393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_393_, 0, v_val_390_);
lean_ctor_set(v___x_393_, 1, v___x_391_);
lean_ctor_set(v___x_393_, 2, v___x_392_);
v___x_394_ = l_String_Slice_toNat_x3f(v___x_393_);
lean_dec_ref_known(v___x_393_, 3);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__2));
v___x_396_ = lean_string_append(v___x_395_, v_val_390_);
lean_dec(v_val_390_);
v___x_397_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__3));
v___x_398_ = lean_string_append(v___x_396_, v___x_397_);
v___x_399_ = lean_mk_io_user_error(v___x_398_);
if (v_isShared_380_ == 0)
{
lean_ctor_set_tag(v___x_379_, 1);
lean_ctor_set(v___x_379_, 0, v___x_399_);
v___x_401_ = v___x_379_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
else
{
lean_object* v_val_403_; lean_object* v___x_405_; 
lean_dec(v_val_390_);
v_val_403_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v___x_394_, 1);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v_val_403_);
v___x_405_ = v___x_379_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_val_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
v_a_408_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_376_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_376_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_374_ = stack[0].m_obj;
lean_object* v_res_416_;
v_res_416_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_374_);
stack->m_obj
 = v_res_416_;
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
lean_object* l_Lean_IO_FS_Stream_readLspMessage(lean_object* v_h_429_){
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
LEAN_EXPORT void l_Lean_IO_FS_Stream_readLspMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_429_ = stack[0].m_obj;
lean_object* v_res_443_;
v_res_443_ = l_Lean_IO_FS_Stream_readLspMessage(v_h_429_);
stack->m_obj
 = v_res_443_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage___boxed(lean_object* v_h_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_IO_FS_Stream_readLspMessage(v_h_444_);
return v_res_446_;
}
}
lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString(lean_object* v_h_447_){
_start:
{
lean_object* v_a_450_; lean_object* v___x_456_; 
lean_inc_ref(v_h_447_);
v___x_456_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_447_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_458_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_457_);
lean_dec_ref_known(v___x_456_, 1);
v___x_458_ = l_Lean_IO_FS_Stream_readUTF8(v_h_447_, v_a_457_);
lean_dec(v_a_457_);
if (lean_obj_tag(v___x_458_) == 0)
{
return v___x_458_;
}
else
{
lean_object* v_a_459_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref_known(v___x_458_, 1);
v_a_450_ = v_a_459_;
goto v___jp_449_;
}
}
else
{
lean_object* v_a_460_; 
lean_dec_ref(v_h_447_);
v_a_460_ = lean_ctor_get(v___x_456_, 0);
lean_inc(v_a_460_);
lean_dec_ref_known(v___x_456_, 1);
v_a_450_ = v_a_460_;
goto v___jp_449_;
}
v___jp_449_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_451_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspMessage___closed__0));
v___x_452_ = lean_io_error_to_string(v_a_450_);
v___x_453_ = lean_string_append(v___x_451_, v___x_452_);
lean_dec_ref(v___x_452_);
v___x_454_ = lean_mk_io_user_error(v___x_453_);
v___x_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readLspMessageAsString_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_447_ = stack[0].m_obj;
lean_object* v_res_461_;
v_res_461_ = l_Lean_IO_FS_Stream_readLspMessageAsString(v_h_447_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString___boxed(lean_object* v_h_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_IO_FS_Stream_readLspMessageAsString(v_h_462_);
return v_res_464_;
}
}
lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg(lean_object* v_h_466_, lean_object* v_expectedMethod_467_, lean_object* v_inst_468_){
_start:
{
lean_object* v_a_471_; lean_object* v___x_477_; 
lean_inc_ref(v_h_466_);
v___x_477_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_466_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_479_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v___x_477_, 1);
v___x_479_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_466_, v_a_478_, v_expectedMethod_467_, v_inst_468_);
lean_dec(v_a_478_);
if (lean_obj_tag(v___x_479_) == 0)
{
return v___x_479_;
}
else
{
lean_object* v_a_480_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc(v_a_480_);
lean_dec_ref_known(v___x_479_, 1);
v_a_471_ = v_a_480_;
goto v___jp_470_;
}
}
else
{
lean_object* v_a_481_; 
lean_dec_ref(v_inst_468_);
lean_dec_ref(v_expectedMethod_467_);
lean_dec_ref(v_h_466_);
v_a_481_ = lean_ctor_get(v___x_477_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v___x_477_, 1);
v_a_471_ = v_a_481_;
goto v___jp_470_;
}
v___jp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_472_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspRequestAs___redArg___closed__0));
v___x_473_ = lean_io_error_to_string(v_a_471_);
v___x_474_ = lean_string_append(v___x_472_, v___x_473_);
lean_dec_ref(v___x_473_);
v___x_475_ = lean_mk_io_user_error(v___x_474_);
v___x_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readLspRequestAs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_466_ = stack[0].m_obj;
lean_object* v_expectedMethod_467_ = stack[1].m_obj;
lean_object* v_inst_468_ = stack[2].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_466_, v_expectedMethod_467_, v_inst_468_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object* v_h_483_, lean_object* v_expectedMethod_484_, lean_object* v_inst_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_483_, v_expectedMethod_484_, v_inst_485_);
return v_res_487_;
}
}
lean_object* l_Lean_IO_FS_Stream_readLspRequestAs(lean_object* v_h_488_, lean_object* v_expectedMethod_489_, lean_object* v_00_u03b1_490_, lean_object* v_inst_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_488_, v_expectedMethod_489_, v_inst_491_);
return v___x_493_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readLspRequestAs_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_488_ = stack[0].m_obj;
lean_object* v_expectedMethod_489_ = stack[1].m_obj;
lean_object* v_inst_491_ = stack[3].m_obj;
lean_object* v_res_494_;
v_res_494_ = l_Lean_IO_FS_Stream_readLspRequestAs(v_h_488_, v_expectedMethod_489_, lean_box(0), v_inst_491_);
stack->m_obj
 = v_res_494_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___boxed(lean_object* v_h_495_, lean_object* v_expectedMethod_496_, lean_object* v_00_u03b1_497_, lean_object* v_inst_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_IO_FS_Stream_readLspRequestAs(v_h_495_, v_expectedMethod_496_, v_00_u03b1_497_, v_inst_498_);
return v_res_500_;
}
}
lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(lean_object* v_h_502_, lean_object* v_expectedMethod_503_, lean_object* v_inst_504_){
_start:
{
lean_object* v_a_507_; lean_object* v___x_513_; 
lean_inc_ref(v_h_502_);
v___x_513_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_502_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_502_, v_a_514_, v_expectedMethod_503_, v_inst_504_);
lean_dec(v_a_514_);
if (lean_obj_tag(v___x_515_) == 0)
{
return v___x_515_;
}
else
{
lean_object* v_a_516_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_a_516_);
lean_dec_ref_known(v___x_515_, 1);
v_a_507_ = v_a_516_;
goto v___jp_506_;
}
}
else
{
lean_object* v_a_517_; 
lean_dec_ref(v_inst_504_);
lean_dec_ref(v_expectedMethod_503_);
lean_dec_ref(v_h_502_);
v_a_517_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_517_);
lean_dec_ref_known(v___x_513_, 1);
v_a_507_ = v_a_517_;
goto v___jp_506_;
}
v___jp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_508_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___closed__0));
v___x_509_ = lean_io_error_to_string(v_a_507_);
v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
lean_dec_ref(v___x_509_);
v___x_511_ = lean_mk_io_user_error(v___x_510_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readLspNotificationAs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_502_ = stack[0].m_obj;
lean_object* v_expectedMethod_503_ = stack[1].m_obj;
lean_object* v_inst_504_ = stack[2].m_obj;
lean_object* v_res_518_;
v_res_518_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_502_, v_expectedMethod_503_, v_inst_504_);
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object* v_h_519_, lean_object* v_expectedMethod_520_, lean_object* v_inst_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_519_, v_expectedMethod_520_, v_inst_521_);
return v_res_523_;
}
}
lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs(lean_object* v_h_524_, lean_object* v_expectedMethod_525_, lean_object* v_00_u03b1_526_, lean_object* v_inst_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_524_, v_expectedMethod_525_, v_inst_527_);
return v___x_529_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readLspNotificationAs_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_524_ = stack[0].m_obj;
lean_object* v_expectedMethod_525_ = stack[1].m_obj;
lean_object* v_inst_527_ = stack[3].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lean_IO_FS_Stream_readLspNotificationAs(v_h_524_, v_expectedMethod_525_, lean_box(0), v_inst_527_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___boxed(lean_object* v_h_531_, lean_object* v_expectedMethod_532_, lean_object* v_00_u03b1_533_, lean_object* v_inst_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_IO_FS_Stream_readLspNotificationAs(v_h_531_, v_expectedMethod_532_, v_00_u03b1_533_, v_inst_534_);
return v_res_536_;
}
}
lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg(lean_object* v_h_538_, lean_object* v_expectedID_539_, lean_object* v_inst_540_){
_start:
{
lean_object* v_a_543_; lean_object* v___x_549_; 
lean_inc_ref(v_h_538_);
v___x_549_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_538_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v___x_549_, 1);
v___x_551_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_538_, v_a_550_, v_expectedID_539_, v_inst_540_);
lean_dec(v_a_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
return v___x_551_;
}
else
{
lean_object* v_a_552_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v_a_543_ = v_a_552_;
goto v___jp_542_;
}
}
else
{
lean_object* v_a_553_; 
lean_dec_ref(v_inst_540_);
lean_dec(v_expectedID_539_);
lean_dec_ref(v_h_538_);
v_a_553_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_a_553_);
lean_dec_ref_known(v___x_549_, 1);
v_a_543_ = v_a_553_;
goto v___jp_542_;
}
v___jp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_544_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspResponseAs___redArg___closed__0));
v___x_545_ = lean_io_error_to_string(v_a_543_);
v___x_546_ = lean_string_append(v___x_544_, v___x_545_);
lean_dec_ref(v___x_545_);
v___x_547_ = lean_mk_io_user_error(v___x_546_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readLspResponseAs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_538_ = stack[0].m_obj;
lean_object* v_expectedID_539_ = stack[1].m_obj;
lean_object* v_inst_540_ = stack[2].m_obj;
lean_object* v_res_554_;
v_res_554_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_538_, v_expectedID_539_, v_inst_540_);
stack->m_obj
 = v_res_554_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object* v_h_555_, lean_object* v_expectedID_556_, lean_object* v_inst_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_555_, v_expectedID_556_, v_inst_557_);
return v_res_559_;
}
}
lean_object* l_Lean_IO_FS_Stream_readLspResponseAs(lean_object* v_h_560_, lean_object* v_expectedID_561_, lean_object* v_00_u03b1_562_, lean_object* v_inst_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_560_, v_expectedID_561_, v_inst_563_);
return v___x_565_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_readLspResponseAs_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_560_ = stack[0].m_obj;
lean_object* v_expectedID_561_ = stack[1].m_obj;
lean_object* v_inst_563_ = stack[3].m_obj;
lean_object* v_res_566_;
v_res_566_ = l_Lean_IO_FS_Stream_readLspResponseAs(v_h_560_, v_expectedID_561_, lean_box(0), v_inst_563_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___boxed(lean_object* v_h_567_, lean_object* v_expectedID_568_, lean_object* v_00_u03b1_569_, lean_object* v_inst_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_IO_FS_Stream_readLspResponseAs(v_h_567_, v_expectedID_568_, v_00_u03b1_569_, v_inst_570_);
return v_res_572_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage(lean_object* v_h_575_, lean_object* v_msg_576_){
_start:
{
lean_object* v_flush_578_; lean_object* v_putStr_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_header_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_flush_578_ = lean_ctor_get(v_h_575_, 0);
lean_inc_ref(v_flush_578_);
v_putStr_579_ = lean_ctor_get(v_h_575_, 4);
lean_inc_ref(v_putStr_579_);
lean_dec_ref(v_h_575_);
v___x_580_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__0));
v___x_581_ = lean_string_utf8_byte_size(v_msg_576_);
v___x_582_ = l_Nat_reprFast(v___x_581_);
v___x_583_ = lean_string_append(v___x_580_, v___x_582_);
lean_dec_ref(v___x_582_);
v___x_584_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__1));
v_header_585_ = lean_string_append(v___x_583_, v___x_584_);
v___x_586_ = lean_string_append(v_header_585_, v_msg_576_);
v___x_587_ = lean_apply_2(v_putStr_579_, v___x_586_, lean_box(0));
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_588_; 
lean_dec_ref_known(v___x_587_, 1);
v___x_588_ = lean_apply_1(v_flush_578_, lean_box(0));
return v___x_588_;
}
else
{
lean_dec_ref(v_flush_578_);
return v___x_587_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeSerializedLspMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_575_ = stack[0].m_obj;
lean_object* v_msg_576_ = stack[1].m_obj;
lean_object* v_res_589_;
v_res_589_ = l_Lean_IO_FS_Stream_writeSerializedLspMessage(v_h_575_, v_msg_576_);
stack->m_obj
 = v_res_589_;
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
lean_object* l_Lean_IO_FS_Stream_writeLspMessage(lean_object* v_h_723_, lean_object* v_msg_724_){
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
lean_inc_ref(v___y_819_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___y_819_);
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
lean_ctor_set(v___x_836_, 0, v___y_820_);
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
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_843_;
goto v___jp_818_;
}
case 1:
{
lean_object* v___x_844_; 
v___x_844_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__19, &l_Lean_IO_FS_Stream_writeLspMessage___closed__19_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__19);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_844_;
goto v___jp_818_;
}
case 2:
{
lean_object* v___x_845_; 
v___x_845_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__23, &l_Lean_IO_FS_Stream_writeLspMessage___closed__23_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__23);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_845_;
goto v___jp_818_;
}
case 3:
{
lean_object* v___x_846_; 
v___x_846_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__27, &l_Lean_IO_FS_Stream_writeLspMessage___closed__27_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__27);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_846_;
goto v___jp_818_;
}
case 4:
{
lean_object* v___x_847_; 
v___x_847_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__31, &l_Lean_IO_FS_Stream_writeLspMessage___closed__31_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__31);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_847_;
goto v___jp_818_;
}
case 5:
{
lean_object* v___x_848_; 
v___x_848_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__35, &l_Lean_IO_FS_Stream_writeLspMessage___closed__35_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__35);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_848_;
goto v___jp_818_;
}
case 6:
{
lean_object* v___x_849_; 
v___x_849_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__39, &l_Lean_IO_FS_Stream_writeLspMessage___closed__39_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__39);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_849_;
goto v___jp_818_;
}
case 7:
{
lean_object* v___x_850_; 
v___x_850_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__43, &l_Lean_IO_FS_Stream_writeLspMessage___closed__43_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__43);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_850_;
goto v___jp_818_;
}
case 8:
{
lean_object* v___x_851_; 
v___x_851_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__47, &l_Lean_IO_FS_Stream_writeLspMessage___closed__47_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__47);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_851_;
goto v___jp_818_;
}
case 9:
{
lean_object* v___x_852_; 
v___x_852_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__51, &l_Lean_IO_FS_Stream_writeLspMessage___closed__51_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__51);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_852_;
goto v___jp_818_;
}
case 10:
{
lean_object* v___x_853_; 
v___x_853_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__55, &l_Lean_IO_FS_Stream_writeLspMessage___closed__55_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__55);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
v___y_821_ = v___x_841_;
v___y_822_ = v___x_853_;
goto v___jp_818_;
}
default: 
{
lean_object* v___x_854_; 
v___x_854_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__59, &l_Lean_IO_FS_Stream_writeLspMessage___closed__59_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__59);
v___y_819_ = v___x_842_;
v___y_820_ = v___x_840_;
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
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_723_ = stack[0].m_obj;
lean_object* v_msg_724_ = stack[1].m_obj;
lean_object* v_res_872_;
v_res_872_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_723_, v_msg_724_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage___boxed(lean_object* v_h_873_, lean_object* v_msg_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_873_, v_msg_874_);
return v_res_876_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg(lean_object* v_inst_877_, lean_object* v_h_878_, lean_object* v_r_879_){
_start:
{
lean_object* v_id_881_; lean_object* v_method_882_; lean_object* v_param_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_903_; 
v_id_881_ = lean_ctor_get(v_r_879_, 0);
v_method_882_ = lean_ctor_get(v_r_879_, 1);
v_param_883_ = lean_ctor_get(v_r_879_, 2);
v_isSharedCheck_903_ = !lean_is_exclusive(v_r_879_);
if (v_isSharedCheck_903_ == 0)
{
v___x_885_ = v_r_879_;
v_isShared_886_ = v_isSharedCheck_903_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_param_883_);
lean_inc(v_method_882_);
lean_inc(v_id_881_);
lean_dec(v_r_879_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_903_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___y_888_; lean_object* v___x_893_; 
v___x_893_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_877_, v_param_883_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v___x_894_; 
lean_dec_ref_known(v___x_893_, 1);
v___x_894_ = lean_box(0);
v___y_888_ = v___x_894_;
goto v___jp_887_;
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_893_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
v___y_888_ = v___x_900_;
goto v___jp_887_;
}
}
}
v___jp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 2, v___y_888_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_id_881_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_method_882_);
lean_ctor_set(v_reuseFailAlloc_892_, 2, v___y_888_);
v___x_890_ = v_reuseFailAlloc_892_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_878_, v___x_890_);
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_877_ = stack[0].m_obj;
lean_object* v_h_878_ = stack[1].m_obj;
lean_object* v_r_879_ = stack[2].m_obj;
lean_object* v_res_904_;
v_res_904_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_877_, v_h_878_, v_r_879_);
stack->m_obj
 = v_res_904_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object* v_inst_905_, lean_object* v_h_906_, lean_object* v_r_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_905_, v_h_906_, v_r_907_);
return v_res_909_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspRequest(lean_object* v_00_u03b1_910_, lean_object* v_inst_911_, lean_object* v_h_912_, lean_object* v_r_913_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_911_, v_h_912_, v_r_913_);
return v___x_915_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspRequest_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_911_ = stack[1].m_obj;
lean_object* v_h_912_ = stack[2].m_obj;
lean_object* v_r_913_ = stack[3].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_Lean_IO_FS_Stream_writeLspRequest(lean_box(0), v_inst_911_, v_h_912_, v_r_913_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___boxed(lean_object* v_00_u03b1_917_, lean_object* v_inst_918_, lean_object* v_h_919_, lean_object* v_r_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_IO_FS_Stream_writeLspRequest(v_00_u03b1_917_, v_inst_918_, v_h_919_, v_r_920_);
return v_res_922_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg(lean_object* v_inst_923_, lean_object* v_h_924_, lean_object* v_n_925_){
_start:
{
lean_object* v_method_927_; lean_object* v_param_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_948_; 
v_method_927_ = lean_ctor_get(v_n_925_, 0);
v_param_928_ = lean_ctor_get(v_n_925_, 1);
v_isSharedCheck_948_ = !lean_is_exclusive(v_n_925_);
if (v_isSharedCheck_948_ == 0)
{
v___x_930_ = v_n_925_;
v_isShared_931_ = v_isSharedCheck_948_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_param_928_);
lean_inc(v_method_927_);
lean_dec(v_n_925_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_948_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___y_933_; lean_object* v___x_938_; 
v___x_938_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_923_, v_param_928_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v___x_939_; 
lean_dec_ref_known(v___x_938_, 1);
v___x_939_ = lean_box(0);
v___y_933_ = v___x_939_;
goto v___jp_932_;
}
else
{
lean_object* v_a_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_947_; 
v_a_940_ = lean_ctor_get(v___x_938_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_938_);
if (v_isSharedCheck_947_ == 0)
{
v___x_942_ = v___x_938_;
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_a_940_);
lean_dec(v___x_938_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_947_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_945_; 
if (v_isShared_943_ == 0)
{
v___x_945_ = v___x_942_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_940_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
v___y_933_ = v___x_945_;
goto v___jp_932_;
}
}
}
v___jp_932_:
{
lean_object* v___x_935_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set_tag(v___x_930_, 1);
lean_ctor_set(v___x_930_, 1, v___y_933_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_method_927_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v___y_933_);
v___x_935_ = v_reuseFailAlloc_937_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_924_, v___x_935_);
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspNotification___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_923_ = stack[0].m_obj;
lean_object* v_h_924_ = stack[1].m_obj;
lean_object* v_n_925_ = stack[2].m_obj;
lean_object* v_res_949_;
v_res_949_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_923_, v_h_924_, v_n_925_);
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object* v_inst_950_, lean_object* v_h_951_, lean_object* v_n_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_950_, v_h_951_, v_n_952_);
return v_res_954_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspNotification(lean_object* v_00_u03b1_955_, lean_object* v_inst_956_, lean_object* v_h_957_, lean_object* v_n_958_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_956_, v_h_957_, v_n_958_);
return v___x_960_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspNotification_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_956_ = stack[1].m_obj;
lean_object* v_h_957_ = stack[2].m_obj;
lean_object* v_n_958_ = stack[3].m_obj;
lean_object* v_res_961_;
v_res_961_ = l_Lean_IO_FS_Stream_writeLspNotification(lean_box(0), v_inst_956_, v_h_957_, v_n_958_);
stack->m_obj
 = v_res_961_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___boxed(lean_object* v_00_u03b1_962_, lean_object* v_inst_963_, lean_object* v_h_964_, lean_object* v_n_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_IO_FS_Stream_writeLspNotification(v_00_u03b1_962_, v_inst_963_, v_h_964_, v_n_965_);
return v_res_967_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg(lean_object* v_inst_968_, lean_object* v_h_969_, lean_object* v_r_970_){
_start:
{
lean_object* v_id_972_; lean_object* v_result_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_982_; 
v_id_972_ = lean_ctor_get(v_r_970_, 0);
v_result_973_ = lean_ctor_get(v_r_970_, 1);
v_isSharedCheck_982_ = !lean_is_exclusive(v_r_970_);
if (v_isSharedCheck_982_ == 0)
{
v___x_975_ = v_r_970_;
v_isShared_976_ = v_isSharedCheck_982_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_result_973_);
lean_inc(v_id_972_);
lean_dec(v_r_970_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_982_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = lean_apply_1(v_inst_968_, v_result_973_);
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 2);
lean_ctor_set(v___x_975_, 1, v___x_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_id_972_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v___x_977_);
v___x_979_ = v_reuseFailAlloc_981_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_969_, v___x_979_);
return v___x_980_;
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspResponse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_968_ = stack[0].m_obj;
lean_object* v_h_969_ = stack[1].m_obj;
lean_object* v_r_970_ = stack[2].m_obj;
lean_object* v_res_983_;
v_res_983_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_968_, v_h_969_, v_r_970_);
stack->m_obj
 = v_res_983_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object* v_inst_984_, lean_object* v_h_985_, lean_object* v_r_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_984_, v_h_985_, v_r_986_);
return v_res_988_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspResponse(lean_object* v_00_u03b1_989_, lean_object* v_inst_990_, lean_object* v_h_991_, lean_object* v_r_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_990_, v_h_991_, v_r_992_);
return v___x_994_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspResponse_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_990_ = stack[1].m_obj;
lean_object* v_h_991_ = stack[2].m_obj;
lean_object* v_r_992_ = stack[3].m_obj;
lean_object* v_res_995_;
v_res_995_ = l_Lean_IO_FS_Stream_writeLspResponse(lean_box(0), v_inst_990_, v_h_991_, v_r_992_);
stack->m_obj
 = v_res_995_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___boxed(lean_object* v_00_u03b1_996_, lean_object* v_inst_997_, lean_object* v_h_998_, lean_object* v_r_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_IO_FS_Stream_writeLspResponse(v_00_u03b1_996_, v_inst_997_, v_h_998_, v_r_999_);
return v_res_1001_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspResponseError(lean_object* v_h_1002_, lean_object* v_e_1003_){
_start:
{
lean_object* v_id_1005_; uint8_t v_code_1006_; lean_object* v_message_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1016_; 
v_id_1005_ = lean_ctor_get(v_e_1003_, 0);
v_code_1006_ = lean_ctor_get_uint8(v_e_1003_, sizeof(void*)*3);
v_message_1007_ = lean_ctor_get(v_e_1003_, 1);
v_isSharedCheck_1016_ = !lean_is_exclusive(v_e_1003_);
if (v_isSharedCheck_1016_ == 0)
{
lean_object* v_unused_1017_; 
v_unused_1017_ = lean_ctor_get(v_e_1003_, 2);
lean_dec(v_unused_1017_);
v___x_1009_ = v_e_1003_;
v_isShared_1010_ = v_isSharedCheck_1016_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_message_1007_);
lean_inc(v_id_1005_);
lean_dec(v_e_1003_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1016_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = lean_box(0);
if (v_isShared_1010_ == 0)
{
lean_ctor_set_tag(v___x_1009_, 3);
lean_ctor_set(v___x_1009_, 2, v___x_1011_);
v___x_1013_ = v___x_1009_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_id_1005_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_message_1007_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v___x_1011_);
lean_ctor_set_uint8(v_reuseFailAlloc_1015_, sizeof(void*)*3, v_code_1006_);
v___x_1013_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_1002_, v___x_1013_);
return v___x_1014_;
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspResponseError_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_1002_ = stack[0].m_obj;
lean_object* v_e_1003_ = stack[1].m_obj;
lean_object* v_res_1018_;
v_res_1018_ = l_Lean_IO_FS_Stream_writeLspResponseError(v_h_1002_, v_e_1003_);
stack->m_obj
 = v_res_1018_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError___boxed(lean_object* v_h_1019_, lean_object* v_e_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_IO_FS_Stream_writeLspResponseError(v_h_1019_, v_e_1020_);
return v_res_1022_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object* v_inst_1023_, lean_object* v_h_1024_, lean_object* v_e_1025_){
_start:
{
lean_object* v_id_1027_; uint8_t v_code_1028_; lean_object* v_message_1029_; lean_object* v_data_x3f_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1050_; 
v_id_1027_ = lean_ctor_get(v_e_1025_, 0);
v_code_1028_ = lean_ctor_get_uint8(v_e_1025_, sizeof(void*)*3);
v_message_1029_ = lean_ctor_get(v_e_1025_, 1);
v_data_x3f_1030_ = lean_ctor_get(v_e_1025_, 2);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_e_1025_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1032_ = v_e_1025_;
v_isShared_1033_ = v_isSharedCheck_1050_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_data_x3f_1030_);
lean_inc(v_message_1029_);
lean_inc(v_id_1027_);
lean_dec(v_e_1025_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1050_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___y_1035_; 
if (lean_obj_tag(v_data_x3f_1030_) == 0)
{
lean_object* v___x_1040_; 
lean_dec_ref(v_inst_1023_);
v___x_1040_ = lean_box(0);
v___y_1035_ = v___x_1040_;
goto v___jp_1034_;
}
else
{
lean_object* v_val_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1049_; 
v_val_1041_ = lean_ctor_get(v_data_x3f_1030_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_data_x3f_1030_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1043_ = v_data_x3f_1030_;
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_val_1041_);
lean_dec(v_data_x3f_1030_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1049_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1045_ = lean_apply_1(v_inst_1023_, v_val_1041_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 0, v___x_1045_);
v___x_1047_ = v___x_1043_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
v___y_1035_ = v___x_1047_;
goto v___jp_1034_;
}
}
}
v___jp_1034_:
{
lean_object* v___x_1037_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set_tag(v___x_1032_, 3);
lean_ctor_set(v___x_1032_, 2, v___y_1035_);
v___x_1037_ = v___x_1032_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_id_1027_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_message_1029_);
lean_ctor_set(v_reuseFailAlloc_1039_, 2, v___y_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1039_, sizeof(void*)*3, v_code_1028_);
v___x_1037_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_1024_, v___x_1037_);
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1023_ = stack[0].m_obj;
lean_object* v_h_1024_ = stack[1].m_obj;
lean_object* v_e_1025_ = stack[2].m_obj;
lean_object* v_res_1051_;
v_res_1051_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1023_, v_h_1024_, v_e_1025_);
stack->m_obj
 = v_res_1051_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object* v_inst_1052_, lean_object* v_h_1053_, lean_object* v_e_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1052_, v_h_1053_, v_e_1054_);
return v_res_1056_;
}
}
lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* v_00_u03b1_1057_, lean_object* v_inst_1058_, lean_object* v_h_1059_, lean_object* v_e_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1058_, v_h_1059_, v_e_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_writeLspResponseErrorWithData_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1058_ = stack[1].m_obj;
lean_object* v_h_1059_ = stack[2].m_obj;
lean_object* v_e_1060_ = stack[3].m_obj;
lean_object* v_res_1063_;
v_res_1063_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(lean_box(0), v_inst_1058_, v_h_1059_, v_e_1060_);
stack->m_obj
 = v_res_1063_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_inst_1065_, lean_object* v_h_1066_, lean_object* v_e_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(v_00_u03b1_1064_, v_inst_1065_, v_h_1066_, v_e_1067_);
return v_res_1069_;
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

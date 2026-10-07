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
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0));
v___x_160_ = lean_string_dec_eq(v_s_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_161_ = lean_unsigned_to_nat(2u);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_string_utf8_byte_size(v_s_158_);
lean_inc_ref_n(v_s_158_, 2);
v___x_164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_164_, 0, v_s_158_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_163_);
v___x_165_ = l_String_Slice_Pos_prevn(v___x_164_, v___x_163_, v___x_161_);
lean_dec_ref_known(v___x_164_, 3);
lean_inc(v___x_165_);
v___x_166_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_166_, 0, v_s_158_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
lean_ctor_set(v___x_166_, 2, v___x_163_);
v___x_167_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2));
v___x_168_ = l_String_Slice_beq(v___x_166_, v___x_167_);
lean_dec_ref_known(v___x_166_, 3);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; 
lean_dec(v___x_165_);
lean_dec_ref(v_s_158_);
v___x_169_ = lean_box(0);
return v___x_169_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
lean_inc(v___x_165_);
lean_inc_ref(v_s_158_);
v___x_170_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_170_, 0, v_s_158_);
lean_ctor_set(v___x_170_, 1, v___x_162_);
lean_ctor_set(v___x_170_, 2, v___x_165_);
v___x_171_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0);
v___x_172_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3));
v___x_173_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_158_, v___x_170_, v___x_165_, v___x_171_, v___x_172_);
lean_dec_ref_known(v___x_170_, 3);
v___x_174_ = lean_array_to_list(v___x_173_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v_tail_176_; 
v_tail_176_ = lean_ctor_get(v___x_174_, 1);
lean_inc(v_tail_176_);
if (lean_obj_tag(v_tail_176_) == 0)
{
lean_object* v___x_177_; 
lean_dec_ref_known(v___x_174_, 2);
v___x_177_ = lean_box(0);
return v___x_177_;
}
else
{
lean_object* v_head_178_; lean_object* v_str_179_; lean_object* v_startInclusive_180_; lean_object* v_endExclusive_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_192_; 
v_head_178_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_head_178_);
lean_dec_ref_known(v___x_174_, 2);
v_str_179_ = lean_ctor_get(v_head_178_, 0);
lean_inc_ref(v_str_179_);
v_startInclusive_180_ = lean_ctor_get(v_head_178_, 1);
lean_inc(v_startInclusive_180_);
v_endExclusive_181_ = lean_ctor_get(v_head_178_, 2);
lean_inc(v_endExclusive_181_);
lean_dec(v_head_178_);
v___x_182_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1));
v___x_183_ = l_String_Slice_intercalate(v___x_182_, v_tail_176_);
v_isSharedCheck_192_ = !lean_is_exclusive(v_tail_176_);
if (v_isSharedCheck_192_ == 0)
{
lean_object* v_unused_193_; lean_object* v_unused_194_; 
v_unused_193_ = lean_ctor_get(v_tail_176_, 1);
lean_dec(v_unused_193_);
v_unused_194_ = lean_ctor_get(v_tail_176_, 0);
lean_dec(v_unused_194_);
v___x_185_ = v_tail_176_;
v_isShared_186_ = v_isSharedCheck_192_;
goto v_resetjp_184_;
}
else
{
lean_dec(v_tail_176_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_192_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_string_utf8_extract_fast(v_str_179_, v_startInclusive_180_, v_endExclusive_181_);
lean_dec(v_endExclusive_181_);
lean_dec(v_startInclusive_180_);
lean_dec_ref(v_str_179_);
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 0);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_183_);
v___x_189_ = v_reuseFailAlloc_191_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_190_; 
v___x_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
return v___x_190_;
}
}
}
}
}
}
else
{
lean_object* v___x_195_; 
lean_dec_ref(v_s_158_);
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(lean_object* v_s_196_, lean_object* v___x_197_, lean_object* v___x_198_, lean_object* v_inst_199_, lean_object* v_R_200_, lean_object* v_a_201_, lean_object* v_b_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_196_, v___x_197_, v___x_198_, v_a_201_, v_b_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object* v_s_204_, lean_object* v___x_205_, lean_object* v___x_206_, lean_object* v_inst_207_, lean_object* v_R_208_, lean_object* v_a_209_, lean_object* v_b_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(v_s_204_, v___x_205_, v___x_206_, v_inst_207_, v_R_208_, v_a_209_, v_b_210_);
lean_dec_ref(v___x_205_);
return v_res_211_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(lean_object* v_s_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Json_parse(v_s_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
uint8_t v___x_216_; 
lean_dec_ref_known(v___x_215_, 1);
v___x_216_ = 0;
return v___x_216_;
}
else
{
lean_object* v_a_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_a_217_ = lean_ctor_get(v___x_215_, 0);
lean_inc_n(v_a_217_, 2);
lean_dec_ref_known(v___x_215_, 1);
v___x_218_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__0));
v___x_219_ = l_Lean_Json_getObjVal_x3f(v_a_217_, v___x_218_);
if (lean_obj_tag(v___x_219_) == 0)
{
uint8_t v___x_220_; 
lean_dec_ref_known(v___x_219_, 1);
lean_dec(v_a_217_);
v___x_220_ = 0;
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec_ref_known(v___x_219_, 1);
v___x_221_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__1));
v___x_222_ = l_Lean_Json_getObjVal_x3f(v_a_217_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
uint8_t v___x_223_; 
lean_dec_ref_known(v___x_222_, 1);
v___x_223_ = 0;
return v___x_223_;
}
else
{
uint8_t v___x_224_; 
lean_dec_ref_known(v___x_222_, 1);
v___x_224_ = 1;
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___boxed(lean_object* v_s_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_s_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__1));
v___x_231_ = lean_mk_io_user_error(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__3));
v___x_234_ = lean_mk_io_user_error(v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(lean_object* v_h_235_){
_start:
{
lean_object* v_getLine_237_; lean_object* v___x_238_; 
v_getLine_237_ = lean_ctor_get(v_h_235_, 3);
lean_inc_ref(v_getLine_237_);
v___x_238_ = lean_apply_1(v_getLine_237_, lean_box(0));
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_283_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_283_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_283_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_283_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = lean_string_utf8_byte_size(v_a_239_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_nat_dec_eq(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1));
v___x_247_ = lean_string_dec_eq(v_a_239_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
lean_inc(v_a_239_);
v___x_248_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField(v_a_239_);
if (lean_obj_tag(v___x_248_) == 0)
{
uint8_t v___x_249_; 
lean_dec_ref(v_h_235_);
lean_inc(v_a_239_);
v___x_249_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_a_239_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__0));
v___x_251_ = l_String_quote(v_a_239_);
v___x_252_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
v___x_253_ = l_Std_Format_defWidth;
v___x_254_ = l_Std_Format_pretty(v___x_252_, v___x_253_, v___x_244_, v___x_244_);
v___x_255_ = lean_string_append(v___x_250_, v___x_254_);
lean_dec_ref(v___x_254_);
v___x_256_ = lean_mk_io_user_error(v___x_255_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 1);
lean_ctor_set(v___x_241_, 0, v___x_256_);
v___x_258_ = v___x_241_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
else
{
lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec(v_a_239_);
v___x_260_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 1);
lean_ctor_set(v___x_241_, 0, v___x_260_);
v___x_262_ = v___x_241_;
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
}
else
{
lean_object* v_val_264_; lean_object* v___x_265_; 
lean_del_object(v___x_241_);
lean_dec(v_a_239_);
v_val_264_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_val_264_);
lean_dec_ref_known(v___x_248_, 1);
v___x_265_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_235_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_270_, 0, v_val_264_);
lean_ctor_set(v___x_270_, 1, v_a_266_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_dec(v_val_264_);
return v___x_265_;
}
}
}
else
{
lean_object* v___x_275_; lean_object* v___x_277_; 
lean_dec(v_a_239_);
lean_dec_ref(v_h_235_);
v___x_275_ = lean_box(0);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_275_);
v___x_277_ = v___x_241_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_281_; 
lean_dec(v_a_239_);
lean_dec_ref(v_h_235_);
v___x_279_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 1);
lean_ctor_set(v___x_241_, 0, v___x_279_);
v___x_281_ = v___x_241_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec_ref(v_h_235_);
v_a_284_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_238_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_238_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___boxed(lean_object* v_h_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
lean_object* v___x_297_; 
v___x_297_ = lean_box(0);
return v___x_297_;
}
else
{
lean_object* v_head_298_; lean_object* v_tail_299_; lean_object* v_fst_300_; lean_object* v_snd_301_; uint8_t v___x_302_; 
v_head_298_ = lean_ctor_get(v_x_296_, 0);
v_tail_299_ = lean_ctor_get(v_x_296_, 1);
v_fst_300_ = lean_ctor_get(v_head_298_, 0);
v_snd_301_ = lean_ctor_get(v_head_298_, 1);
v___x_302_ = lean_string_dec_eq(v_x_295_, v_fst_300_);
if (v___x_302_ == 0)
{
v_x_296_ = v_tail_299_;
goto _start;
}
else
{
lean_object* v___x_304_; 
lean_inc(v_snd_301_);
v___x_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_304_, 0, v_snd_301_);
return v___x_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_305_, v_x_306_);
lean_dec(v_x_306_);
lean_dec_ref(v_x_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
if (lean_obj_tag(v_x_312_) == 0)
{
return v_x_311_;
}
else
{
lean_object* v_head_313_; lean_object* v_tail_314_; lean_object* v_fst_315_; lean_object* v_snd_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_head_313_ = lean_ctor_get(v_x_312_, 0);
v_tail_314_ = lean_ctor_get(v_x_312_, 1);
v_fst_315_ = lean_ctor_get(v_head_313_, 0);
v_snd_316_ = lean_ctor_get(v_head_313_, 1);
v___x_317_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_318_ = lean_string_append(v_x_311_, v___x_317_);
v___x_319_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_320_ = lean_string_append(v___x_319_, v_fst_315_);
v___x_321_ = lean_string_append(v___x_320_, v___x_317_);
v___x_322_ = lean_string_append(v___x_321_, v_snd_316_);
v___x_323_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_324_ = lean_string_append(v___x_322_, v___x_323_);
v___x_325_ = lean_string_append(v___x_318_, v___x_324_);
lean_dec_ref(v___x_324_);
v_x_311_ = v___x_325_;
v_x_312_ = v_tail_314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(v_x_327_, v_x_328_);
lean_dec(v_x_328_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(lean_object* v_x_333_){
_start:
{
if (lean_obj_tag(v_x_333_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__0));
return v___x_334_;
}
else
{
lean_object* v_tail_335_; 
v_tail_335_ = lean_ctor_get(v_x_333_, 1);
if (lean_obj_tag(v_tail_335_) == 0)
{
lean_object* v_head_336_; lean_object* v_fst_337_; lean_object* v_snd_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_head_336_ = lean_ctor_get(v_x_333_, 0);
v_fst_337_ = lean_ctor_get(v_head_336_, 0);
v_snd_338_ = lean_ctor_get(v_head_336_, 1);
v___x_339_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_340_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_341_ = lean_string_append(v___x_340_, v_fst_337_);
v___x_342_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_343_ = lean_string_append(v___x_341_, v___x_342_);
v___x_344_ = lean_string_append(v___x_343_, v_snd_338_);
v___x_345_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_346_ = lean_string_append(v___x_344_, v___x_345_);
v___x_347_ = lean_string_append(v___x_339_, v___x_346_);
lean_dec_ref(v___x_346_);
v___x_348_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__2));
v___x_349_ = lean_string_append(v___x_347_, v___x_348_);
return v___x_349_;
}
else
{
lean_object* v_head_350_; lean_object* v_fst_351_; lean_object* v_snd_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; uint32_t v___x_363_; lean_object* v___x_364_; 
v_head_350_ = lean_ctor_get(v_x_333_, 0);
v_fst_351_ = lean_ctor_get(v_head_350_, 0);
v_snd_352_ = lean_ctor_get(v_head_350_, 1);
v___x_353_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_354_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_355_ = lean_string_append(v___x_354_, v_fst_351_);
v___x_356_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_357_ = lean_string_append(v___x_355_, v___x_356_);
v___x_358_ = lean_string_append(v___x_357_, v_snd_352_);
v___x_359_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_360_ = lean_string_append(v___x_358_, v___x_359_);
v___x_361_ = lean_string_append(v___x_353_, v___x_360_);
lean_dec_ref(v___x_360_);
v___x_362_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(v___x_361_, v_tail_335_);
v___x_363_ = 93;
v___x_364_ = lean_string_push(v___x_362_, v___x_363_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object* v_x_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(v_x_365_);
lean_dec(v_x_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(lean_object* v_h_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_371_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_404_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_404_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_404_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_404_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__0));
v___x_379_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v___x_378_, v_a_374_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__1));
v___x_381_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(v_a_374_);
lean_dec(v_a_374_);
v___x_382_ = lean_string_append(v___x_380_, v___x_381_);
lean_dec_ref(v___x_381_);
v___x_383_ = lean_mk_io_user_error(v___x_382_);
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 1);
lean_ctor_set(v___x_376_, 0, v___x_383_);
v___x_385_ = v___x_376_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_object* v_val_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_a_374_);
v_val_387_ = lean_ctor_get(v___x_379_, 0);
lean_inc_n(v_val_387_, 2);
lean_dec_ref_known(v___x_379_, 1);
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = lean_string_utf8_byte_size(v_val_387_);
v___x_390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_390_, 0, v_val_387_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
lean_ctor_set(v___x_390_, 2, v___x_389_);
v___x_391_ = l_String_Slice_toNat_x3f(v___x_390_);
lean_dec_ref_known(v___x_390_, 3);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__2));
v___x_393_ = lean_string_append(v___x_392_, v_val_387_);
lean_dec(v_val_387_);
v___x_394_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__3));
v___x_395_ = lean_string_append(v___x_393_, v___x_394_);
v___x_396_ = lean_mk_io_user_error(v___x_395_);
if (v_isShared_377_ == 0)
{
lean_ctor_set_tag(v___x_376_, 1);
lean_ctor_set(v___x_376_, 0, v___x_396_);
v___x_398_ = v___x_376_;
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
lean_object* v_val_400_; lean_object* v___x_402_; 
lean_dec(v_val_387_);
v_val_400_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_val_400_);
lean_dec_ref_known(v___x_391_, 1);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_val_400_);
v___x_402_ = v___x_376_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_val_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_373_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_373_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___boxed(lean_object* v_h_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0(lean_object* v_00_u03b2_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_417_, v_x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object* v_00_u03b2_420_, lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0(v_00_u03b2_420_, v_x_421_, v_x_422_);
lean_dec(v_x_422_);
lean_dec_ref(v_x_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage(lean_object* v_h_425_){
_start:
{
lean_object* v_a_428_; lean_object* v___x_434_; 
lean_inc_ref(v_h_425_);
v___x_434_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_425_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_436_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
v___x_436_ = l_Lean_IO_FS_Stream_readMessage(v_h_425_, v_a_435_);
lean_dec(v_a_435_);
if (lean_obj_tag(v___x_436_) == 0)
{
return v___x_436_;
}
else
{
lean_object* v_a_437_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v___x_436_, 1);
v_a_428_ = v_a_437_;
goto v___jp_427_;
}
}
else
{
lean_object* v_a_438_; 
lean_dec_ref(v_h_425_);
v_a_438_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_438_);
lean_dec_ref_known(v___x_434_, 1);
v_a_428_ = v_a_438_;
goto v___jp_427_;
}
v___jp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_429_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspMessage___closed__0));
v___x_430_ = lean_io_error_to_string(v_a_428_);
v___x_431_ = lean_string_append(v___x_429_, v___x_430_);
lean_dec_ref(v___x_430_);
v___x_432_ = lean_mk_io_user_error(v___x_431_);
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage___boxed(lean_object* v_h_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_IO_FS_Stream_readLspMessage(v_h_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString(lean_object* v_h_442_){
_start:
{
lean_object* v_a_445_; lean_object* v___x_451_; 
lean_inc_ref(v_h_442_);
v___x_451_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_442_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v___x_453_ = l_Lean_IO_FS_Stream_readUTF8(v_h_442_, v_a_452_);
lean_dec(v_a_452_);
if (lean_obj_tag(v___x_453_) == 0)
{
return v___x_453_;
}
else
{
lean_object* v_a_454_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
v_a_445_ = v_a_454_;
goto v___jp_444_;
}
}
else
{
lean_object* v_a_455_; 
lean_dec_ref(v_h_442_);
v_a_455_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_451_, 1);
v_a_445_ = v_a_455_;
goto v___jp_444_;
}
v___jp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_446_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspMessage___closed__0));
v___x_447_ = lean_io_error_to_string(v_a_445_);
v___x_448_ = lean_string_append(v___x_446_, v___x_447_);
lean_dec_ref(v___x_447_);
v___x_449_ = lean_mk_io_user_error(v___x_448_);
v___x_450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString___boxed(lean_object* v_h_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_IO_FS_Stream_readLspMessageAsString(v_h_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg(lean_object* v_h_460_, lean_object* v_expectedMethod_461_, lean_object* v_inst_462_){
_start:
{
lean_object* v_a_465_; lean_object* v___x_471_; 
lean_inc_ref(v_h_460_);
v___x_471_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_460_);
if (lean_obj_tag(v___x_471_) == 0)
{
lean_object* v_a_472_; lean_object* v___x_473_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v___x_473_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_460_, v_a_472_, v_expectedMethod_461_, v_inst_462_);
lean_dec(v_a_472_);
if (lean_obj_tag(v___x_473_) == 0)
{
return v___x_473_;
}
else
{
lean_object* v_a_474_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
lean_dec_ref_known(v___x_473_, 1);
v_a_465_ = v_a_474_;
goto v___jp_464_;
}
}
else
{
lean_object* v_a_475_; 
lean_dec_ref(v_inst_462_);
lean_dec_ref(v_expectedMethod_461_);
lean_dec_ref(v_h_460_);
v_a_475_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_471_, 1);
v_a_465_ = v_a_475_;
goto v___jp_464_;
}
v___jp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_466_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspRequestAs___redArg___closed__0));
v___x_467_ = lean_io_error_to_string(v_a_465_);
v___x_468_ = lean_string_append(v___x_466_, v___x_467_);
lean_dec_ref(v___x_467_);
v___x_469_ = lean_mk_io_user_error(v___x_468_);
v___x_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object* v_h_476_, lean_object* v_expectedMethod_477_, lean_object* v_inst_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_476_, v_expectedMethod_477_, v_inst_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs(lean_object* v_h_481_, lean_object* v_expectedMethod_482_, lean_object* v_00_u03b1_483_, lean_object* v_inst_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_481_, v_expectedMethod_482_, v_inst_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___boxed(lean_object* v_h_487_, lean_object* v_expectedMethod_488_, lean_object* v_00_u03b1_489_, lean_object* v_inst_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_IO_FS_Stream_readLspRequestAs(v_h_487_, v_expectedMethod_488_, v_00_u03b1_489_, v_inst_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(lean_object* v_h_494_, lean_object* v_expectedMethod_495_, lean_object* v_inst_496_){
_start:
{
lean_object* v_a_499_; lean_object* v___x_505_; 
lean_inc_ref(v_h_494_);
v___x_505_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_494_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_494_, v_a_506_, v_expectedMethod_495_, v_inst_496_);
lean_dec(v_a_506_);
if (lean_obj_tag(v___x_507_) == 0)
{
return v___x_507_;
}
else
{
lean_object* v_a_508_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v_a_499_ = v_a_508_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_509_; 
lean_dec_ref(v_inst_496_);
lean_dec_ref(v_expectedMethod_495_);
lean_dec_ref(v_h_494_);
v_a_509_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_505_, 1);
v_a_499_ = v_a_509_;
goto v___jp_498_;
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_500_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___closed__0));
v___x_501_ = lean_io_error_to_string(v_a_499_);
v___x_502_ = lean_string_append(v___x_500_, v___x_501_);
lean_dec_ref(v___x_501_);
v___x_503_ = lean_mk_io_user_error(v___x_502_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object* v_h_510_, lean_object* v_expectedMethod_511_, lean_object* v_inst_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_510_, v_expectedMethod_511_, v_inst_512_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs(lean_object* v_h_515_, lean_object* v_expectedMethod_516_, lean_object* v_00_u03b1_517_, lean_object* v_inst_518_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_515_, v_expectedMethod_516_, v_inst_518_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___boxed(lean_object* v_h_521_, lean_object* v_expectedMethod_522_, lean_object* v_00_u03b1_523_, lean_object* v_inst_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_IO_FS_Stream_readLspNotificationAs(v_h_521_, v_expectedMethod_522_, v_00_u03b1_523_, v_inst_524_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg(lean_object* v_h_528_, lean_object* v_expectedID_529_, lean_object* v_inst_530_){
_start:
{
lean_object* v_a_533_; lean_object* v___x_539_; 
lean_inc_ref(v_h_528_);
v___x_539_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_528_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
v___x_541_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_528_, v_a_540_, v_expectedID_529_, v_inst_530_);
lean_dec(v_a_540_);
if (lean_obj_tag(v___x_541_) == 0)
{
return v___x_541_;
}
else
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v_a_533_ = v_a_542_;
goto v___jp_532_;
}
}
else
{
lean_object* v_a_543_; 
lean_dec_ref(v_inst_530_);
lean_dec(v_expectedID_529_);
lean_dec_ref(v_h_528_);
v_a_543_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_539_, 1);
v_a_533_ = v_a_543_;
goto v___jp_532_;
}
v___jp_532_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_534_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspResponseAs___redArg___closed__0));
v___x_535_ = lean_io_error_to_string(v_a_533_);
v___x_536_ = lean_string_append(v___x_534_, v___x_535_);
lean_dec_ref(v___x_535_);
v___x_537_ = lean_mk_io_user_error(v___x_536_);
v___x_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object* v_h_544_, lean_object* v_expectedID_545_, lean_object* v_inst_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_544_, v_expectedID_545_, v_inst_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs(lean_object* v_h_549_, lean_object* v_expectedID_550_, lean_object* v_00_u03b1_551_, lean_object* v_inst_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_549_, v_expectedID_550_, v_inst_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___boxed(lean_object* v_h_555_, lean_object* v_expectedID_556_, lean_object* v_00_u03b1_557_, lean_object* v_inst_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_IO_FS_Stream_readLspResponseAs(v_h_555_, v_expectedID_556_, v_00_u03b1_557_, v_inst_558_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage(lean_object* v_h_563_, lean_object* v_msg_564_){
_start:
{
lean_object* v_flush_566_; lean_object* v_putStr_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v_header_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_flush_566_ = lean_ctor_get(v_h_563_, 0);
lean_inc_ref(v_flush_566_);
v_putStr_567_ = lean_ctor_get(v_h_563_, 4);
lean_inc_ref(v_putStr_567_);
lean_dec_ref(v_h_563_);
v___x_568_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__0));
v___x_569_ = lean_string_utf8_byte_size(v_msg_564_);
v___x_570_ = l_Nat_reprFast(v___x_569_);
v___x_571_ = lean_string_append(v___x_568_, v___x_570_);
lean_dec_ref(v___x_570_);
v___x_572_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__1));
v_header_573_ = lean_string_append(v___x_571_, v___x_572_);
v___x_574_ = lean_string_append(v_header_573_, v_msg_564_);
v___x_575_ = lean_apply_2(v_putStr_567_, v___x_574_, lean_box(0));
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; 
lean_dec_ref_known(v___x_575_, 1);
v___x_576_ = lean_apply_1(v_flush_566_, lean_box(0));
return v___x_576_;
}
else
{
lean_dec_ref(v_flush_566_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object* v_h_577_, lean_object* v_msg_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_IO_FS_Stream_writeSerializedLspMessage(v_h_577_, v_msg_578_);
lean_dec_ref(v_msg_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(lean_object* v_k_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
lean_object* v___x_583_; 
lean_dec_ref(v_k_581_);
v___x_583_ = lean_box(0);
return v___x_583_;
}
else
{
lean_object* v_val_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_val_584_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_val_584_);
lean_dec_ref_known(v_x_582_, 1);
v___x_585_ = l_Lean_Json_Structured_toJson(v_val_584_);
v___x_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_586_, 0, v_k_581_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(lean_object* v_k_589_, lean_object* v_x_590_){
_start:
{
if (lean_obj_tag(v_x_590_) == 0)
{
lean_object* v___x_591_; 
lean_dec_ref(v_k_589_);
v___x_591_ = lean_box(0);
return v___x_591_;
}
else
{
lean_object* v_val_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_val_592_ = lean_ctor_get(v_x_590_, 0);
lean_inc(v_val_592_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_k_589_);
lean_ctor_set(v___x_593_, 1, v_val_592_);
v___x_594_ = lean_box(0);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1___boxed(lean_object* v_k_596_, lean_object* v_x_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(v_k_596_, v_x_597_);
lean_dec(v_x_597_);
return v_res_598_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__12(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(32700u);
v___x_615_ = lean_nat_to_int(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__13(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__12, &l_Lean_IO_FS_Stream_writeLspMessage___closed__12_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__12);
v___x_617_ = lean_int_neg(v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__14(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__13, &l_Lean_IO_FS_Stream_writeLspMessage___closed__13_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__13);
v___x_619_ = l_Lean_JsonNumber_fromInt(v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__15(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__14, &l_Lean_IO_FS_Stream_writeLspMessage___closed__14_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__14);
v___x_621_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__16(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_unsigned_to_nat(32600u);
v___x_623_ = lean_nat_to_int(v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__17(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__16, &l_Lean_IO_FS_Stream_writeLspMessage___closed__16_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__16);
v___x_625_ = lean_int_neg(v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__18(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__17, &l_Lean_IO_FS_Stream_writeLspMessage___closed__17_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__17);
v___x_627_ = l_Lean_JsonNumber_fromInt(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__19(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__18, &l_Lean_IO_FS_Stream_writeLspMessage___closed__18_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__18);
v___x_629_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__20(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(32601u);
v___x_631_ = lean_nat_to_int(v___x_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__21(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__20, &l_Lean_IO_FS_Stream_writeLspMessage___closed__20_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__20);
v___x_633_ = lean_int_neg(v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__22(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__21, &l_Lean_IO_FS_Stream_writeLspMessage___closed__21_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__21);
v___x_635_ = l_Lean_JsonNumber_fromInt(v___x_634_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__23(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__22, &l_Lean_IO_FS_Stream_writeLspMessage___closed__22_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__22);
v___x_637_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__24(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(32602u);
v___x_639_ = lean_nat_to_int(v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__25(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__24, &l_Lean_IO_FS_Stream_writeLspMessage___closed__24_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__24);
v___x_641_ = lean_int_neg(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__26(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__25, &l_Lean_IO_FS_Stream_writeLspMessage___closed__25_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__25);
v___x_643_ = l_Lean_JsonNumber_fromInt(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__27(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__26, &l_Lean_IO_FS_Stream_writeLspMessage___closed__26_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__26);
v___x_645_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__28(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(32603u);
v___x_647_ = lean_nat_to_int(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__29(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__28, &l_Lean_IO_FS_Stream_writeLspMessage___closed__28_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__28);
v___x_649_ = lean_int_neg(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__30(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__29, &l_Lean_IO_FS_Stream_writeLspMessage___closed__29_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__29);
v___x_651_ = l_Lean_JsonNumber_fromInt(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__31(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__30, &l_Lean_IO_FS_Stream_writeLspMessage___closed__30_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__30);
v___x_653_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__32(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_unsigned_to_nat(32002u);
v___x_655_ = lean_nat_to_int(v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__33(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__32, &l_Lean_IO_FS_Stream_writeLspMessage___closed__32_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__32);
v___x_657_ = lean_int_neg(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__34(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__33, &l_Lean_IO_FS_Stream_writeLspMessage___closed__33_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__33);
v___x_659_ = l_Lean_JsonNumber_fromInt(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__35(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__34, &l_Lean_IO_FS_Stream_writeLspMessage___closed__34_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__34);
v___x_661_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__36(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(32001u);
v___x_663_ = lean_nat_to_int(v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__37(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__36, &l_Lean_IO_FS_Stream_writeLspMessage___closed__36_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__36);
v___x_665_ = lean_int_neg(v___x_664_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__38(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__37, &l_Lean_IO_FS_Stream_writeLspMessage___closed__37_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__37);
v___x_667_ = l_Lean_JsonNumber_fromInt(v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__39(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__38, &l_Lean_IO_FS_Stream_writeLspMessage___closed__38_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__38);
v___x_669_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__40(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_unsigned_to_nat(32801u);
v___x_671_ = lean_nat_to_int(v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__41(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__40, &l_Lean_IO_FS_Stream_writeLspMessage___closed__40_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__40);
v___x_673_ = lean_int_neg(v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__42(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__41, &l_Lean_IO_FS_Stream_writeLspMessage___closed__41_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__41);
v___x_675_ = l_Lean_JsonNumber_fromInt(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__43(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__42, &l_Lean_IO_FS_Stream_writeLspMessage___closed__42_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__42);
v___x_677_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__44(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_unsigned_to_nat(32800u);
v___x_679_ = lean_nat_to_int(v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__45(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__44, &l_Lean_IO_FS_Stream_writeLspMessage___closed__44_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__44);
v___x_681_ = lean_int_neg(v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__46(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__45, &l_Lean_IO_FS_Stream_writeLspMessage___closed__45_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__45);
v___x_683_ = l_Lean_JsonNumber_fromInt(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__47(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__46, &l_Lean_IO_FS_Stream_writeLspMessage___closed__46_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__46);
v___x_685_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__48(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(32900u);
v___x_687_ = lean_nat_to_int(v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__49(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__48, &l_Lean_IO_FS_Stream_writeLspMessage___closed__48_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__48);
v___x_689_ = lean_int_neg(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__50(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__49, &l_Lean_IO_FS_Stream_writeLspMessage___closed__49_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__49);
v___x_691_ = l_Lean_JsonNumber_fromInt(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__51(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__50, &l_Lean_IO_FS_Stream_writeLspMessage___closed__50_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__50);
v___x_693_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__52(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_unsigned_to_nat(32901u);
v___x_695_ = lean_nat_to_int(v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__53(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__52, &l_Lean_IO_FS_Stream_writeLspMessage___closed__52_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__52);
v___x_697_ = lean_int_neg(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__54(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__53, &l_Lean_IO_FS_Stream_writeLspMessage___closed__53_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__53);
v___x_699_ = l_Lean_JsonNumber_fromInt(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__55(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__54, &l_Lean_IO_FS_Stream_writeLspMessage___closed__54_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__54);
v___x_701_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__56(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_unsigned_to_nat(32902u);
v___x_703_ = lean_nat_to_int(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__57(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__56, &l_Lean_IO_FS_Stream_writeLspMessage___closed__56_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__56);
v___x_705_ = lean_int_neg(v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__58(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__57, &l_Lean_IO_FS_Stream_writeLspMessage___closed__57_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__57);
v___x_707_ = l_Lean_JsonNumber_fromInt(v___x_706_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__59(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__58, &l_Lean_IO_FS_Stream_writeLspMessage___closed__58_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__58);
v___x_709_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage(lean_object* v_h_710_, lean_object* v_msg_711_){
_start:
{
lean_object* v___x_713_; lean_object* v___y_715_; 
v___x_713_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__3));
switch(lean_obj_tag(v_msg_711_))
{
case 0:
{
lean_object* v_id_720_; lean_object* v_method_721_; lean_object* v_params_x3f_722_; lean_object* v___x_723_; lean_object* v___y_725_; 
v_id_720_ = lean_ctor_get(v_msg_711_, 0);
lean_inc(v_id_720_);
v_method_721_ = lean_ctor_get(v_msg_711_, 1);
lean_inc_ref(v_method_721_);
v_params_x3f_722_ = lean_ctor_get(v_msg_711_, 2);
lean_inc(v_params_x3f_722_);
lean_dec_ref_known(v_msg_711_, 3);
v___x_723_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_720_))
{
case 0:
{
lean_object* v_s_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
v_s_736_ = lean_ctor_get(v_id_720_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v_id_720_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v_id_720_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_s_736_);
lean_dec(v_id_720_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 3);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_s_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
v___y_725_ = v___x_741_;
goto v___jp_724_;
}
}
}
case 1:
{
lean_object* v_n_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
v_n_744_ = lean_ctor_get(v_id_720_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v_id_720_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v_id_720_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_n_744_);
lean_dec(v_id_720_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 2);
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_n_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
v___y_725_ = v___x_749_;
goto v___jp_724_;
}
}
}
default: 
{
lean_object* v___x_752_; 
v___x_752_ = lean_box(0);
v___y_725_ = v___x_752_;
goto v___jp_724_;
}
}
v___jp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_723_);
lean_ctor_set(v___x_726_, 1, v___y_725_);
v___x_727_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__5));
v___x_728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_728_, 0, v_method_721_);
v___x_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_box(0);
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_732_, 0, v___x_726_);
lean_ctor_set(v___x_732_, 1, v___x_731_);
v___x_733_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__6));
v___x_734_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(v___x_733_, v_params_x3f_722_);
v___x_735_ = l_List_appendTR___redArg(v___x_732_, v___x_734_);
v___y_715_ = v___x_735_;
goto v___jp_714_;
}
}
case 1:
{
lean_object* v_method_753_; lean_object* v_params_x3f_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_766_; 
v_method_753_ = lean_ctor_get(v_msg_711_, 0);
v_params_x3f_754_ = lean_ctor_get(v_msg_711_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_msg_711_);
if (v_isSharedCheck_766_ == 0)
{
v___x_756_ = v_msg_711_;
v_isShared_757_ = v_isSharedCheck_766_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_params_x3f_754_);
lean_inc(v_method_753_);
lean_dec(v_msg_711_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_766_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_758_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__5));
v___x_759_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_759_, 0, v_method_753_);
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 0);
lean_ctor_set(v___x_756_, 1, v___x_759_);
lean_ctor_set(v___x_756_, 0, v___x_758_);
v___x_761_ = v___x_756_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___x_759_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__6));
v___x_763_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(v___x_762_, v_params_x3f_754_);
v___x_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_761_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___y_715_ = v___x_764_;
goto v___jp_714_;
}
}
}
case 2:
{
lean_object* v_id_767_; lean_object* v_result_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_800_; 
v_id_767_ = lean_ctor_get(v_msg_711_, 0);
v_result_768_ = lean_ctor_get(v_msg_711_, 1);
v_isSharedCheck_800_ = !lean_is_exclusive(v_msg_711_);
if (v_isSharedCheck_800_ == 0)
{
v___x_770_ = v_msg_711_;
v_isShared_771_ = v_isSharedCheck_800_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_result_768_);
lean_inc(v_id_767_);
lean_dec(v_msg_711_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_800_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___y_774_; 
v___x_772_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_767_))
{
case 0:
{
lean_object* v_s_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_s_783_ = lean_ctor_get(v_id_767_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_id_767_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v_id_767_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_s_783_);
lean_dec(v_id_767_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set_tag(v___x_785_, 3);
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_s_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
v___y_774_ = v___x_788_;
goto v___jp_773_;
}
}
}
case 1:
{
lean_object* v_n_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_n_791_ = lean_ctor_get(v_id_767_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v_id_767_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v_id_767_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_n_791_);
lean_dec(v_id_767_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
lean_ctor_set_tag(v___x_793_, 2);
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_n_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
v___y_774_ = v___x_796_;
goto v___jp_773_;
}
}
}
default: 
{
lean_object* v___x_799_; 
v___x_799_ = lean_box(0);
v___y_774_ = v___x_799_;
goto v___jp_773_;
}
}
v___jp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_771_ == 0)
{
lean_ctor_set_tag(v___x_770_, 0);
lean_ctor_set(v___x_770_, 1, v___y_774_);
lean_ctor_set(v___x_770_, 0, v___x_772_);
v___x_776_ = v___x_770_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___y_774_);
v___x_776_ = v_reuseFailAlloc_782_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_777_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__7));
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
lean_ctor_set(v___x_778_, 1, v_result_768_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
v___x_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_776_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___y_715_ = v___x_781_;
goto v___jp_714_;
}
}
}
}
default: 
{
lean_object* v_id_801_; uint8_t v_code_802_; lean_object* v_message_803_; lean_object* v_data_x3f_804_; lean_object* v___y_806_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___x_824_; lean_object* v___y_826_; 
v_id_801_ = lean_ctor_get(v_msg_711_, 0);
lean_inc(v_id_801_);
v_code_802_ = lean_ctor_get_uint8(v_msg_711_, sizeof(void*)*3);
v_message_803_ = lean_ctor_get(v_msg_711_, 1);
lean_inc_ref(v_message_803_);
v_data_x3f_804_ = lean_ctor_get(v_msg_711_, 2);
lean_inc(v_data_x3f_804_);
lean_dec_ref_known(v_msg_711_, 3);
v___x_824_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_801_))
{
case 0:
{
lean_object* v_s_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_s_842_ = lean_ctor_get(v_id_801_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v_id_801_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v_id_801_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_s_842_);
lean_dec(v_id_801_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 3);
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_s_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
v___y_826_ = v___x_847_;
goto v___jp_825_;
}
}
}
case 1:
{
lean_object* v_n_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_n_850_ = lean_ctor_get(v_id_801_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v_id_801_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v_id_801_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_n_850_);
lean_dec(v_id_801_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
lean_ctor_set_tag(v___x_852_, 2);
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_n_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
v___y_826_ = v___x_855_;
goto v___jp_825_;
}
}
}
default: 
{
lean_object* v___x_858_; 
v___x_858_ = lean_box(0);
v___y_826_ = v___x_858_;
goto v___jp_825_;
}
}
v___jp_805_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_inc(v___y_809_);
lean_inc_ref(v___y_806_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___y_806_);
lean_ctor_set(v___x_810_, 1, v___y_809_);
v___x_811_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__8));
v___x_812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_812_, 0, v_message_803_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_box(0);
v___x_815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_810_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__9));
v___x_818_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(v___x_817_, v_data_x3f_804_);
lean_dec(v_data_x3f_804_);
v___x_819_ = l_List_appendTR___redArg(v___x_816_, v___x_818_);
v___x_820_ = l_Lean_Json_mkObj(v___x_819_);
lean_dec(v___x_819_);
lean_inc_ref(v___y_808_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___y_808_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v___x_814_);
v___x_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_823_, 0, v___y_807_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___y_715_ = v___x_823_;
goto v___jp_714_;
}
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_824_);
lean_ctor_set(v___x_827_, 1, v___y_826_);
v___x_828_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__10));
v___x_829_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__11));
switch(v_code_802_)
{
case 0:
{
lean_object* v___x_830_; 
v___x_830_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__15, &l_Lean_IO_FS_Stream_writeLspMessage___closed__15_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__15);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_830_;
goto v___jp_805_;
}
case 1:
{
lean_object* v___x_831_; 
v___x_831_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__19, &l_Lean_IO_FS_Stream_writeLspMessage___closed__19_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__19);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_831_;
goto v___jp_805_;
}
case 2:
{
lean_object* v___x_832_; 
v___x_832_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__23, &l_Lean_IO_FS_Stream_writeLspMessage___closed__23_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__23);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_832_;
goto v___jp_805_;
}
case 3:
{
lean_object* v___x_833_; 
v___x_833_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__27, &l_Lean_IO_FS_Stream_writeLspMessage___closed__27_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__27);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_833_;
goto v___jp_805_;
}
case 4:
{
lean_object* v___x_834_; 
v___x_834_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__31, &l_Lean_IO_FS_Stream_writeLspMessage___closed__31_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__31);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_834_;
goto v___jp_805_;
}
case 5:
{
lean_object* v___x_835_; 
v___x_835_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__35, &l_Lean_IO_FS_Stream_writeLspMessage___closed__35_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__35);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_835_;
goto v___jp_805_;
}
case 6:
{
lean_object* v___x_836_; 
v___x_836_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__39, &l_Lean_IO_FS_Stream_writeLspMessage___closed__39_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__39);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_836_;
goto v___jp_805_;
}
case 7:
{
lean_object* v___x_837_; 
v___x_837_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__43, &l_Lean_IO_FS_Stream_writeLspMessage___closed__43_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__43);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_837_;
goto v___jp_805_;
}
case 8:
{
lean_object* v___x_838_; 
v___x_838_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__47, &l_Lean_IO_FS_Stream_writeLspMessage___closed__47_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__47);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_838_;
goto v___jp_805_;
}
case 9:
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__51, &l_Lean_IO_FS_Stream_writeLspMessage___closed__51_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__51);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_839_;
goto v___jp_805_;
}
case 10:
{
lean_object* v___x_840_; 
v___x_840_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__55, &l_Lean_IO_FS_Stream_writeLspMessage___closed__55_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__55);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_840_;
goto v___jp_805_;
}
default: 
{
lean_object* v___x_841_; 
v___x_841_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__59, &l_Lean_IO_FS_Stream_writeLspMessage___closed__59_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__59);
v___y_806_ = v___x_829_;
v___y_807_ = v___x_827_;
v___y_808_ = v___x_828_;
v___y_809_ = v___x_841_;
goto v___jp_805_;
}
}
}
}
}
v___jp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_713_);
lean_ctor_set(v___x_716_, 1, v___y_715_);
v___x_717_ = l_Lean_Json_mkObj(v___x_716_);
lean_dec_ref_known(v___x_716_, 2);
v___x_718_ = l_Lean_Json_compress(v___x_717_);
v___x_719_ = l_Lean_IO_FS_Stream_writeSerializedLspMessage(v_h_710_, v___x_718_);
lean_dec_ref(v___x_718_);
return v___x_719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage___boxed(lean_object* v_h_859_, lean_object* v_msg_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_859_, v_msg_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg(lean_object* v_inst_863_, lean_object* v_h_864_, lean_object* v_r_865_){
_start:
{
lean_object* v_id_867_; lean_object* v_method_868_; lean_object* v_param_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_889_; 
v_id_867_ = lean_ctor_get(v_r_865_, 0);
v_method_868_ = lean_ctor_get(v_r_865_, 1);
v_param_869_ = lean_ctor_get(v_r_865_, 2);
v_isSharedCheck_889_ = !lean_is_exclusive(v_r_865_);
if (v_isSharedCheck_889_ == 0)
{
v___x_871_ = v_r_865_;
v_isShared_872_ = v_isSharedCheck_889_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_param_869_);
lean_inc(v_method_868_);
lean_inc(v_id_867_);
lean_dec(v_r_865_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_889_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___y_874_; lean_object* v___x_879_; 
v___x_879_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_863_, v_param_869_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v___x_880_; 
lean_dec_ref_known(v___x_879_, 1);
v___x_880_ = lean_box(0);
v___y_874_ = v___x_880_;
goto v___jp_873_;
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
v_a_881_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_879_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_879_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
v___y_874_ = v___x_886_;
goto v___jp_873_;
}
}
}
v___jp_873_:
{
lean_object* v___x_876_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 2, v___y_874_);
v___x_876_ = v___x_871_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_id_867_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_method_868_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v___y_874_);
v___x_876_ = v_reuseFailAlloc_878_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_864_, v___x_876_);
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object* v_inst_890_, lean_object* v_h_891_, lean_object* v_r_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_890_, v_h_891_, v_r_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest(lean_object* v_00_u03b1_895_, lean_object* v_inst_896_, lean_object* v_h_897_, lean_object* v_r_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_896_, v_h_897_, v_r_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___boxed(lean_object* v_00_u03b1_901_, lean_object* v_inst_902_, lean_object* v_h_903_, lean_object* v_r_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_IO_FS_Stream_writeLspRequest(v_00_u03b1_901_, v_inst_902_, v_h_903_, v_r_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg(lean_object* v_inst_907_, lean_object* v_h_908_, lean_object* v_n_909_){
_start:
{
lean_object* v_method_911_; lean_object* v_param_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_932_; 
v_method_911_ = lean_ctor_get(v_n_909_, 0);
v_param_912_ = lean_ctor_get(v_n_909_, 1);
v_isSharedCheck_932_ = !lean_is_exclusive(v_n_909_);
if (v_isSharedCheck_932_ == 0)
{
v___x_914_ = v_n_909_;
v_isShared_915_ = v_isSharedCheck_932_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_param_912_);
lean_inc(v_method_911_);
lean_dec(v_n_909_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_932_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___y_917_; lean_object* v___x_922_; 
v___x_922_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_907_, v_param_912_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_923_; 
lean_dec_ref_known(v___x_922_, 1);
v___x_923_ = lean_box(0);
v___y_917_ = v___x_923_;
goto v___jp_916_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_922_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_922_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
v___y_917_ = v___x_929_;
goto v___jp_916_;
}
}
}
v___jp_916_:
{
lean_object* v___x_919_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set_tag(v___x_914_, 1);
lean_ctor_set(v___x_914_, 1, v___y_917_);
v___x_919_ = v___x_914_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_method_911_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v___y_917_);
v___x_919_ = v_reuseFailAlloc_921_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_908_, v___x_919_);
return v___x_920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object* v_inst_933_, lean_object* v_h_934_, lean_object* v_n_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_933_, v_h_934_, v_n_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification(lean_object* v_00_u03b1_938_, lean_object* v_inst_939_, lean_object* v_h_940_, lean_object* v_n_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_939_, v_h_940_, v_n_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___boxed(lean_object* v_00_u03b1_944_, lean_object* v_inst_945_, lean_object* v_h_946_, lean_object* v_n_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_IO_FS_Stream_writeLspNotification(v_00_u03b1_944_, v_inst_945_, v_h_946_, v_n_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg(lean_object* v_inst_950_, lean_object* v_h_951_, lean_object* v_r_952_){
_start:
{
lean_object* v_id_954_; lean_object* v_result_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_964_; 
v_id_954_ = lean_ctor_get(v_r_952_, 0);
v_result_955_ = lean_ctor_get(v_r_952_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_r_952_);
if (v_isSharedCheck_964_ == 0)
{
v___x_957_ = v_r_952_;
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_result_955_);
lean_inc(v_id_954_);
lean_dec(v_r_952_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_964_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_959_; lean_object* v___x_961_; 
v___x_959_ = lean_apply_1(v_inst_950_, v_result_955_);
if (v_isShared_958_ == 0)
{
lean_ctor_set_tag(v___x_957_, 2);
lean_ctor_set(v___x_957_, 1, v___x_959_);
v___x_961_ = v___x_957_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_id_954_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_959_);
v___x_961_ = v_reuseFailAlloc_963_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_951_, v___x_961_);
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object* v_inst_965_, lean_object* v_h_966_, lean_object* v_r_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_965_, v_h_966_, v_r_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse(lean_object* v_00_u03b1_970_, lean_object* v_inst_971_, lean_object* v_h_972_, lean_object* v_r_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_971_, v_h_972_, v_r_973_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___boxed(lean_object* v_00_u03b1_976_, lean_object* v_inst_977_, lean_object* v_h_978_, lean_object* v_r_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_IO_FS_Stream_writeLspResponse(v_00_u03b1_976_, v_inst_977_, v_h_978_, v_r_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError(lean_object* v_h_982_, lean_object* v_e_983_){
_start:
{
lean_object* v_id_985_; uint8_t v_code_986_; lean_object* v_message_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_996_; 
v_id_985_ = lean_ctor_get(v_e_983_, 0);
v_code_986_ = lean_ctor_get_uint8(v_e_983_, sizeof(void*)*3);
v_message_987_ = lean_ctor_get(v_e_983_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_e_983_);
if (v_isSharedCheck_996_ == 0)
{
lean_object* v_unused_997_; 
v_unused_997_ = lean_ctor_get(v_e_983_, 2);
lean_dec(v_unused_997_);
v___x_989_ = v_e_983_;
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_message_987_);
lean_inc(v_id_985_);
lean_dec(v_e_983_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = lean_box(0);
if (v_isShared_990_ == 0)
{
lean_ctor_set_tag(v___x_989_, 3);
lean_ctor_set(v___x_989_, 2, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_id_985_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_message_987_);
lean_ctor_set(v_reuseFailAlloc_995_, 2, v___x_991_);
lean_ctor_set_uint8(v_reuseFailAlloc_995_, sizeof(void*)*3, v_code_986_);
v___x_993_ = v_reuseFailAlloc_995_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_982_, v___x_993_);
return v___x_994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError___boxed(lean_object* v_h_998_, lean_object* v_e_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_IO_FS_Stream_writeLspResponseError(v_h_998_, v_e_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object* v_inst_1002_, lean_object* v_h_1003_, lean_object* v_e_1004_){
_start:
{
lean_object* v_id_1006_; uint8_t v_code_1007_; lean_object* v_message_1008_; lean_object* v_data_x3f_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1029_; 
v_id_1006_ = lean_ctor_get(v_e_1004_, 0);
v_code_1007_ = lean_ctor_get_uint8(v_e_1004_, sizeof(void*)*3);
v_message_1008_ = lean_ctor_get(v_e_1004_, 1);
v_data_x3f_1009_ = lean_ctor_get(v_e_1004_, 2);
v_isSharedCheck_1029_ = !lean_is_exclusive(v_e_1004_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1011_ = v_e_1004_;
v_isShared_1012_ = v_isSharedCheck_1029_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_data_x3f_1009_);
lean_inc(v_message_1008_);
lean_inc(v_id_1006_);
lean_dec(v_e_1004_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1029_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___y_1014_; 
if (lean_obj_tag(v_data_x3f_1009_) == 0)
{
lean_object* v___x_1019_; 
lean_dec_ref(v_inst_1002_);
v___x_1019_ = lean_box(0);
v___y_1014_ = v___x_1019_;
goto v___jp_1013_;
}
else
{
lean_object* v_val_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1028_; 
v_val_1020_ = lean_ctor_get(v_data_x3f_1009_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_data_x3f_1009_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1022_ = v_data_x3f_1009_;
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_val_1020_);
lean_dec(v_data_x3f_1009_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1024_ = lean_apply_1(v_inst_1002_, v_val_1020_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
v___y_1014_ = v___x_1026_;
goto v___jp_1013_;
}
}
}
v___jp_1013_:
{
lean_object* v___x_1016_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set_tag(v___x_1011_, 3);
lean_ctor_set(v___x_1011_, 2, v___y_1014_);
v___x_1016_ = v___x_1011_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_id_1006_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_message_1008_);
lean_ctor_set(v_reuseFailAlloc_1018_, 2, v___y_1014_);
lean_ctor_set_uint8(v_reuseFailAlloc_1018_, sizeof(void*)*3, v_code_1007_);
v___x_1016_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_1003_, v___x_1016_);
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object* v_inst_1030_, lean_object* v_h_1031_, lean_object* v_e_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1030_, v_h_1031_, v_e_1032_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* v_00_u03b1_1035_, lean_object* v_inst_1036_, lean_object* v_h_1037_, lean_object* v_e_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1036_, v_h_1037_, v_e_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_inst_1042_, lean_object* v_h_1043_, lean_object* v_e_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(v_00_u03b1_1041_, v_inst_1042_, v_h_1043_, v_e_1044_);
return v_res_1046_;
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

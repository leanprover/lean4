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
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__5;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__6;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__7 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__7_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__7_value)}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__8 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__8_value;
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
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__0));
v___x_3_ = lean_string_utf8_byte_size(v___x_2_);
return v___x_3_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1);
v___x_6_ = lean_nat_dec_eq(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__1);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__0));
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_7_);
return v___x_10_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3);
v___x_12_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__4);
v___x_15_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3);
v___x_16_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_13_);
lean_ctor_set(v___x_16_, 3, v___x_13_);
return v___x_16_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__5, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__5);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg(){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__2);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__6, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__6_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__6);
return v___x_27_;
}
else
{
lean_object* v___x_28_; 
v___x_28_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__8));
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___boxed(lean_object* v___dummy_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg();
return v_res_30_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0(void){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg();
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(lean_object* v_s_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object* v_s_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0(v_s_34_);
lean_dec_ref(v_s_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object* v_s_36_, lean_object* v___x_37_, lean_object* v___x_38_, lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
lean_object* v_it_42_; lean_object* v_startInclusive_43_; lean_object* v_endExclusive_44_; 
if (lean_obj_tag(v_a_39_) == 0)
{
lean_object* v_currPos_48_; lean_object* v_searcher_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_155_; 
v_currPos_48_ = lean_ctor_get(v_a_39_, 0);
v_searcher_49_ = lean_ctor_get(v_a_39_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_a_39_);
if (v_isSharedCheck_155_ == 0)
{
v___x_51_ = v_a_39_;
v_isShared_52_ = v_isSharedCheck_155_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_searcher_49_);
lean_inc(v_currPos_48_);
lean_dec(v_a_39_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_155_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v_it_54_; lean_object* v_it_60_; lean_object* v_startPos_61_; lean_object* v_endPos_62_; 
switch(lean_obj_tag(v_searcher_49_))
{
case 0:
{
lean_object* v_pos_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_87_; 
lean_del_object(v___x_51_);
v_pos_75_ = lean_ctor_get(v_searcher_49_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v_searcher_49_);
if (v_isSharedCheck_87_ == 0)
{
v___x_77_ = v_searcher_49_;
v_isShared_78_ = v_isSharedCheck_87_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_pos_75_);
lean_dec(v_searcher_49_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_87_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v_startInclusive_79_; lean_object* v_endExclusive_80_; lean_object* v___x_81_; uint8_t v_decide_82_; 
v_startInclusive_79_ = lean_ctor_get(v___x_37_, 1);
v_endExclusive_80_ = lean_ctor_get(v___x_37_, 2);
v___x_81_ = lean_nat_sub(v_endExclusive_80_, v_startInclusive_79_);
v_decide_82_ = lean_nat_dec_eq(v_pos_75_, v___x_81_);
lean_dec(v___x_81_);
if (v_decide_82_ == 0)
{
lean_object* v___x_84_; 
lean_inc(v_pos_75_);
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 1);
v___x_84_ = v___x_77_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_pos_75_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_inc(v_pos_75_);
v_it_60_ = v___x_84_;
v_startPos_61_ = v_pos_75_;
v_endPos_62_ = v_pos_75_;
goto v___jp_59_;
}
}
else
{
lean_object* v___x_86_; 
lean_del_object(v___x_77_);
v___x_86_ = lean_box(3);
lean_inc(v_pos_75_);
v_it_60_ = v___x_86_;
v_startPos_61_ = v_pos_75_;
v_endPos_62_ = v_pos_75_;
goto v___jp_59_;
}
}
}
case 1:
{
lean_object* v_pos_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_pos_88_ = lean_ctor_get(v_searcher_49_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_searcher_49_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v_searcher_49_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_pos_88_);
lean_dec(v_searcher_49_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = lean_string_utf8_next_fast(v_s_36_, v_pos_88_);
lean_dec(v_pos_88_);
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 0);
lean_ctor_set(v___x_90_, 0, v___x_92_);
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
v_it_54_ = v___x_94_;
goto v___jp_53_;
}
}
}
case 2:
{
lean_object* v_needle_97_; lean_object* v_table_98_; lean_object* v_stackPos_99_; lean_object* v_needlePos_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_154_; 
v_needle_97_ = lean_ctor_get(v_searcher_49_, 0);
v_table_98_ = lean_ctor_get(v_searcher_49_, 1);
v_stackPos_99_ = lean_ctor_get(v_searcher_49_, 2);
v_needlePos_100_ = lean_ctor_get(v_searcher_49_, 3);
v_isSharedCheck_154_ = !lean_is_exclusive(v_searcher_49_);
if (v_isSharedCheck_154_ == 0)
{
v___x_102_ = v_searcher_49_;
v_isShared_103_ = v_isSharedCheck_154_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_needlePos_100_);
lean_inc(v_stackPos_99_);
lean_inc(v_table_98_);
lean_inc(v_needle_97_);
lean_dec(v_searcher_49_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_154_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_str_104_; lean_object* v_startInclusive_105_; lean_object* v_endExclusive_106_; lean_object* v_basePos_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v_str_104_ = lean_ctor_get(v_needle_97_, 0);
v_startInclusive_105_ = lean_ctor_get(v_needle_97_, 1);
v_endExclusive_106_ = lean_ctor_get(v_needle_97_, 2);
v_basePos_107_ = lean_nat_sub(v_stackPos_99_, v_needlePos_100_);
v___x_108_ = lean_nat_sub(v_endExclusive_106_, v_startInclusive_105_);
v___x_109_ = lean_nat_add(v_basePos_107_, v___x_108_);
v___x_110_ = lean_nat_dec_le(v___x_109_, v___x_38_);
lean_dec(v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
lean_dec(v___x_108_);
lean_del_object(v___x_102_);
lean_dec(v_needlePos_100_);
lean_dec(v_stackPos_99_);
lean_dec_ref(v_table_98_);
lean_dec_ref(v_needle_97_);
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_basePos_107_, v___x_111_);
lean_dec(v_basePos_107_);
v___x_113_ = lean_nat_dec_le(v___x_112_, v___x_38_);
lean_dec(v___x_112_);
if (v___x_113_ == 0)
{
lean_del_object(v___x_51_);
goto v___jp_73_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_box(3);
v_it_54_ = v___x_114_;
goto v___jp_53_;
}
}
else
{
uint8_t v_stackByte_115_; lean_object* v___x_116_; uint8_t v_patByte_117_; uint8_t v___x_118_; 
lean_dec(v_basePos_107_);
lean_inc(v_stackPos_99_);
v_stackByte_115_ = lean_string_get_byte_fast(v_s_36_, v_stackPos_99_);
v___x_116_ = lean_nat_add(v_startInclusive_105_, v_needlePos_100_);
v_patByte_117_ = lean_string_get_byte_fast(v_str_104_, v___x_116_);
v___x_118_ = lean_uint8_dec_eq(v_stackByte_115_, v_patByte_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; uint8_t v_decide_120_; 
lean_dec(v___x_108_);
v___x_119_ = lean_unsigned_to_nat(0u);
v_decide_120_ = lean_nat_dec_eq(v_needlePos_100_, v___x_119_);
if (v_decide_120_ == 0)
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v_newNeedlePos_123_; uint8_t v___x_124_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = lean_nat_sub(v_needlePos_100_, v___x_121_);
lean_dec(v_needlePos_100_);
v_newNeedlePos_123_ = lean_array_fget_borrowed(v_table_98_, v___x_122_);
lean_dec(v___x_122_);
v___x_124_ = lean_nat_dec_eq(v_newNeedlePos_123_, v___x_119_);
if (v___x_124_ == 0)
{
lean_object* v___x_126_; 
lean_inc(v_newNeedlePos_123_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 3, v_newNeedlePos_123_);
v___x_126_ = v___x_102_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_needle_97_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_table_98_);
lean_ctor_set(v_reuseFailAlloc_127_, 2, v_stackPos_99_);
lean_ctor_set(v_reuseFailAlloc_127_, 3, v_newNeedlePos_123_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
v_it_54_ = v___x_126_;
goto v___jp_53_;
}
}
else
{
lean_object* v_nextStackPos_128_; lean_object* v___x_130_; 
v_nextStackPos_128_ = l_String_Slice_posGE___redArg(v___x_37_, v_stackPos_99_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 3, v___x_119_);
lean_ctor_set(v___x_102_, 2, v_nextStackPos_128_);
v___x_130_ = v___x_102_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_needle_97_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_table_98_);
lean_ctor_set(v_reuseFailAlloc_131_, 2, v_nextStackPos_128_);
lean_ctor_set(v_reuseFailAlloc_131_, 3, v___x_119_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
v_it_54_ = v___x_130_;
goto v___jp_53_;
}
}
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v_nextStackPos_134_; lean_object* v___x_136_; 
lean_dec(v_needlePos_100_);
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_stackPos_99_, v___x_132_);
lean_dec(v_stackPos_99_);
v_nextStackPos_134_ = l_String_Slice_posGE___redArg(v___x_37_, v___x_133_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 3, v___x_119_);
lean_ctor_set(v___x_102_, 2, v_nextStackPos_134_);
v___x_136_ = v___x_102_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_needle_97_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_table_98_);
lean_ctor_set(v_reuseFailAlloc_137_, 2, v_nextStackPos_134_);
lean_ctor_set(v_reuseFailAlloc_137_, 3, v___x_119_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
v_it_54_ = v___x_136_;
goto v___jp_53_;
}
}
}
else
{
lean_object* v___x_138_; lean_object* v_nextStackPos_139_; lean_object* v_nextNeedlePos_140_; uint8_t v_decide_141_; 
lean_del_object(v___x_51_);
v___x_138_ = lean_unsigned_to_nat(1u);
v_nextStackPos_139_ = lean_nat_add(v_stackPos_99_, v___x_138_);
lean_dec(v_stackPos_99_);
v_nextNeedlePos_140_ = lean_nat_add(v_needlePos_100_, v___x_138_);
lean_dec(v_needlePos_100_);
v_decide_141_ = lean_nat_dec_eq(v_nextNeedlePos_140_, v___x_108_);
lean_dec(v___x_108_);
if (v_decide_141_ == 0)
{
lean_object* v___x_143_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 3, v_nextNeedlePos_140_);
lean_ctor_set(v___x_102_, 2, v_nextStackPos_139_);
v___x_143_ = v___x_102_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_needle_97_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_table_98_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_nextStackPos_139_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v_nextNeedlePos_140_);
v___x_143_ = v_reuseFailAlloc_146_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v_currPos_48_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v_a_39_ = v___x_144_;
goto _start;
}
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_147_ = lean_nat_sub(v_nextStackPos_139_, v_nextNeedlePos_140_);
lean_dec(v_nextNeedlePos_140_);
v___x_148_ = l_String_Slice_pos_x21(v___x_37_, v___x_147_);
lean_dec(v___x_147_);
v___x_149_ = l_String_Slice_pos_x21(v___x_37_, v_nextStackPos_139_);
v___x_150_ = lean_unsigned_to_nat(0u);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 3, v___x_150_);
lean_ctor_set(v___x_102_, 2, v_nextStackPos_139_);
v___x_152_ = v___x_102_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_needle_97_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_table_98_);
lean_ctor_set(v_reuseFailAlloc_153_, 2, v_nextStackPos_139_);
lean_ctor_set(v_reuseFailAlloc_153_, 3, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
v_it_60_ = v___x_152_;
v_startPos_61_ = v___x_148_;
v_endPos_62_ = v___x_149_;
goto v___jp_59_;
}
}
}
}
}
}
default: 
{
lean_del_object(v___x_51_);
goto v___jp_73_;
}
}
v___jp_53_:
{
lean_object* v___x_56_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v_it_54_);
v___x_56_ = v___x_51_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v_currPos_48_);
lean_ctor_set(v_reuseFailAlloc_58_, 1, v_it_54_);
v___x_56_ = v_reuseFailAlloc_58_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
v_a_39_ = v___x_56_;
goto _start;
}
}
v___jp_59_:
{
lean_object* v_slice_63_; lean_object* v_startInclusive_64_; lean_object* v_endExclusive_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
v_slice_63_ = l_String_Slice_subslice_x21(v___x_37_, v_currPos_48_, v_startPos_61_);
v_startInclusive_64_ = lean_ctor_get(v_slice_63_, 0);
v_endExclusive_65_ = lean_ctor_get(v_slice_63_, 1);
v_isSharedCheck_72_ = !lean_is_exclusive(v_slice_63_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v_slice_63_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_endExclusive_65_);
lean_inc(v_startInclusive_64_);
lean_dec(v_slice_63_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v_nextIt_70_; 
if (v_isShared_68_ == 0)
{
lean_ctor_set(v___x_67_, 1, v_it_60_);
lean_ctor_set(v___x_67_, 0, v_endPos_62_);
v_nextIt_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_endPos_62_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_it_60_);
v_nextIt_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
v_it_42_ = v_nextIt_70_;
v_startInclusive_43_ = v_startInclusive_64_;
v_endExclusive_44_ = v_endExclusive_65_;
goto v___jp_41_;
}
}
}
v___jp_73_:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(1);
lean_inc(v___x_38_);
v_it_42_ = v___x_74_;
v_startInclusive_43_ = v_currPos_48_;
v_endExclusive_44_ = v___x_38_;
goto v___jp_41_;
}
}
}
else
{
lean_dec(v___x_38_);
lean_dec_ref(v_s_36_);
return v_b_40_;
}
v___jp_41_:
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_inc_ref(v_s_36_);
v___x_45_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_45_, 0, v_s_36_);
lean_ctor_set(v___x_45_, 1, v_startInclusive_43_);
lean_ctor_set(v___x_45_, 2, v_endExclusive_44_);
v___x_46_ = lean_array_push(v_b_40_, v___x_45_);
v_a_39_ = v_it_42_;
v_b_40_ = v___x_46_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object* v_s_156_, lean_object* v___x_157_, lean_object* v___x_158_, lean_object* v_a_159_, lean_object* v_b_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_156_, v___x_157_, v___x_158_, v_a_159_, v_b_160_);
lean_dec_ref(v___x_157_);
return v_res_161_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0));
v___x_164_ = lean_string_utf8_byte_size(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__1);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0));
v___x_168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_165_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField(lean_object* v_s_172_){
_start:
{
uint8_t v___y_174_; lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__4));
v___x_211_ = lean_string_dec_eq(v_s_172_, v___x_210_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; 
v___x_212_ = 1;
v___y_174_ = v___x_212_;
goto v___jp_173_;
}
else
{
uint8_t v___x_213_; 
v___x_213_ = 0;
v___y_174_ = v___x_213_;
goto v___jp_173_;
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_unsigned_to_nat(0u);
v___x_176_ = lean_string_utf8_byte_size(v_s_172_);
lean_inc_ref(v_s_172_);
v___x_177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_177_, 0, v_s_172_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_176_);
if (v___y_174_ == 0)
{
lean_object* v___x_178_; 
lean_dec_ref_known(v___x_177_, 3);
lean_dec_ref(v_s_172_);
v___x_178_ = lean_box(0);
return v___x_178_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_179_ = lean_unsigned_to_nat(2u);
v___x_180_ = l_String_Slice_Pos_prevn(v___x_177_, v___x_176_, v___x_179_);
lean_dec_ref_known(v___x_177_, 3);
lean_inc(v___x_180_);
lean_inc_ref(v_s_172_);
v___x_181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_181_, 0, v_s_172_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
lean_ctor_set(v___x_181_, 2, v___x_176_);
v___x_182_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__2);
v___x_183_ = l_String_Slice_beq(v___x_181_, v___x_182_);
lean_dec_ref_known(v___x_181_, 3);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
lean_dec(v___x_180_);
lean_dec_ref(v_s_172_);
v___x_184_ = lean_box(0);
return v___x_184_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
lean_inc(v___x_180_);
lean_inc_ref(v_s_172_);
v___x_185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_185_, 0, v_s_172_);
lean_ctor_set(v___x_185_, 1, v___x_175_);
lean_ctor_set(v___x_185_, 2, v___x_180_);
v___x_186_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___closed__0);
v___x_187_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__3));
v___x_188_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_172_, v___x_185_, v___x_180_, v___x_186_, v___x_187_);
lean_dec_ref_known(v___x_185_, 3);
v___x_189_ = lean_array_to_list(v___x_188_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(0);
return v___x_190_;
}
else
{
lean_object* v_tail_191_; 
v_tail_191_ = lean_ctor_get(v___x_189_, 1);
lean_inc(v_tail_191_);
if (lean_obj_tag(v_tail_191_) == 0)
{
lean_object* v___x_192_; 
lean_dec_ref_known(v___x_189_, 2);
v___x_192_ = lean_box(0);
return v___x_192_;
}
else
{
lean_object* v_head_193_; lean_object* v_str_194_; lean_object* v_startInclusive_195_; lean_object* v_endExclusive_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_207_; 
v_head_193_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_head_193_);
lean_dec_ref_known(v___x_189_, 2);
v_str_194_ = lean_ctor_get(v_head_193_, 0);
lean_inc_ref(v_str_194_);
v_startInclusive_195_ = lean_ctor_get(v_head_193_, 1);
lean_inc(v_startInclusive_195_);
v_endExclusive_196_ = lean_ctor_get(v_head_193_, 2);
lean_inc(v_endExclusive_196_);
lean_dec(v_head_193_);
v___x_197_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__0___redArg___closed__3);
v___x_198_ = l_String_Slice_intercalate(v___x_197_, v_tail_191_);
v_isSharedCheck_207_ = !lean_is_exclusive(v_tail_191_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; lean_object* v_unused_209_; 
v_unused_208_ = lean_ctor_get(v_tail_191_, 1);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_tail_191_, 0);
lean_dec(v_unused_209_);
v___x_200_ = v_tail_191_;
v_isShared_201_ = v_isSharedCheck_207_;
goto v_resetjp_199_;
}
else
{
lean_dec(v_tail_191_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_207_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_string_utf8_extract_fast(v_str_194_, v_startInclusive_195_, v_endExclusive_196_);
lean_dec(v_endExclusive_196_);
lean_dec(v_startInclusive_195_);
lean_dec_ref(v_str_194_);
if (v_isShared_201_ == 0)
{
lean_ctor_set_tag(v___x_200_, 0);
lean_ctor_set(v___x_200_, 1, v___x_198_);
lean_ctor_set(v___x_200_, 0, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_198_);
v___x_204_ = v_reuseFailAlloc_206_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_205_; 
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(lean_object* v_s_214_, lean_object* v___x_215_, lean_object* v___x_216_, lean_object* v_inst_217_, lean_object* v_R_218_, lean_object* v_a_219_, lean_object* v_b_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_214_, v___x_215_, v___x_216_, v_a_219_, v_b_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object* v_s_222_, lean_object* v___x_223_, lean_object* v___x_224_, lean_object* v_inst_225_, lean_object* v_R_226_, lean_object* v_a_227_, lean_object* v_b_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField_spec__1(v_s_222_, v___x_223_, v___x_224_, v_inst_225_, v_R_226_, v_a_227_, v_b_228_);
lean_dec_ref(v___x_223_);
return v_res_229_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(lean_object* v_s_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_Json_parse(v_s_232_);
if (lean_obj_tag(v___x_233_) == 0)
{
uint8_t v___x_234_; 
lean_dec_ref_known(v___x_233_, 1);
v___x_234_ = 0;
return v___x_234_;
}
else
{
lean_object* v_a_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_a_235_ = lean_ctor_get(v___x_233_, 0);
lean_inc_n(v_a_235_, 2);
lean_dec_ref_known(v___x_233_, 1);
v___x_236_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__0));
v___x_237_ = l_Lean_Json_getObjVal_x3f(v_a_235_, v___x_236_);
if (lean_obj_tag(v___x_237_) == 0)
{
uint8_t v___x_238_; 
lean_dec_ref_known(v___x_237_, 1);
lean_dec(v_a_235_);
v___x_238_ = 0;
return v___x_238_;
}
else
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___closed__1));
v___x_240_ = l_Lean_Json_getObjVal_x3f(v_a_235_, v___x_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
uint8_t v___x_241_; 
lean_dec_ref_known(v___x_240_, 1);
v___x_241_ = 0;
return v___x_241_;
}
else
{
uint8_t v___x_242_; 
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = 1;
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request___boxed(lean_object* v_s_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_s_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__1));
v___x_249_ = lean_mk_io_user_error(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__3));
v___x_252_ = lean_mk_io_user_error(v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(lean_object* v_h_253_){
_start:
{
lean_object* v_getLine_255_; lean_object* v___x_256_; 
v_getLine_255_ = lean_ctor_get(v_h_253_, 3);
lean_inc_ref(v_getLine_255_);
v___x_256_ = lean_apply_1(v_getLine_255_, lean_box(0));
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_301_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_301_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_301_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_301_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_261_ = lean_string_utf8_byte_size(v_a_257_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_nat_dec_eq(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField___closed__0));
v___x_265_ = lean_string_dec_eq(v_a_257_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; 
lean_inc(v_a_257_);
v___x_266_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_parseHeaderField(v_a_257_);
if (lean_obj_tag(v___x_266_) == 0)
{
uint8_t v___x_267_; 
lean_dec_ref(v_h_253_);
lean_inc(v_a_257_);
v___x_267_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_isLean3Request(v_a_257_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__0));
v___x_269_ = l_String_quote(v_a_257_);
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = l_Std_Format_defWidth;
v___x_272_ = l_Std_Format_pretty(v___x_270_, v___x_271_, v___x_262_, v___x_262_);
v___x_273_ = lean_string_append(v___x_268_, v___x_272_);
lean_dec_ref(v___x_272_);
v___x_274_ = lean_mk_io_user_error(v___x_273_);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 1);
lean_ctor_set(v___x_259_, 0, v___x_274_);
v___x_276_ = v___x_259_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_280_; 
lean_dec(v_a_257_);
v___x_278_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__2);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 1);
lean_ctor_set(v___x_259_, 0, v___x_278_);
v___x_280_ = v___x_259_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
else
{
lean_object* v_val_282_; lean_object* v___x_283_; 
lean_del_object(v___x_259_);
lean_dec(v_a_257_);
v_val_282_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_val_282_);
lean_dec_ref_known(v___x_266_, 1);
v___x_283_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_253_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_292_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_292_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_292_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_290_; 
v___x_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_288_, 0, v_val_282_);
lean_ctor_set(v___x_288_, 1, v_a_284_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_288_);
v___x_290_ = v___x_286_;
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
lean_dec(v_val_282_);
return v___x_283_;
}
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_295_; 
lean_dec(v_a_257_);
lean_dec_ref(v_h_253_);
v___x_293_ = lean_box(0);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_293_);
v___x_295_ = v___x_259_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
else
{
lean_object* v___x_297_; lean_object* v___x_299_; 
lean_dec(v_a_257_);
lean_dec_ref(v_h_253_);
v___x_297_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4, &l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4_once, _init_l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___closed__4);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 1);
lean_ctor_set(v___x_259_, 0, v___x_297_);
v___x_299_ = v___x_259_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref(v_h_253_);
v_a_302_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_256_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_256_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields___boxed(lean_object* v_h_310_, lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object* v_x_313_, lean_object* v_x_314_){
_start:
{
if (lean_obj_tag(v_x_314_) == 0)
{
lean_object* v___x_315_; 
v___x_315_ = lean_box(0);
return v___x_315_;
}
else
{
lean_object* v_head_316_; lean_object* v_tail_317_; lean_object* v_fst_318_; lean_object* v_snd_319_; uint8_t v___x_320_; 
v_head_316_ = lean_ctor_get(v_x_314_, 0);
v_tail_317_ = lean_ctor_get(v_x_314_, 1);
v_fst_318_ = lean_ctor_get(v_head_316_, 0);
v_snd_319_ = lean_ctor_get(v_head_316_, 1);
v___x_320_ = lean_string_dec_eq(v_x_313_, v_fst_318_);
if (v___x_320_ == 0)
{
v_x_314_ = v_tail_317_;
goto _start;
}
else
{
lean_object* v___x_322_; 
lean_inc(v_snd_319_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v_snd_319_);
return v___x_322_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_323_, v_x_324_);
lean_dec(v_x_324_);
lean_dec_ref(v_x_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object* v_x_329_, lean_object* v_x_330_){
_start:
{
if (lean_obj_tag(v_x_330_) == 0)
{
return v_x_329_;
}
else
{
lean_object* v_head_331_; lean_object* v_tail_332_; lean_object* v_fst_333_; lean_object* v_snd_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_head_331_ = lean_ctor_get(v_x_330_, 0);
v_tail_332_ = lean_ctor_get(v_x_330_, 1);
v_fst_333_ = lean_ctor_get(v_head_331_, 0);
v_snd_334_ = lean_ctor_get(v_head_331_, 1);
v___x_335_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_336_ = lean_string_append(v_x_329_, v___x_335_);
v___x_337_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_338_ = lean_string_append(v___x_337_, v_fst_333_);
v___x_339_ = lean_string_append(v___x_338_, v___x_335_);
v___x_340_ = lean_string_append(v___x_339_, v_snd_334_);
v___x_341_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_342_ = lean_string_append(v___x_340_, v___x_341_);
v___x_343_ = lean_string_append(v___x_336_, v___x_342_);
lean_dec_ref(v___x_342_);
v_x_329_ = v___x_343_;
v_x_330_ = v_tail_332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(v_x_345_, v_x_346_);
lean_dec(v_x_346_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(lean_object* v_x_351_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v___x_352_; 
v___x_352_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__0));
return v___x_352_;
}
else
{
lean_object* v_tail_353_; 
v_tail_353_ = lean_ctor_get(v_x_351_, 1);
if (lean_obj_tag(v_tail_353_) == 0)
{
lean_object* v_head_354_; lean_object* v_fst_355_; lean_object* v_snd_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v_head_354_ = lean_ctor_get(v_x_351_, 0);
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
v___x_366_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__2));
v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
return v___x_367_;
}
else
{
lean_object* v_head_368_; lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint32_t v___x_381_; lean_object* v___x_382_; 
v_head_368_ = lean_ctor_get(v_x_351_, 0);
v_fst_369_ = lean_ctor_get(v_head_368_, 0);
v_snd_370_ = lean_ctor_get(v_head_368_, 1);
v___x_371_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_372_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_373_ = lean_string_append(v___x_372_, v_fst_369_);
v___x_374_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_375_ = lean_string_append(v___x_373_, v___x_374_);
v___x_376_ = lean_string_append(v___x_375_, v_snd_370_);
v___x_377_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_378_ = lean_string_append(v___x_376_, v___x_377_);
v___x_379_ = lean_string_append(v___x_371_, v___x_378_);
lean_dec_ref(v___x_378_);
v___x_380_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1_spec__1(v___x_379_, v_tail_353_);
v___x_381_ = 93;
v___x_382_ = lean_string_push(v___x_380_, v___x_381_);
return v___x_382_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object* v_x_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(v_x_383_);
lean_dec(v_x_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(lean_object* v_h_389_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readHeaderFields(v_h_389_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_422_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_422_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_422_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_422_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__0));
v___x_397_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v___x_396_, v_a_392_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_398_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__1));
v___x_399_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__1(v_a_392_);
lean_dec(v_a_392_);
v___x_400_ = lean_string_append(v___x_398_, v___x_399_);
lean_dec_ref(v___x_399_);
v___x_401_ = lean_mk_io_user_error(v___x_400_);
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 1);
lean_ctor_set(v___x_394_, 0, v___x_401_);
v___x_403_ = v___x_394_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
else
{
lean_object* v_val_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v_a_392_);
v_val_405_ = lean_ctor_get(v___x_397_, 0);
lean_inc_n(v_val_405_, 2);
lean_dec_ref_known(v___x_397_, 1);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_string_utf8_byte_size(v_val_405_);
v___x_408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_408_, 0, v_val_405_);
lean_ctor_set(v___x_408_, 1, v___x_406_);
lean_ctor_set(v___x_408_, 2, v___x_407_);
v___x_409_ = l_String_Slice_toNat_x3f(v___x_408_);
lean_dec_ref_known(v___x_408_, 3);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_410_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__2));
v___x_411_ = lean_string_append(v___x_410_, v_val_405_);
lean_dec(v_val_405_);
v___x_412_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___closed__3));
v___x_413_ = lean_string_append(v___x_411_, v___x_412_);
v___x_414_ = lean_mk_io_user_error(v___x_413_);
if (v_isShared_395_ == 0)
{
lean_ctor_set_tag(v___x_394_, 1);
lean_ctor_set(v___x_394_, 0, v___x_414_);
v___x_416_ = v___x_394_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
lean_object* v_val_418_; lean_object* v___x_420_; 
lean_dec(v_val_405_);
v_val_418_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v___x_409_, 1);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v_val_418_);
v___x_420_ = v___x_394_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_val_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_a_423_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_391_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_391_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader___boxed(lean_object* v_h_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0(lean_object* v_00_u03b2_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object* v_00_u03b2_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader_spec__0(v_00_u03b2_438_, v_x_439_, v_x_440_);
lean_dec(v_x_440_);
lean_dec_ref(v_x_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage(lean_object* v_h_443_){
_start:
{
lean_object* v_a_446_; lean_object* v___x_452_; 
lean_inc_ref(v_h_443_);
v___x_452_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_443_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_454_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v___x_454_ = l_Lean_IO_FS_Stream_readMessage(v_h_443_, v_a_453_);
lean_dec(v_a_453_);
if (lean_obj_tag(v___x_454_) == 0)
{
return v___x_454_;
}
else
{
lean_object* v_a_455_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v_a_446_ = v_a_455_;
goto v___jp_445_;
}
}
else
{
lean_object* v_a_456_; 
lean_dec_ref(v_h_443_);
v_a_456_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_452_, 1);
v_a_446_ = v_a_456_;
goto v___jp_445_;
}
v___jp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_447_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspMessage___closed__0));
v___x_448_ = lean_io_error_to_string(v_a_446_);
v___x_449_ = lean_string_append(v___x_447_, v___x_448_);
lean_dec_ref(v___x_448_);
v___x_450_ = lean_mk_io_user_error(v___x_449_);
v___x_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessage___boxed(lean_object* v_h_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_IO_FS_Stream_readLspMessage(v_h_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString(lean_object* v_h_460_){
_start:
{
lean_object* v_a_463_; lean_object* v___x_469_; 
lean_inc_ref(v_h_460_);
v___x_469_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_460_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_471_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = l_Lean_IO_FS_Stream_readUTF8(v_h_460_, v_a_470_);
lean_dec(v_a_470_);
if (lean_obj_tag(v___x_471_) == 0)
{
return v___x_471_;
}
else
{
lean_object* v_a_472_; 
v_a_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_a_472_);
lean_dec_ref_known(v___x_471_, 1);
v_a_463_ = v_a_472_;
goto v___jp_462_;
}
}
else
{
lean_object* v_a_473_; 
lean_dec_ref(v_h_460_);
v_a_473_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_469_, 1);
v_a_463_ = v_a_473_;
goto v___jp_462_;
}
v___jp_462_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_464_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspMessage___closed__0));
v___x_465_ = lean_io_error_to_string(v_a_463_);
v___x_466_ = lean_string_append(v___x_464_, v___x_465_);
lean_dec_ref(v___x_465_);
v___x_467_ = lean_mk_io_user_error(v___x_466_);
v___x_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspMessageAsString___boxed(lean_object* v_h_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_IO_FS_Stream_readLspMessageAsString(v_h_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg(lean_object* v_h_478_, lean_object* v_expectedMethod_479_, lean_object* v_inst_480_){
_start:
{
lean_object* v_a_483_; lean_object* v___x_489_; 
lean_inc_ref(v_h_478_);
v___x_489_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_478_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_491_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
v___x_491_ = l_Lean_IO_FS_Stream_readRequestAs___redArg(v_h_478_, v_a_490_, v_expectedMethod_479_, v_inst_480_);
lean_dec(v_a_490_);
if (lean_obj_tag(v___x_491_) == 0)
{
return v___x_491_;
}
else
{
lean_object* v_a_492_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v_a_483_ = v_a_492_;
goto v___jp_482_;
}
}
else
{
lean_object* v_a_493_; 
lean_dec_ref(v_inst_480_);
lean_dec_ref(v_expectedMethod_479_);
lean_dec_ref(v_h_478_);
v_a_493_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_493_);
lean_dec_ref_known(v___x_489_, 1);
v_a_483_ = v_a_493_;
goto v___jp_482_;
}
v___jp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_484_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspRequestAs___redArg___closed__0));
v___x_485_ = lean_io_error_to_string(v_a_483_);
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
lean_dec_ref(v___x_485_);
v___x_487_ = lean_mk_io_user_error(v___x_486_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object* v_h_494_, lean_object* v_expectedMethod_495_, lean_object* v_inst_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_494_, v_expectedMethod_495_, v_inst_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs(lean_object* v_h_499_, lean_object* v_expectedMethod_500_, lean_object* v_00_u03b1_501_, lean_object* v_inst_502_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_IO_FS_Stream_readLspRequestAs___redArg(v_h_499_, v_expectedMethod_500_, v_inst_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspRequestAs___boxed(lean_object* v_h_505_, lean_object* v_expectedMethod_506_, lean_object* v_00_u03b1_507_, lean_object* v_inst_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_IO_FS_Stream_readLspRequestAs(v_h_505_, v_expectedMethod_506_, v_00_u03b1_507_, v_inst_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(lean_object* v_h_512_, lean_object* v_expectedMethod_513_, lean_object* v_inst_514_){
_start:
{
lean_object* v_a_517_; lean_object* v___x_523_; 
lean_inc_ref(v_h_512_);
v___x_523_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_512_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = l_Lean_IO_FS_Stream_readNotificationAs___redArg(v_h_512_, v_a_524_, v_expectedMethod_513_, v_inst_514_);
lean_dec(v_a_524_);
if (lean_obj_tag(v___x_525_) == 0)
{
return v___x_525_;
}
else
{
lean_object* v_a_526_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v_a_517_ = v_a_526_;
goto v___jp_516_;
}
}
else
{
lean_object* v_a_527_; 
lean_dec_ref(v_inst_514_);
lean_dec_ref(v_expectedMethod_513_);
lean_dec_ref(v_h_512_);
v_a_527_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_523_, 1);
v_a_517_ = v_a_527_;
goto v___jp_516_;
}
v___jp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_518_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___closed__0));
v___x_519_ = lean_io_error_to_string(v_a_517_);
v___x_520_ = lean_string_append(v___x_518_, v___x_519_);
lean_dec_ref(v___x_519_);
v___x_521_ = lean_mk_io_user_error(v___x_520_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object* v_h_528_, lean_object* v_expectedMethod_529_, lean_object* v_inst_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_528_, v_expectedMethod_529_, v_inst_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs(lean_object* v_h_533_, lean_object* v_expectedMethod_534_, lean_object* v_00_u03b1_535_, lean_object* v_inst_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_IO_FS_Stream_readLspNotificationAs___redArg(v_h_533_, v_expectedMethod_534_, v_inst_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspNotificationAs___boxed(lean_object* v_h_539_, lean_object* v_expectedMethod_540_, lean_object* v_00_u03b1_541_, lean_object* v_inst_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_IO_FS_Stream_readLspNotificationAs(v_h_539_, v_expectedMethod_540_, v_00_u03b1_541_, v_inst_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg(lean_object* v_h_546_, lean_object* v_expectedID_547_, lean_object* v_inst_548_){
_start:
{
lean_object* v_a_551_; lean_object* v___x_557_; 
lean_inc_ref(v_h_546_);
v___x_557_ = l___private_Lean_Data_Lsp_Communication_0__Lean_IO_FS_Stream_readLspHeader(v_h_546_);
if (lean_obj_tag(v___x_557_) == 0)
{
lean_object* v_a_558_; lean_object* v___x_559_; 
v_a_558_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v___x_557_, 1);
v___x_559_ = l_Lean_IO_FS_Stream_readResponseAs___redArg(v_h_546_, v_a_558_, v_expectedID_547_, v_inst_548_);
lean_dec(v_a_558_);
if (lean_obj_tag(v___x_559_) == 0)
{
return v___x_559_;
}
else
{
lean_object* v_a_560_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_a_560_);
lean_dec_ref_known(v___x_559_, 1);
v_a_551_ = v_a_560_;
goto v___jp_550_;
}
}
else
{
lean_object* v_a_561_; 
lean_dec_ref(v_inst_548_);
lean_dec(v_expectedID_547_);
lean_dec_ref(v_h_546_);
v_a_561_ = lean_ctor_get(v___x_557_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v___x_557_, 1);
v_a_551_ = v_a_561_;
goto v___jp_550_;
}
v___jp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_552_ = ((lean_object*)(l_Lean_IO_FS_Stream_readLspResponseAs___redArg___closed__0));
v___x_553_ = lean_io_error_to_string(v_a_551_);
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = lean_mk_io_user_error(v___x_554_);
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object* v_h_562_, lean_object* v_expectedID_563_, lean_object* v_inst_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_562_, v_expectedID_563_, v_inst_564_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs(lean_object* v_h_567_, lean_object* v_expectedID_568_, lean_object* v_00_u03b1_569_, lean_object* v_inst_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_IO_FS_Stream_readLspResponseAs___redArg(v_h_567_, v_expectedID_568_, v_inst_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_readLspResponseAs___boxed(lean_object* v_h_573_, lean_object* v_expectedID_574_, lean_object* v_00_u03b1_575_, lean_object* v_inst_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_IO_FS_Stream_readLspResponseAs(v_h_573_, v_expectedID_574_, v_00_u03b1_575_, v_inst_576_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage(lean_object* v_h_581_, lean_object* v_msg_582_){
_start:
{
lean_object* v_flush_584_; lean_object* v_putStr_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v_header_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v_flush_584_ = lean_ctor_get(v_h_581_, 0);
lean_inc_ref(v_flush_584_);
v_putStr_585_ = lean_ctor_get(v_h_581_, 4);
lean_inc_ref(v_putStr_585_);
lean_dec_ref(v_h_581_);
v___x_586_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__0));
v___x_587_ = lean_string_utf8_byte_size(v_msg_582_);
v___x_588_ = l_Nat_reprFast(v___x_587_);
v___x_589_ = lean_string_append(v___x_586_, v___x_588_);
lean_dec_ref(v___x_588_);
v___x_590_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeSerializedLspMessage___closed__1));
v_header_591_ = lean_string_append(v___x_589_, v___x_590_);
v___x_592_ = lean_string_append(v_header_591_, v_msg_582_);
v___x_593_ = lean_apply_2(v_putStr_585_, v___x_592_, lean_box(0));
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v___x_594_; 
lean_dec_ref_known(v___x_593_, 1);
v___x_594_ = lean_apply_1(v_flush_584_, lean_box(0));
return v___x_594_;
}
else
{
lean_dec_ref(v_flush_584_);
return v___x_593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object* v_h_595_, lean_object* v_msg_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_IO_FS_Stream_writeSerializedLspMessage(v_h_595_, v_msg_596_);
lean_dec_ref(v_msg_596_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(lean_object* v_k_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_600_) == 0)
{
lean_object* v___x_601_; 
lean_dec_ref(v_k_599_);
v___x_601_ = lean_box(0);
return v___x_601_;
}
else
{
lean_object* v_val_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_val_602_ = lean_ctor_get(v_x_600_, 0);
lean_inc(v_val_602_);
lean_dec_ref_known(v_x_600_, 1);
v___x_603_ = l_Lean_Json_Structured_toJson(v_val_602_);
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v_k_599_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_box(0);
v___x_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
return v___x_606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(lean_object* v_k_607_, lean_object* v_x_608_){
_start:
{
if (lean_obj_tag(v_x_608_) == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_k_607_);
v___x_609_ = lean_box(0);
return v___x_609_;
}
else
{
lean_object* v_val_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v_val_610_ = lean_ctor_get(v_x_608_, 0);
lean_inc(v_val_610_);
v___x_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_611_, 0, v_k_607_);
lean_ctor_set(v___x_611_, 1, v_val_610_);
v___x_612_ = lean_box(0);
v___x_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1___boxed(lean_object* v_k_614_, lean_object* v_x_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(v_k_614_, v_x_615_);
lean_dec(v_x_615_);
return v_res_616_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__12(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = lean_unsigned_to_nat(32700u);
v___x_633_ = lean_nat_to_int(v___x_632_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__13(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__12, &l_Lean_IO_FS_Stream_writeLspMessage___closed__12_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__12);
v___x_635_ = lean_int_neg(v___x_634_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__14(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__13, &l_Lean_IO_FS_Stream_writeLspMessage___closed__13_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__13);
v___x_637_ = l_Lean_JsonNumber_fromInt(v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__15(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__14, &l_Lean_IO_FS_Stream_writeLspMessage___closed__14_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__14);
v___x_639_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__16(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = lean_unsigned_to_nat(32600u);
v___x_641_ = lean_nat_to_int(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__17(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__16, &l_Lean_IO_FS_Stream_writeLspMessage___closed__16_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__16);
v___x_643_ = lean_int_neg(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__18(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__17, &l_Lean_IO_FS_Stream_writeLspMessage___closed__17_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__17);
v___x_645_ = l_Lean_JsonNumber_fromInt(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__19(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__18, &l_Lean_IO_FS_Stream_writeLspMessage___closed__18_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__18);
v___x_647_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__20(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(32601u);
v___x_649_ = lean_nat_to_int(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__21(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__20, &l_Lean_IO_FS_Stream_writeLspMessage___closed__20_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__20);
v___x_651_ = lean_int_neg(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__22(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__21, &l_Lean_IO_FS_Stream_writeLspMessage___closed__21_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__21);
v___x_653_ = l_Lean_JsonNumber_fromInt(v___x_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__23(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__22, &l_Lean_IO_FS_Stream_writeLspMessage___closed__22_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__22);
v___x_655_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__24(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = lean_unsigned_to_nat(32602u);
v___x_657_ = lean_nat_to_int(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__25(void){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__24, &l_Lean_IO_FS_Stream_writeLspMessage___closed__24_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__24);
v___x_659_ = lean_int_neg(v___x_658_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__26(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__25, &l_Lean_IO_FS_Stream_writeLspMessage___closed__25_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__25);
v___x_661_ = l_Lean_JsonNumber_fromInt(v___x_660_);
return v___x_661_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__27(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__26, &l_Lean_IO_FS_Stream_writeLspMessage___closed__26_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__26);
v___x_663_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__28(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(32603u);
v___x_665_ = lean_nat_to_int(v___x_664_);
return v___x_665_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__29(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__28, &l_Lean_IO_FS_Stream_writeLspMessage___closed__28_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__28);
v___x_667_ = lean_int_neg(v___x_666_);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__30(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__29, &l_Lean_IO_FS_Stream_writeLspMessage___closed__29_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__29);
v___x_669_ = l_Lean_JsonNumber_fromInt(v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__31(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__30, &l_Lean_IO_FS_Stream_writeLspMessage___closed__30_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__30);
v___x_671_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__32(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_unsigned_to_nat(32002u);
v___x_673_ = lean_nat_to_int(v___x_672_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__33(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__32, &l_Lean_IO_FS_Stream_writeLspMessage___closed__32_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__32);
v___x_675_ = lean_int_neg(v___x_674_);
return v___x_675_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__34(void){
_start:
{
lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_676_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__33, &l_Lean_IO_FS_Stream_writeLspMessage___closed__33_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__33);
v___x_677_ = l_Lean_JsonNumber_fromInt(v___x_676_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__35(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__34, &l_Lean_IO_FS_Stream_writeLspMessage___closed__34_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__34);
v___x_679_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__36(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_unsigned_to_nat(32001u);
v___x_681_ = lean_nat_to_int(v___x_680_);
return v___x_681_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__37(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__36, &l_Lean_IO_FS_Stream_writeLspMessage___closed__36_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__36);
v___x_683_ = lean_int_neg(v___x_682_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__38(void){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__37, &l_Lean_IO_FS_Stream_writeLspMessage___closed__37_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__37);
v___x_685_ = l_Lean_JsonNumber_fromInt(v___x_684_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__39(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__38, &l_Lean_IO_FS_Stream_writeLspMessage___closed__38_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__38);
v___x_687_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__40(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_unsigned_to_nat(32801u);
v___x_689_ = lean_nat_to_int(v___x_688_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__41(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__40, &l_Lean_IO_FS_Stream_writeLspMessage___closed__40_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__40);
v___x_691_ = lean_int_neg(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__42(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__41, &l_Lean_IO_FS_Stream_writeLspMessage___closed__41_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__41);
v___x_693_ = l_Lean_JsonNumber_fromInt(v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__43(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__42, &l_Lean_IO_FS_Stream_writeLspMessage___closed__42_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__42);
v___x_695_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__44(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_unsigned_to_nat(32800u);
v___x_697_ = lean_nat_to_int(v___x_696_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__45(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__44, &l_Lean_IO_FS_Stream_writeLspMessage___closed__44_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__44);
v___x_699_ = lean_int_neg(v___x_698_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__46(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__45, &l_Lean_IO_FS_Stream_writeLspMessage___closed__45_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__45);
v___x_701_ = l_Lean_JsonNumber_fromInt(v___x_700_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__47(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__46, &l_Lean_IO_FS_Stream_writeLspMessage___closed__46_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__46);
v___x_703_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__48(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_unsigned_to_nat(32900u);
v___x_705_ = lean_nat_to_int(v___x_704_);
return v___x_705_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__49(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__48, &l_Lean_IO_FS_Stream_writeLspMessage___closed__48_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__48);
v___x_707_ = lean_int_neg(v___x_706_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__50(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__49, &l_Lean_IO_FS_Stream_writeLspMessage___closed__49_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__49);
v___x_709_ = l_Lean_JsonNumber_fromInt(v___x_708_);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__51(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__50, &l_Lean_IO_FS_Stream_writeLspMessage___closed__50_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__50);
v___x_711_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__52(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = lean_unsigned_to_nat(32901u);
v___x_713_ = lean_nat_to_int(v___x_712_);
return v___x_713_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__53(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__52, &l_Lean_IO_FS_Stream_writeLspMessage___closed__52_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__52);
v___x_715_ = lean_int_neg(v___x_714_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__54(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__53, &l_Lean_IO_FS_Stream_writeLspMessage___closed__53_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__53);
v___x_717_ = l_Lean_JsonNumber_fromInt(v___x_716_);
return v___x_717_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__55(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__54, &l_Lean_IO_FS_Stream_writeLspMessage___closed__54_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__54);
v___x_719_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__56(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_unsigned_to_nat(32902u);
v___x_721_ = lean_nat_to_int(v___x_720_);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__57(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__56, &l_Lean_IO_FS_Stream_writeLspMessage___closed__56_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__56);
v___x_723_ = lean_int_neg(v___x_722_);
return v___x_723_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__58(void){
_start:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__57, &l_Lean_IO_FS_Stream_writeLspMessage___closed__57_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__57);
v___x_725_ = l_Lean_JsonNumber_fromInt(v___x_724_);
return v___x_725_;
}
}
static lean_object* _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__59(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__58, &l_Lean_IO_FS_Stream_writeLspMessage___closed__58_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__58);
v___x_727_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage(lean_object* v_h_728_, lean_object* v_msg_729_){
_start:
{
lean_object* v___x_731_; lean_object* v___y_733_; 
v___x_731_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__3));
switch(lean_obj_tag(v_msg_729_))
{
case 0:
{
lean_object* v_id_738_; lean_object* v_method_739_; lean_object* v_params_x3f_740_; lean_object* v___x_741_; lean_object* v___y_743_; 
v_id_738_ = lean_ctor_get(v_msg_729_, 0);
lean_inc(v_id_738_);
v_method_739_ = lean_ctor_get(v_msg_729_, 1);
lean_inc_ref(v_method_739_);
v_params_x3f_740_ = lean_ctor_get(v_msg_729_, 2);
lean_inc(v_params_x3f_740_);
lean_dec_ref_known(v_msg_729_, 3);
v___x_741_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_738_))
{
case 0:
{
lean_object* v_s_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
v_s_754_ = lean_ctor_get(v_id_738_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v_id_738_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v_id_738_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_s_754_);
lean_dec(v_id_738_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set_tag(v___x_756_, 3);
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_s_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
v___y_743_ = v___x_759_;
goto v___jp_742_;
}
}
}
case 1:
{
lean_object* v_n_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_n_762_ = lean_ctor_get(v_id_738_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v_id_738_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v_id_738_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_n_762_);
lean_dec(v_id_738_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 2);
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_n_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
v___y_743_ = v___x_767_;
goto v___jp_742_;
}
}
}
default: 
{
lean_object* v___x_770_; 
v___x_770_ = lean_box(0);
v___y_743_ = v___x_770_;
goto v___jp_742_;
}
}
v___jp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_741_);
lean_ctor_set(v___x_744_, 1, v___y_743_);
v___x_745_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__5));
v___x_746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_746_, 0, v_method_739_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_box(0);
v___x_749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_747_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_744_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__6));
v___x_752_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(v___x_751_, v_params_x3f_740_);
v___x_753_ = l_List_appendTR___redArg(v___x_750_, v___x_752_);
v___y_733_ = v___x_753_;
goto v___jp_732_;
}
}
case 1:
{
lean_object* v_method_771_; lean_object* v_params_x3f_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_784_; 
v_method_771_ = lean_ctor_get(v_msg_729_, 0);
v_params_x3f_772_ = lean_ctor_get(v_msg_729_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_msg_729_);
if (v_isSharedCheck_784_ == 0)
{
v___x_774_ = v_msg_729_;
v_isShared_775_ = v_isSharedCheck_784_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_params_x3f_772_);
lean_inc(v_method_771_);
lean_dec(v_msg_729_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_784_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_779_; 
v___x_776_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__5));
v___x_777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_777_, 0, v_method_771_);
if (v_isShared_775_ == 0)
{
lean_ctor_set_tag(v___x_774_, 0);
lean_ctor_set(v___x_774_, 1, v___x_777_);
lean_ctor_set(v___x_774_, 0, v___x_776_);
v___x_779_ = v___x_774_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_777_);
v___x_779_ = v_reuseFailAlloc_783_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__6));
v___x_781_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__0(v___x_780_, v_params_x3f_772_);
v___x_782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_779_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___y_733_ = v___x_782_;
goto v___jp_732_;
}
}
}
case 2:
{
lean_object* v_id_785_; lean_object* v_result_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_818_; 
v_id_785_ = lean_ctor_get(v_msg_729_, 0);
v_result_786_ = lean_ctor_get(v_msg_729_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_msg_729_);
if (v_isSharedCheck_818_ == 0)
{
v___x_788_ = v_msg_729_;
v_isShared_789_ = v_isSharedCheck_818_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_result_786_);
lean_inc(v_id_785_);
lean_dec(v_msg_729_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_818_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___y_792_; 
v___x_790_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_785_))
{
case 0:
{
lean_object* v_s_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v_s_801_ = lean_ctor_get(v_id_785_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v_id_785_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v_id_785_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_s_801_);
lean_dec(v_id_785_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 3);
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_s_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v___y_792_ = v___x_806_;
goto v___jp_791_;
}
}
}
case 1:
{
lean_object* v_n_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
v_n_809_ = lean_ctor_get(v_id_785_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_id_785_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v_id_785_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_n_809_);
lean_dec(v_id_785_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set_tag(v___x_811_, 2);
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_n_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
v___y_792_ = v___x_814_;
goto v___jp_791_;
}
}
}
default: 
{
lean_object* v___x_817_; 
v___x_817_ = lean_box(0);
v___y_792_ = v___x_817_;
goto v___jp_791_;
}
}
v___jp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 0);
lean_ctor_set(v___x_788_, 1, v___y_792_);
lean_ctor_set(v___x_788_, 0, v___x_790_);
v___x_794_ = v___x_788_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_800_, 1, v___y_792_);
v___x_794_ = v_reuseFailAlloc_800_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_795_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__7));
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v_result_786_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_794_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___y_733_ = v___x_799_;
goto v___jp_732_;
}
}
}
}
default: 
{
lean_object* v_id_819_; uint8_t v_code_820_; lean_object* v_message_821_; lean_object* v_data_x3f_822_; lean_object* v___y_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___x_842_; lean_object* v___y_844_; 
v_id_819_ = lean_ctor_get(v_msg_729_, 0);
lean_inc(v_id_819_);
v_code_820_ = lean_ctor_get_uint8(v_msg_729_, sizeof(void*)*3);
v_message_821_ = lean_ctor_get(v_msg_729_, 1);
lean_inc_ref(v_message_821_);
v_data_x3f_822_ = lean_ctor_get(v_msg_729_, 2);
lean_inc(v_data_x3f_822_);
lean_dec_ref_known(v_msg_729_, 3);
v___x_842_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_819_))
{
case 0:
{
lean_object* v_s_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_s_860_ = lean_ctor_get(v_id_819_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v_id_819_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v_id_819_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_s_860_);
lean_dec(v_id_819_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 3);
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_s_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
v___y_844_ = v___x_865_;
goto v___jp_843_;
}
}
}
case 1:
{
lean_object* v_n_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_n_868_ = lean_ctor_get(v_id_819_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v_id_819_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v_id_819_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_n_868_);
lean_dec(v_id_819_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
lean_ctor_set_tag(v___x_870_, 2);
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_n_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
v___y_844_ = v___x_873_;
goto v___jp_843_;
}
}
}
default: 
{
lean_object* v___x_876_; 
v___x_876_ = lean_box(0);
v___y_844_ = v___x_876_;
goto v___jp_843_;
}
}
v___jp_823_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
lean_inc(v___y_827_);
lean_inc_ref(v___y_825_);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___y_825_);
lean_ctor_set(v___x_828_, 1, v___y_827_);
v___x_829_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__8));
v___x_830_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_830_, 0, v_message_821_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_box(0);
v___x_833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_828_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__9));
v___x_836_ = l_Lean_Json_opt___at___00Lean_IO_FS_Stream_writeLspMessage_spec__1(v___x_835_, v_data_x3f_822_);
lean_dec(v_data_x3f_822_);
v___x_837_ = l_List_appendTR___redArg(v___x_834_, v___x_836_);
v___x_838_ = l_Lean_Json_mkObj(v___x_837_);
lean_dec(v___x_837_);
lean_inc_ref(v___y_826_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___y_826_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
lean_ctor_set(v___x_840_, 1, v___x_832_);
v___x_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_841_, 0, v___y_824_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___y_733_ = v___x_841_;
goto v___jp_732_;
}
v___jp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_842_);
lean_ctor_set(v___x_845_, 1, v___y_844_);
v___x_846_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__10));
v___x_847_ = ((lean_object*)(l_Lean_IO_FS_Stream_writeLspMessage___closed__11));
switch(v_code_820_)
{
case 0:
{
lean_object* v___x_848_; 
v___x_848_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__15, &l_Lean_IO_FS_Stream_writeLspMessage___closed__15_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__15);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_848_;
goto v___jp_823_;
}
case 1:
{
lean_object* v___x_849_; 
v___x_849_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__19, &l_Lean_IO_FS_Stream_writeLspMessage___closed__19_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__19);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_849_;
goto v___jp_823_;
}
case 2:
{
lean_object* v___x_850_; 
v___x_850_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__23, &l_Lean_IO_FS_Stream_writeLspMessage___closed__23_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__23);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_850_;
goto v___jp_823_;
}
case 3:
{
lean_object* v___x_851_; 
v___x_851_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__27, &l_Lean_IO_FS_Stream_writeLspMessage___closed__27_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__27);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_851_;
goto v___jp_823_;
}
case 4:
{
lean_object* v___x_852_; 
v___x_852_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__31, &l_Lean_IO_FS_Stream_writeLspMessage___closed__31_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__31);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_852_;
goto v___jp_823_;
}
case 5:
{
lean_object* v___x_853_; 
v___x_853_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__35, &l_Lean_IO_FS_Stream_writeLspMessage___closed__35_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__35);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_853_;
goto v___jp_823_;
}
case 6:
{
lean_object* v___x_854_; 
v___x_854_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__39, &l_Lean_IO_FS_Stream_writeLspMessage___closed__39_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__39);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_854_;
goto v___jp_823_;
}
case 7:
{
lean_object* v___x_855_; 
v___x_855_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__43, &l_Lean_IO_FS_Stream_writeLspMessage___closed__43_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__43);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_855_;
goto v___jp_823_;
}
case 8:
{
lean_object* v___x_856_; 
v___x_856_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__47, &l_Lean_IO_FS_Stream_writeLspMessage___closed__47_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__47);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_856_;
goto v___jp_823_;
}
case 9:
{
lean_object* v___x_857_; 
v___x_857_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__51, &l_Lean_IO_FS_Stream_writeLspMessage___closed__51_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__51);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_857_;
goto v___jp_823_;
}
case 10:
{
lean_object* v___x_858_; 
v___x_858_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__55, &l_Lean_IO_FS_Stream_writeLspMessage___closed__55_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__55);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_858_;
goto v___jp_823_;
}
default: 
{
lean_object* v___x_859_; 
v___x_859_ = lean_obj_once(&l_Lean_IO_FS_Stream_writeLspMessage___closed__59, &l_Lean_IO_FS_Stream_writeLspMessage___closed__59_once, _init_l_Lean_IO_FS_Stream_writeLspMessage___closed__59);
v___y_824_ = v___x_845_;
v___y_825_ = v___x_847_;
v___y_826_ = v___x_846_;
v___y_827_ = v___x_859_;
goto v___jp_823_;
}
}
}
}
}
v___jp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_731_);
lean_ctor_set(v___x_734_, 1, v___y_733_);
v___x_735_ = l_Lean_Json_mkObj(v___x_734_);
lean_dec_ref_known(v___x_734_, 2);
v___x_736_ = l_Lean_Json_compress(v___x_735_);
v___x_737_ = l_Lean_IO_FS_Stream_writeSerializedLspMessage(v_h_728_, v___x_736_);
lean_dec_ref(v___x_736_);
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspMessage___boxed(lean_object* v_h_877_, lean_object* v_msg_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_877_, v_msg_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg(lean_object* v_inst_881_, lean_object* v_h_882_, lean_object* v_r_883_){
_start:
{
lean_object* v_id_885_; lean_object* v_method_886_; lean_object* v_param_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_907_; 
v_id_885_ = lean_ctor_get(v_r_883_, 0);
v_method_886_ = lean_ctor_get(v_r_883_, 1);
v_param_887_ = lean_ctor_get(v_r_883_, 2);
v_isSharedCheck_907_ = !lean_is_exclusive(v_r_883_);
if (v_isSharedCheck_907_ == 0)
{
v___x_889_ = v_r_883_;
v_isShared_890_ = v_isSharedCheck_907_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_param_887_);
lean_inc(v_method_886_);
lean_inc(v_id_885_);
lean_dec(v_r_883_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_907_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___y_892_; lean_object* v___x_897_; 
v___x_897_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_881_, v_param_887_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v___x_898_; 
lean_dec_ref_known(v___x_897_, 1);
v___x_898_ = lean_box(0);
v___y_892_ = v___x_898_;
goto v___jp_891_;
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
v_a_899_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_897_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_897_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
v___y_892_ = v___x_904_;
goto v___jp_891_;
}
}
}
v___jp_891_:
{
lean_object* v___x_894_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 2, v___y_892_);
v___x_894_ = v___x_889_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_id_885_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_method_886_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v___y_892_);
v___x_894_ = v_reuseFailAlloc_896_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_882_, v___x_894_);
return v___x_895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object* v_inst_908_, lean_object* v_h_909_, lean_object* v_r_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_908_, v_h_909_, v_r_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest(lean_object* v_00_u03b1_913_, lean_object* v_inst_914_, lean_object* v_h_915_, lean_object* v_r_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_IO_FS_Stream_writeLspRequest___redArg(v_inst_914_, v_h_915_, v_r_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspRequest___boxed(lean_object* v_00_u03b1_919_, lean_object* v_inst_920_, lean_object* v_h_921_, lean_object* v_r_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_IO_FS_Stream_writeLspRequest(v_00_u03b1_919_, v_inst_920_, v_h_921_, v_r_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg(lean_object* v_inst_925_, lean_object* v_h_926_, lean_object* v_n_927_){
_start:
{
lean_object* v_method_929_; lean_object* v_param_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_950_; 
v_method_929_ = lean_ctor_get(v_n_927_, 0);
v_param_930_ = lean_ctor_get(v_n_927_, 1);
v_isSharedCheck_950_ = !lean_is_exclusive(v_n_927_);
if (v_isSharedCheck_950_ == 0)
{
v___x_932_ = v_n_927_;
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_param_930_);
lean_inc(v_method_929_);
lean_dec(v_n_927_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_950_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___y_935_; lean_object* v___x_940_; 
v___x_940_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_925_, v_param_930_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v___x_941_; 
lean_dec_ref_known(v___x_940_, 1);
v___x_941_ = lean_box(0);
v___y_935_ = v___x_941_;
goto v___jp_934_;
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_940_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_940_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
v___y_935_ = v___x_947_;
goto v___jp_934_;
}
}
}
v___jp_934_:
{
lean_object* v___x_937_; 
if (v_isShared_933_ == 0)
{
lean_ctor_set_tag(v___x_932_, 1);
lean_ctor_set(v___x_932_, 1, v___y_935_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_method_929_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___y_935_);
v___x_937_ = v_reuseFailAlloc_939_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; 
v___x_938_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_926_, v___x_937_);
return v___x_938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object* v_inst_951_, lean_object* v_h_952_, lean_object* v_n_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_951_, v_h_952_, v_n_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification(lean_object* v_00_u03b1_956_, lean_object* v_inst_957_, lean_object* v_h_958_, lean_object* v_n_959_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Lean_IO_FS_Stream_writeLspNotification___redArg(v_inst_957_, v_h_958_, v_n_959_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspNotification___boxed(lean_object* v_00_u03b1_962_, lean_object* v_inst_963_, lean_object* v_h_964_, lean_object* v_n_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_IO_FS_Stream_writeLspNotification(v_00_u03b1_962_, v_inst_963_, v_h_964_, v_n_965_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg(lean_object* v_inst_968_, lean_object* v_h_969_, lean_object* v_r_970_){
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
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object* v_inst_983_, lean_object* v_h_984_, lean_object* v_r_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_983_, v_h_984_, v_r_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse(lean_object* v_00_u03b1_988_, lean_object* v_inst_989_, lean_object* v_h_990_, lean_object* v_r_991_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Lean_IO_FS_Stream_writeLspResponse___redArg(v_inst_989_, v_h_990_, v_r_991_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponse___boxed(lean_object* v_00_u03b1_994_, lean_object* v_inst_995_, lean_object* v_h_996_, lean_object* v_r_997_, lean_object* v_a_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_IO_FS_Stream_writeLspResponse(v_00_u03b1_994_, v_inst_995_, v_h_996_, v_r_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError(lean_object* v_h_1000_, lean_object* v_e_1001_){
_start:
{
lean_object* v_id_1003_; uint8_t v_code_1004_; lean_object* v_message_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1014_; 
v_id_1003_ = lean_ctor_get(v_e_1001_, 0);
v_code_1004_ = lean_ctor_get_uint8(v_e_1001_, sizeof(void*)*3);
v_message_1005_ = lean_ctor_get(v_e_1001_, 1);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_e_1001_);
if (v_isSharedCheck_1014_ == 0)
{
lean_object* v_unused_1015_; 
v_unused_1015_ = lean_ctor_get(v_e_1001_, 2);
lean_dec(v_unused_1015_);
v___x_1007_ = v_e_1001_;
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_message_1005_);
lean_inc(v_id_1003_);
lean_dec(v_e_1001_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1009_ = lean_box(0);
if (v_isShared_1008_ == 0)
{
lean_ctor_set_tag(v___x_1007_, 3);
lean_ctor_set(v___x_1007_, 2, v___x_1009_);
v___x_1011_ = v___x_1007_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_id_1003_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_message_1005_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v___x_1009_);
lean_ctor_set_uint8(v_reuseFailAlloc_1013_, sizeof(void*)*3, v_code_1004_);
v___x_1011_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_1000_, v___x_1011_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseError___boxed(lean_object* v_h_1016_, lean_object* v_e_1017_, lean_object* v_a_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_IO_FS_Stream_writeLspResponseError(v_h_1016_, v_e_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object* v_inst_1020_, lean_object* v_h_1021_, lean_object* v_e_1022_){
_start:
{
lean_object* v_id_1024_; uint8_t v_code_1025_; lean_object* v_message_1026_; lean_object* v_data_x3f_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1047_; 
v_id_1024_ = lean_ctor_get(v_e_1022_, 0);
v_code_1025_ = lean_ctor_get_uint8(v_e_1022_, sizeof(void*)*3);
v_message_1026_ = lean_ctor_get(v_e_1022_, 1);
v_data_x3f_1027_ = lean_ctor_get(v_e_1022_, 2);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_e_1022_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1029_ = v_e_1022_;
v_isShared_1030_ = v_isSharedCheck_1047_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_data_x3f_1027_);
lean_inc(v_message_1026_);
lean_inc(v_id_1024_);
lean_dec(v_e_1022_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1047_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___y_1032_; 
if (lean_obj_tag(v_data_x3f_1027_) == 0)
{
lean_object* v___x_1037_; 
lean_dec_ref(v_inst_1020_);
v___x_1037_ = lean_box(0);
v___y_1032_ = v___x_1037_;
goto v___jp_1031_;
}
else
{
lean_object* v_val_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1046_; 
v_val_1038_ = lean_ctor_get(v_data_x3f_1027_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_data_x3f_1027_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1040_ = v_data_x3f_1027_;
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_val_1038_);
lean_dec(v_data_x3f_1027_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1046_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = lean_apply_1(v_inst_1020_, v_val_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
v___y_1032_ = v___x_1044_;
goto v___jp_1031_;
}
}
}
v___jp_1031_:
{
lean_object* v___x_1034_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 3);
lean_ctor_set(v___x_1029_, 2, v___y_1032_);
v___x_1034_ = v___x_1029_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_id_1024_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_message_1026_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v___y_1032_);
lean_ctor_set_uint8(v_reuseFailAlloc_1036_, sizeof(void*)*3, v_code_1025_);
v___x_1034_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_IO_FS_Stream_writeLspMessage(v_h_1021_, v___x_1034_);
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object* v_inst_1048_, lean_object* v_h_1049_, lean_object* v_e_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1048_, v_h_1049_, v_e_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* v_00_u03b1_1053_, lean_object* v_inst_1054_, lean_object* v_h_1055_, lean_object* v_e_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1054_, v_h_1055_, v_e_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object* v_00_u03b1_1059_, lean_object* v_inst_1060_, lean_object* v_h_1061_, lean_object* v_e_1062_, lean_object* v_a_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_IO_FS_Stream_writeLspResponseErrorWithData(v_00_u03b1_1059_, v_inst_1060_, v_h_1061_, v_e_1062_);
return v_res_1064_;
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

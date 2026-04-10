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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_posGE___redArg(lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_Slice_intercalate(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readUTF8(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*);
static const lean_string_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0_value;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7_value;
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__7_value)}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1_value;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3;
static const lean_array_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "seq_num"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Invalid header field: "};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 176, .m_capacity = 176, .m_length = 175, .m_data = "A Lean 3 request was received. Please ensure that your editor has a Lean 4 compatible extension installed. For VSCode, this is\n\n    https://github.com/leanprover/vscode-lean4 "};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1_value;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Stream was closed"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3_value;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0 = (const lean_object*)&l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0_value;
static const lean_string_object l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1 = (const lean_object*)&l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1_value;
static const lean_string_object l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2 = (const lean_object*)&l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Content-Length"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "No Content-Length field in header: "};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Content-Length header field value '"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "' is not a Nat"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readLspMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Cannot read LSP message: "};
static const lean_object* l_IO_FS_Stream_readLspMessage___closed__0 = (const lean_object*)&l_IO_FS_Stream_readLspMessage___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readLspRequestAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Cannot read LSP request: "};
static const lean_object* l_IO_FS_Stream_readLspRequestAs___redArg___closed__0 = (const lean_object*)&l_IO_FS_Stream_readLspRequestAs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Cannot read LSP notification: "};
static const lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0 = (const lean_object*)&l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readLspResponseAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Cannot read LSP response: "};
static const lean_object* l_IO_FS_Stream_readLspResponseAs___redArg___closed__0 = (const lean_object*)&l_IO_FS_Stream_readLspResponseAs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_writeSerializedLspMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Content-Length: "};
static const lean_object* l_IO_FS_Stream_writeSerializedLspMessage___closed__0 = (const lean_object*)&l_IO_FS_Stream_writeSerializedLspMessage___closed__0_value;
static const lean_string_object l_IO_FS_Stream_writeSerializedLspMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\r\n\r\n"};
static const lean_object* l_IO_FS_Stream_writeSerializedLspMessage___closed__1 = (const lean_object*)&l_IO_FS_Stream_writeSerializedLspMessage___closed__1_value;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_writeLspMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "jsonrpc"};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__0 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__0_value;
static const lean_string_object l_IO_FS_Stream_writeLspMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "2.0"};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__1 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__1_value;
static const lean_ctor_object l_IO_FS_Stream_writeLspMessage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__1_value)}};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__2 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__2_value;
static const lean_ctor_object l_IO_FS_Stream_writeLspMessage___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__0_value),((lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__2_value)}};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__3 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__3_value;
static const lean_string_object l_IO_FS_Stream_writeLspMessage___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "id"};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__4 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__4_value;
static const lean_string_object l_IO_FS_Stream_writeLspMessage___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "method"};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__5 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__5_value;
static const lean_string_object l_IO_FS_Stream_writeLspMessage___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "params"};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__6 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__6_value;
static const lean_string_object l_IO_FS_Stream_writeLspMessage___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__7 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__7_value;
static const lean_string_object l_IO_FS_Stream_writeLspMessage___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "message"};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__8 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__8_value;
static const lean_string_object l_IO_FS_Stream_writeLspMessage___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__9 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__9_value;
static const lean_string_object l_IO_FS_Stream_writeLspMessage___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "error"};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__10 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__10_value;
static const lean_string_object l_IO_FS_Stream_writeLspMessage___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_IO_FS_Stream_writeLspMessage___closed__11 = (const lean_object*)&l_IO_FS_Stream_writeLspMessage___closed__11_value;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__12;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__13;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__14;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__15;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__16;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__17;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__18;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__19;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__20;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__21;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__22;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__23;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__24;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__25;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__26;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__27;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__28;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__29;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__30;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__31;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__32;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__33;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__34;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__35;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__36;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__37;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__38;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__39;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__40;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__41;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__42;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__43;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__44;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__45;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__46;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__47;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__48;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__49;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__50;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__51;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__52;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__53;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__54;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__55;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__56;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__57;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__58;
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__59;
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0));
v___x_3_ = lean_string_utf8_byte_size(v___x_2_);
return v___x_3_;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1);
v___x_6_ = lean_nat_dec_eq(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_7_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0));
v___x_10_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
lean_ctor_set(v___x_10_, 2, v___x_7_);
return v___x_10_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
v___x_12_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_11_);
return v___x_12_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4);
v___x_15_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
v___x_16_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_13_);
lean_ctor_set(v___x_16_, 3, v___x_13_);
return v___x_16_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(lean_object* v_s_25_){
_start:
{
uint8_t v___x_26_; 
v___x_26_ = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6);
return v___x_27_;
}
else
{
lean_object* v___x_28_; 
v___x_28_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8));
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object* v_s_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(v_s_29_);
lean_dec_ref(v_s_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object* v_s_31_, lean_object* v___x_32_, lean_object* v___x_33_, lean_object* v_a_34_, lean_object* v_b_35_){
_start:
{
lean_object* v_it_37_; lean_object* v_startInclusive_38_; lean_object* v_endExclusive_39_; 
if (lean_obj_tag(v_a_34_) == 0)
{
lean_object* v_currPos_43_; lean_object* v_searcher_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_148_; 
v_currPos_43_ = lean_ctor_get(v_a_34_, 0);
v_searcher_44_ = lean_ctor_get(v_a_34_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_a_34_);
if (v_isSharedCheck_148_ == 0)
{
v___x_46_ = v_a_34_;
v_isShared_47_ = v_isSharedCheck_148_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_searcher_44_);
lean_inc(v_currPos_43_);
lean_dec(v_a_34_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_148_;
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
lean_object* v_startInclusive_74_; lean_object* v_endExclusive_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v_startInclusive_74_ = lean_ctor_get(v___x_32_, 1);
v_endExclusive_75_ = lean_ctor_get(v___x_32_, 2);
v___x_76_ = lean_nat_sub(v_endExclusive_75_, v_startInclusive_74_);
v___x_77_ = lean_nat_dec_eq(v_pos_70_, v___x_76_);
lean_dec(v___x_76_);
if (v___x_77_ == 0)
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
lean_object* v_needle_92_; lean_object* v_table_93_; lean_object* v_stackPos_94_; lean_object* v_needlePos_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_147_; 
v_needle_92_ = lean_ctor_get(v_searcher_44_, 0);
v_table_93_ = lean_ctor_get(v_searcher_44_, 1);
v_stackPos_94_ = lean_ctor_get(v_searcher_44_, 2);
v_needlePos_95_ = lean_ctor_get(v_searcher_44_, 3);
v_isSharedCheck_147_ = !lean_is_exclusive(v_searcher_44_);
if (v_isSharedCheck_147_ == 0)
{
v___x_97_ = v_searcher_44_;
v_isShared_98_ = v_isSharedCheck_147_;
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
v_isShared_98_ = v_isSharedCheck_147_;
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
uint8_t v___x_106_; 
lean_dec(v___x_103_);
lean_del_object(v___x_97_);
lean_dec(v_needlePos_95_);
lean_dec(v_stackPos_94_);
lean_dec_ref(v_table_93_);
lean_dec_ref(v_needle_92_);
v___x_106_ = lean_nat_dec_lt(v_basePos_102_, v___x_33_);
lean_dec(v_basePos_102_);
if (v___x_106_ == 0)
{
lean_del_object(v___x_46_);
goto v___jp_68_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = lean_box(3);
v_it_49_ = v___x_107_;
goto v___jp_48_;
}
}
else
{
uint8_t v_stackByte_108_; lean_object* v___x_109_; uint8_t v_patByte_110_; uint8_t v___x_111_; 
lean_dec(v_basePos_102_);
lean_inc(v_stackPos_94_);
v_stackByte_108_ = lean_string_get_byte_fast(v_s_31_, v_stackPos_94_);
v___x_109_ = lean_nat_add(v_startInclusive_100_, v_needlePos_95_);
v_patByte_110_ = lean_string_get_byte_fast(v_str_99_, v___x_109_);
v___x_111_ = lean_uint8_dec_eq(v_stackByte_108_, v_patByte_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; uint8_t v___x_113_; 
lean_dec(v___x_103_);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_nat_dec_eq(v_needlePos_95_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_newNeedlePos_116_; uint8_t v___x_117_; 
v___x_114_ = lean_unsigned_to_nat(1u);
v___x_115_ = lean_nat_sub(v_needlePos_95_, v___x_114_);
lean_dec(v_needlePos_95_);
v_newNeedlePos_116_ = lean_array_fget_borrowed(v_table_93_, v___x_115_);
lean_dec(v___x_115_);
v___x_117_ = lean_nat_dec_eq(v_newNeedlePos_116_, v___x_112_);
if (v___x_117_ == 0)
{
lean_object* v___x_119_; 
lean_inc(v_newNeedlePos_116_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v_newNeedlePos_116_);
v___x_119_ = v___x_97_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_needle_92_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_table_93_);
lean_ctor_set(v_reuseFailAlloc_120_, 2, v_stackPos_94_);
lean_ctor_set(v_reuseFailAlloc_120_, 3, v_newNeedlePos_116_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
v_it_49_ = v___x_119_;
goto v___jp_48_;
}
}
else
{
lean_object* v_nextStackPos_121_; lean_object* v___x_123_; 
v_nextStackPos_121_ = l_String_Slice_posGE___redArg(v___x_32_, v_stackPos_94_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v___x_112_);
lean_ctor_set(v___x_97_, 2, v_nextStackPos_121_);
v___x_123_ = v___x_97_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_needle_92_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v_table_93_);
lean_ctor_set(v_reuseFailAlloc_124_, 2, v_nextStackPos_121_);
lean_ctor_set(v_reuseFailAlloc_124_, 3, v___x_112_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
v_it_49_ = v___x_123_;
goto v___jp_48_;
}
}
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v_nextStackPos_127_; lean_object* v___x_129_; 
lean_dec(v_needlePos_95_);
v___x_125_ = lean_unsigned_to_nat(1u);
v___x_126_ = lean_nat_add(v_stackPos_94_, v___x_125_);
lean_dec(v_stackPos_94_);
v_nextStackPos_127_ = l_String_Slice_posGE___redArg(v___x_32_, v___x_126_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v___x_112_);
lean_ctor_set(v___x_97_, 2, v_nextStackPos_127_);
v___x_129_ = v___x_97_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_needle_92_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_table_93_);
lean_ctor_set(v_reuseFailAlloc_130_, 2, v_nextStackPos_127_);
lean_ctor_set(v_reuseFailAlloc_130_, 3, v___x_112_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
v_it_49_ = v___x_129_;
goto v___jp_48_;
}
}
}
else
{
lean_object* v___x_131_; lean_object* v_nextStackPos_132_; lean_object* v_nextNeedlePos_133_; uint8_t v___x_134_; 
lean_del_object(v___x_46_);
v___x_131_ = lean_unsigned_to_nat(1u);
v_nextStackPos_132_ = lean_nat_add(v_stackPos_94_, v___x_131_);
lean_dec(v_stackPos_94_);
v_nextNeedlePos_133_ = lean_nat_add(v_needlePos_95_, v___x_131_);
lean_dec(v_needlePos_95_);
v___x_134_ = lean_nat_dec_eq(v_nextNeedlePos_133_, v___x_103_);
lean_dec(v___x_103_);
if (v___x_134_ == 0)
{
lean_object* v___x_136_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v_nextNeedlePos_133_);
lean_ctor_set(v___x_97_, 2, v_nextStackPos_132_);
v___x_136_ = v___x_97_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_needle_92_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_table_93_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_nextStackPos_132_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v_nextNeedlePos_133_);
v___x_136_ = v_reuseFailAlloc_139_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; 
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_currPos_43_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v_a_34_ = v___x_137_;
goto _start;
}
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_140_ = lean_nat_sub(v_nextStackPos_132_, v_nextNeedlePos_133_);
lean_dec(v_nextNeedlePos_133_);
v___x_141_ = l_String_Slice_pos_x21(v___x_32_, v___x_140_);
lean_dec(v___x_140_);
v___x_142_ = l_String_Slice_pos_x21(v___x_32_, v_nextStackPos_132_);
v___x_143_ = lean_unsigned_to_nat(0u);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 3, v___x_143_);
lean_ctor_set(v___x_97_, 2, v_nextStackPos_132_);
v___x_145_ = v___x_97_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_needle_92_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_table_93_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_nextStackPos_132_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
v_it_55_ = v___x_145_;
v_startPos_56_ = v___x_141_;
v_endPos_57_ = v___x_142_;
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object* v_s_149_, lean_object* v___x_150_, lean_object* v___x_151_, lean_object* v_a_152_, lean_object* v_b_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_149_, v___x_150_, v___x_151_, v_a_152_, v_b_153_);
lean_dec_ref(v___x_150_);
return v_res_154_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1));
v___x_158_ = lean_string_utf8_byte_size(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_159_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2, &l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1));
v___x_162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
lean_ctor_set(v___x_162_, 2, v___x_159_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object* v_s_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0));
v___x_167_ = lean_string_dec_eq(v_s_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_168_ = lean_unsigned_to_nat(2u);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_string_utf8_byte_size(v_s_165_);
lean_inc_ref_n(v_s_165_, 2);
v___x_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_171_, 0, v_s_165_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_170_);
v___x_172_ = l_String_Slice_Pos_prevn(v___x_171_, v___x_170_, v___x_168_);
lean_dec_ref(v___x_171_);
lean_inc(v___x_172_);
v___x_173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_173_, 0, v_s_165_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
lean_ctor_set(v___x_173_, 2, v___x_170_);
v___x_174_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3, &l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3_once, _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3);
v___x_175_ = l_String_Slice_beq(v___x_173_, v___x_174_);
lean_dec_ref(v___x_173_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
lean_dec(v___x_172_);
lean_dec_ref(v_s_165_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
lean_inc(v___x_172_);
lean_inc_ref(v_s_165_);
v___x_177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_177_, 0, v_s_165_);
lean_ctor_set(v___x_177_, 1, v___x_169_);
lean_ctor_set(v___x_177_, 2, v___x_172_);
v___x_178_ = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(v___x_177_);
v___x_179_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4));
v___x_180_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_165_, v___x_177_, v___x_172_, v___x_178_, v___x_179_);
lean_dec_ref(v___x_177_);
v___x_181_ = lean_array_to_list(v___x_180_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_box(0);
return v___x_182_;
}
else
{
lean_object* v_tail_183_; 
v_tail_183_ = lean_ctor_get(v___x_181_, 1);
lean_inc(v_tail_183_);
if (lean_obj_tag(v_tail_183_) == 0)
{
lean_object* v___x_184_; 
lean_dec_ref(v___x_181_);
v___x_184_ = lean_box(0);
return v___x_184_;
}
else
{
lean_object* v_head_185_; lean_object* v_str_186_; lean_object* v_startInclusive_187_; lean_object* v_endExclusive_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_199_; 
v_head_185_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_head_185_);
lean_dec_ref(v___x_181_);
v_str_186_ = lean_ctor_get(v_head_185_, 0);
lean_inc_ref(v_str_186_);
v_startInclusive_187_ = lean_ctor_get(v_head_185_, 1);
lean_inc(v_startInclusive_187_);
v_endExclusive_188_ = lean_ctor_get(v_head_185_, 2);
lean_inc(v_endExclusive_188_);
lean_dec(v_head_185_);
v___x_189_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
v___x_190_ = l_String_Slice_intercalate(v___x_189_, v_tail_183_);
v_isSharedCheck_199_ = !lean_is_exclusive(v_tail_183_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; lean_object* v_unused_201_; 
v_unused_200_ = lean_ctor_get(v_tail_183_, 1);
lean_dec(v_unused_200_);
v_unused_201_ = lean_ctor_get(v_tail_183_, 0);
lean_dec(v_unused_201_);
v___x_192_ = v_tail_183_;
v_isShared_193_ = v_isSharedCheck_199_;
goto v_resetjp_191_;
}
else
{
lean_dec(v_tail_183_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_199_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_string_utf8_extract(v_str_186_, v_startInclusive_187_, v_endExclusive_188_);
lean_dec(v_endExclusive_188_);
lean_dec(v_startInclusive_187_);
lean_dec_ref(v_str_186_);
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 0);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_190_);
v___x_196_ = v_reuseFailAlloc_198_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; 
v___x_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
}
}
}
}
else
{
lean_object* v___x_202_; 
lean_dec_ref(v_s_165_);
v___x_202_ = lean_box(0);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(lean_object* v_s_203_, lean_object* v___x_204_, lean_object* v___x_205_, lean_object* v_inst_206_, lean_object* v_R_207_, lean_object* v_a_208_, lean_object* v_b_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(v_s_203_, v___x_204_, v___x_205_, v_a_208_, v_b_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object* v_s_211_, lean_object* v___x_212_, lean_object* v___x_213_, lean_object* v_inst_214_, lean_object* v_R_215_, lean_object* v_a_216_, lean_object* v_b_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(v_s_211_, v___x_212_, v___x_213_, v_inst_214_, v_R_215_, v_a_216_, v_b_217_);
lean_dec_ref(v___x_212_);
return v_res_218_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(lean_object* v_s_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Json_parse(v_s_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
uint8_t v___x_223_; 
lean_dec_ref(v___x_222_);
v___x_223_ = 0;
return v___x_223_;
}
else
{
lean_object* v_a_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_a_224_ = lean_ctor_get(v___x_222_, 0);
lean_inc_n(v_a_224_, 2);
lean_dec_ref(v___x_222_);
v___x_225_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0));
v___x_226_ = l_Lean_Json_getObjVal_x3f(v_a_224_, v___x_225_);
if (lean_obj_tag(v___x_226_) == 0)
{
uint8_t v___x_227_; 
lean_dec_ref(v___x_226_);
lean_dec(v_a_224_);
v___x_227_ = 0;
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec_ref(v___x_226_);
v___x_228_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1));
v___x_229_ = l_Lean_Json_getObjVal_x3f(v_a_224_, v___x_228_);
if (lean_obj_tag(v___x_229_) == 0)
{
uint8_t v___x_230_; 
lean_dec_ref(v___x_229_);
v___x_230_ = 0;
return v___x_230_;
}
else
{
uint8_t v___x_231_; 
lean_dec_ref(v___x_229_);
v___x_231_ = 1;
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(lean_object* v_s_232_){
_start:
{
uint8_t v_res_233_; lean_object* v_r_234_; 
v_res_233_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(v_s_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1));
v___x_238_ = lean_mk_io_user_error(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3));
v___x_241_ = lean_mk_io_user_error(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object* v_h_242_){
_start:
{
lean_object* v_getLine_244_; lean_object* v___x_245_; 
v_getLine_244_ = lean_ctor_get(v_h_242_, 3);
lean_inc_ref(v_getLine_244_);
v___x_245_ = lean_apply_1(v_getLine_244_, lean_box(0));
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_290_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_290_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_290_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_290_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_250_ = lean_string_utf8_byte_size(v_a_246_);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_nat_dec_eq(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1));
v___x_254_ = lean_string_dec_eq(v_a_246_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_inc(v_a_246_);
v___x_255_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(v_a_246_);
if (lean_obj_tag(v___x_255_) == 0)
{
uint8_t v___x_256_; 
lean_dec_ref(v_h_242_);
lean_inc(v_a_246_);
v___x_256_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(v_a_246_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_257_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0));
v___x_258_ = l_String_quote(v_a_246_);
v___x_259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
v___x_260_ = l_Std_Format_defWidth;
v___x_261_ = l_Std_Format_pretty(v___x_259_, v___x_260_, v___x_251_, v___x_251_);
v___x_262_ = lean_string_append(v___x_257_, v___x_261_);
lean_dec_ref(v___x_261_);
v___x_263_ = lean_mk_io_user_error(v___x_262_);
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 1);
lean_ctor_set(v___x_248_, 0, v___x_263_);
v___x_265_ = v___x_248_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec(v_a_246_);
v___x_267_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2, &l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2);
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 1);
lean_ctor_set(v___x_248_, 0, v___x_267_);
v___x_269_ = v___x_248_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_object* v_val_271_; lean_object* v___x_272_; 
lean_del_object(v___x_248_);
lean_dec(v_a_246_);
v_val_271_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_val_271_);
lean_dec_ref(v___x_255_);
v___x_272_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(v_h_242_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_281_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v_val_271_);
lean_ctor_set(v___x_277_, 1, v_a_273_);
if (v_isShared_276_ == 0)
{
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_279_ = v___x_275_;
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
lean_dec(v_val_271_);
return v___x_272_;
}
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_284_; 
lean_dec(v_a_246_);
lean_dec_ref(v_h_242_);
v___x_282_ = lean_box(0);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_282_);
v___x_284_ = v___x_248_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v___x_286_; lean_object* v___x_288_; 
lean_dec(v_a_246_);
lean_dec_ref(v_h_242_);
v___x_286_ = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4, &l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4_once, _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4);
if (v_isShared_249_ == 0)
{
lean_ctor_set_tag(v___x_248_, 1);
lean_ctor_set(v___x_248_, 0, v___x_286_);
v___x_288_ = v___x_248_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec_ref(v_h_242_);
v_a_291_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_245_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_245_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___boxed(lean_object* v_h_299_, lean_object* v_a_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(v_h_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
return v_x_305_;
}
else
{
lean_object* v_head_307_; lean_object* v_tail_308_; lean_object* v_fst_309_; lean_object* v_snd_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_head_307_ = lean_ctor_get(v_x_306_, 0);
v_tail_308_ = lean_ctor_get(v_x_306_, 1);
v_fst_309_ = lean_ctor_get(v_head_307_, 0);
v_snd_310_ = lean_ctor_get(v_head_307_, 1);
v___x_311_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_312_ = lean_string_append(v_x_305_, v___x_311_);
v___x_313_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_314_ = lean_string_append(v___x_313_, v_fst_309_);
v___x_315_ = lean_string_append(v___x_314_, v___x_311_);
v___x_316_ = lean_string_append(v___x_315_, v_snd_310_);
v___x_317_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_318_ = lean_string_append(v___x_316_, v___x_317_);
v___x_319_ = lean_string_append(v___x_312_, v___x_318_);
lean_dec_ref(v___x_318_);
v_x_305_ = v___x_319_;
v_x_306_ = v_tail_308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(v_x_321_, v_x_322_);
lean_dec(v_x_322_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_object* v___x_328_; 
v___x_328_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0));
return v___x_328_;
}
else
{
lean_object* v_tail_329_; 
v_tail_329_ = lean_ctor_get(v_x_327_, 1);
if (lean_obj_tag(v_tail_329_) == 0)
{
lean_object* v_head_330_; lean_object* v_fst_331_; lean_object* v_snd_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_head_330_ = lean_ctor_get(v_x_327_, 0);
v_fst_331_ = lean_ctor_get(v_head_330_, 0);
v_snd_332_ = lean_ctor_get(v_head_330_, 1);
v___x_333_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_334_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_335_ = lean_string_append(v___x_334_, v_fst_331_);
v___x_336_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_337_ = lean_string_append(v___x_335_, v___x_336_);
v___x_338_ = lean_string_append(v___x_337_, v_snd_332_);
v___x_339_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_340_ = lean_string_append(v___x_338_, v___x_339_);
v___x_341_ = lean_string_append(v___x_333_, v___x_340_);
lean_dec_ref(v___x_340_);
v___x_342_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2));
v___x_343_ = lean_string_append(v___x_341_, v___x_342_);
return v___x_343_;
}
else
{
lean_object* v_head_344_; lean_object* v_fst_345_; lean_object* v_snd_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint32_t v___x_357_; lean_object* v___x_358_; 
v_head_344_ = lean_ctor_get(v_x_327_, 0);
v_fst_345_ = lean_ctor_get(v_head_344_, 0);
v_snd_346_ = lean_ctor_get(v_head_344_, 1);
v___x_347_ = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1));
v___x_348_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
v___x_349_ = lean_string_append(v___x_348_, v_fst_345_);
v___x_350_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
v___x_351_ = lean_string_append(v___x_349_, v___x_350_);
v___x_352_ = lean_string_append(v___x_351_, v_snd_346_);
v___x_353_ = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
v___x_354_ = lean_string_append(v___x_352_, v___x_353_);
v___x_355_ = lean_string_append(v___x_347_, v___x_354_);
lean_dec_ref(v___x_354_);
v___x_356_ = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(v___x_355_, v_tail_329_);
v___x_357_ = 93;
v___x_358_ = lean_string_push(v___x_356_, v___x_357_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object* v_x_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(v_x_359_);
lean_dec(v_x_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
if (lean_obj_tag(v_x_362_) == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_box(0);
return v___x_363_;
}
else
{
lean_object* v_head_364_; lean_object* v_tail_365_; lean_object* v_fst_366_; lean_object* v_snd_367_; uint8_t v___x_368_; 
v_head_364_ = lean_ctor_get(v_x_362_, 0);
v_tail_365_ = lean_ctor_get(v_x_362_, 1);
v_fst_366_ = lean_ctor_get(v_head_364_, 0);
v_snd_367_ = lean_ctor_get(v_head_364_, 1);
v___x_368_ = lean_string_dec_eq(v_x_361_, v_fst_366_);
if (v___x_368_ == 0)
{
v_x_362_ = v_tail_365_;
goto _start;
}
else
{
lean_object* v___x_370_; 
lean_inc(v_snd_367_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v_snd_367_);
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_371_, v_x_372_);
lean_dec(v_x_372_);
lean_dec_ref(v_x_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object* v_h_378_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(v_h_378_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_411_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_411_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_411_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_411_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0));
v___x_386_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(v___x_385_, v_a_381_);
if (lean_obj_tag(v___x_386_) == 0)
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1));
v___x_388_ = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(v_a_381_);
lean_dec(v_a_381_);
v___x_389_ = lean_string_append(v___x_387_, v___x_388_);
lean_dec_ref(v___x_388_);
v___x_390_ = lean_mk_io_user_error(v___x_389_);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 1);
lean_ctor_set(v___x_383_, 0, v___x_390_);
v___x_392_ = v___x_383_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
else
{
lean_object* v_val_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v_a_381_);
v_val_394_ = lean_ctor_get(v___x_386_, 0);
lean_inc_n(v_val_394_, 2);
lean_dec_ref(v___x_386_);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_string_utf8_byte_size(v_val_394_);
v___x_397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_397_, 0, v_val_394_);
lean_ctor_set(v___x_397_, 1, v___x_395_);
lean_ctor_set(v___x_397_, 2, v___x_396_);
v___x_398_ = l_String_Slice_toNat_x3f(v___x_397_);
lean_dec_ref(v___x_397_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_399_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2));
v___x_400_ = lean_string_append(v___x_399_, v_val_394_);
lean_dec(v_val_394_);
v___x_401_ = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3));
v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
v___x_403_ = lean_mk_io_user_error(v___x_402_);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 1);
lean_ctor_set(v___x_383_, 0, v___x_403_);
v___x_405_ = v___x_383_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
else
{
lean_object* v_val_407_; lean_object* v___x_409_; 
lean_dec(v_val_394_);
v_val_407_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_val_407_);
lean_dec_ref(v___x_398_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v_val_407_);
v___x_409_ = v___x_383_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_val_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_412_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_380_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_380_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___boxed(lean_object* v_h_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(v_h_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(lean_object* v_00_u03b2_423_, lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(v_x_424_, v_x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object* v_00_u03b2_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(v_00_u03b2_427_, v_x_428_, v_x_429_);
lean_dec(v_x_429_);
lean_dec_ref(v_x_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object* v_h_432_){
_start:
{
lean_object* v_a_435_; lean_object* v___x_441_; 
lean_inc_ref(v_h_432_);
v___x_441_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(v_h_432_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_442_);
lean_dec_ref(v___x_441_);
v___x_443_ = l_IO_FS_Stream_readMessage(v_h_432_, v_a_442_);
lean_dec(v_a_442_);
if (lean_obj_tag(v___x_443_) == 0)
{
return v___x_443_;
}
else
{
lean_object* v_a_444_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
lean_inc(v_a_444_);
lean_dec_ref(v___x_443_);
v_a_435_ = v_a_444_;
goto v___jp_434_;
}
}
else
{
lean_object* v_a_445_; 
lean_dec_ref(v_h_432_);
v_a_445_ = lean_ctor_get(v___x_441_, 0);
lean_inc(v_a_445_);
lean_dec_ref(v___x_441_);
v_a_435_ = v_a_445_;
goto v___jp_434_;
}
v___jp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_436_ = ((lean_object*)(l_IO_FS_Stream_readLspMessage___closed__0));
v___x_437_ = lean_io_error_to_string(v_a_435_);
v___x_438_ = lean_string_append(v___x_436_, v___x_437_);
lean_dec_ref(v___x_437_);
v___x_439_ = lean_mk_io_user_error(v___x_438_);
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage___boxed(lean_object* v_h_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_IO_FS_Stream_readLspMessage(v_h_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString(lean_object* v_h_449_){
_start:
{
lean_object* v_a_452_; lean_object* v___x_458_; 
lean_inc_ref(v_h_449_);
v___x_458_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(v_h_449_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_460_; 
v_a_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_459_);
lean_dec_ref(v___x_458_);
v___x_460_ = l_IO_FS_Stream_readUTF8(v_h_449_, v_a_459_);
lean_dec(v_a_459_);
if (lean_obj_tag(v___x_460_) == 0)
{
return v___x_460_;
}
else
{
lean_object* v_a_461_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_a_461_);
lean_dec_ref(v___x_460_);
v_a_452_ = v_a_461_;
goto v___jp_451_;
}
}
else
{
lean_object* v_a_462_; 
lean_dec_ref(v_h_449_);
v_a_462_ = lean_ctor_get(v___x_458_, 0);
lean_inc(v_a_462_);
lean_dec_ref(v___x_458_);
v_a_452_ = v_a_462_;
goto v___jp_451_;
}
v___jp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_453_ = ((lean_object*)(l_IO_FS_Stream_readLspMessage___closed__0));
v___x_454_ = lean_io_error_to_string(v_a_452_);
v___x_455_ = lean_string_append(v___x_453_, v___x_454_);
lean_dec_ref(v___x_454_);
v___x_456_ = lean_mk_io_user_error(v___x_455_);
v___x_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString___boxed(lean_object* v_h_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_IO_FS_Stream_readLspMessageAsString(v_h_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object* v_h_467_, lean_object* v_expectedMethod_468_, lean_object* v_inst_469_){
_start:
{
lean_object* v_a_472_; lean_object* v___x_478_; 
lean_inc_ref(v_h_467_);
v___x_478_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(v_h_467_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref(v___x_478_);
v___x_480_ = l_IO_FS_Stream_readRequestAs___redArg(v_h_467_, v_a_479_, v_expectedMethod_468_, v_inst_469_);
lean_dec(v_a_479_);
if (lean_obj_tag(v___x_480_) == 0)
{
return v___x_480_;
}
else
{
lean_object* v_a_481_; 
v_a_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_a_481_);
lean_dec_ref(v___x_480_);
v_a_472_ = v_a_481_;
goto v___jp_471_;
}
}
else
{
lean_object* v_a_482_; 
lean_dec_ref(v_inst_469_);
lean_dec_ref(v_expectedMethod_468_);
lean_dec_ref(v_h_467_);
v_a_482_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_482_);
lean_dec_ref(v___x_478_);
v_a_472_ = v_a_482_;
goto v___jp_471_;
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_473_ = ((lean_object*)(l_IO_FS_Stream_readLspRequestAs___redArg___closed__0));
v___x_474_ = lean_io_error_to_string(v_a_472_);
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
lean_dec_ref(v___x_474_);
v___x_476_ = lean_mk_io_user_error(v___x_475_);
v___x_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object* v_h_483_, lean_object* v_expectedMethod_484_, lean_object* v_inst_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_IO_FS_Stream_readLspRequestAs___redArg(v_h_483_, v_expectedMethod_484_, v_inst_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object* v_h_488_, lean_object* v_expectedMethod_489_, lean_object* v_00_u03b1_490_, lean_object* v_inst_491_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_IO_FS_Stream_readLspRequestAs___redArg(v_h_488_, v_expectedMethod_489_, v_inst_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___boxed(lean_object* v_h_494_, lean_object* v_expectedMethod_495_, lean_object* v_00_u03b1_496_, lean_object* v_inst_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_IO_FS_Stream_readLspRequestAs(v_h_494_, v_expectedMethod_495_, v_00_u03b1_496_, v_inst_497_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg(lean_object* v_h_501_, lean_object* v_expectedMethod_502_, lean_object* v_inst_503_){
_start:
{
lean_object* v_a_506_; lean_object* v___x_512_; 
lean_inc_ref(v_h_501_);
v___x_512_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(v_h_501_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_514_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
lean_dec_ref(v___x_512_);
v___x_514_ = l_IO_FS_Stream_readNotificationAs___redArg(v_h_501_, v_a_513_, v_expectedMethod_502_, v_inst_503_);
lean_dec(v_a_513_);
if (lean_obj_tag(v___x_514_) == 0)
{
return v___x_514_;
}
else
{
lean_object* v_a_515_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v___x_514_);
v_a_506_ = v_a_515_;
goto v___jp_505_;
}
}
else
{
lean_object* v_a_516_; 
lean_dec_ref(v_inst_503_);
lean_dec_ref(v_expectedMethod_502_);
lean_dec_ref(v_h_501_);
v_a_516_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_516_);
lean_dec_ref(v___x_512_);
v_a_506_ = v_a_516_;
goto v___jp_505_;
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_507_ = ((lean_object*)(l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0));
v___x_508_ = lean_io_error_to_string(v_a_506_);
v___x_509_ = lean_string_append(v___x_507_, v___x_508_);
lean_dec_ref(v___x_508_);
v___x_510_ = lean_mk_io_user_error(v___x_509_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object* v_h_517_, lean_object* v_expectedMethod_518_, lean_object* v_inst_519_, lean_object* v_a_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_IO_FS_Stream_readLspNotificationAs___redArg(v_h_517_, v_expectedMethod_518_, v_inst_519_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object* v_h_522_, lean_object* v_expectedMethod_523_, lean_object* v_00_u03b1_524_, lean_object* v_inst_525_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_IO_FS_Stream_readLspNotificationAs___redArg(v_h_522_, v_expectedMethod_523_, v_inst_525_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___boxed(lean_object* v_h_528_, lean_object* v_expectedMethod_529_, lean_object* v_00_u03b1_530_, lean_object* v_inst_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_IO_FS_Stream_readLspNotificationAs(v_h_528_, v_expectedMethod_529_, v_00_u03b1_530_, v_inst_531_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg(lean_object* v_h_535_, lean_object* v_expectedID_536_, lean_object* v_inst_537_){
_start:
{
lean_object* v_a_540_; lean_object* v___x_546_; 
lean_inc_ref(v_h_535_);
v___x_546_ = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(v_h_535_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref(v___x_546_);
v___x_548_ = l_IO_FS_Stream_readResponseAs___redArg(v_h_535_, v_a_547_, v_expectedID_536_, v_inst_537_);
lean_dec(v_a_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
return v___x_548_;
}
else
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v___x_548_);
v_a_540_ = v_a_549_;
goto v___jp_539_;
}
}
else
{
lean_object* v_a_550_; 
lean_dec_ref(v_inst_537_);
lean_dec(v_expectedID_536_);
lean_dec_ref(v_h_535_);
v_a_550_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_550_);
lean_dec_ref(v___x_546_);
v_a_540_ = v_a_550_;
goto v___jp_539_;
}
v___jp_539_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_541_ = ((lean_object*)(l_IO_FS_Stream_readLspResponseAs___redArg___closed__0));
v___x_542_ = lean_io_error_to_string(v_a_540_);
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = lean_mk_io_user_error(v___x_543_);
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object* v_h_551_, lean_object* v_expectedID_552_, lean_object* v_inst_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_IO_FS_Stream_readLspResponseAs___redArg(v_h_551_, v_expectedID_552_, v_inst_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object* v_h_556_, lean_object* v_expectedID_557_, lean_object* v_00_u03b1_558_, lean_object* v_inst_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_IO_FS_Stream_readLspResponseAs___redArg(v_h_556_, v_expectedID_557_, v_inst_559_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___boxed(lean_object* v_h_562_, lean_object* v_expectedID_563_, lean_object* v_00_u03b1_564_, lean_object* v_inst_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_IO_FS_Stream_readLspResponseAs(v_h_562_, v_expectedID_563_, v_00_u03b1_564_, v_inst_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage(lean_object* v_h_570_, lean_object* v_msg_571_){
_start:
{
lean_object* v_flush_573_; lean_object* v_putStr_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_header_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_flush_573_ = lean_ctor_get(v_h_570_, 0);
lean_inc_ref(v_flush_573_);
v_putStr_574_ = lean_ctor_get(v_h_570_, 4);
lean_inc_ref(v_putStr_574_);
lean_dec_ref(v_h_570_);
v___x_575_ = ((lean_object*)(l_IO_FS_Stream_writeSerializedLspMessage___closed__0));
v___x_576_ = lean_string_utf8_byte_size(v_msg_571_);
v___x_577_ = l_Nat_reprFast(v___x_576_);
v___x_578_ = lean_string_append(v___x_575_, v___x_577_);
lean_dec_ref(v___x_577_);
v___x_579_ = ((lean_object*)(l_IO_FS_Stream_writeSerializedLspMessage___closed__1));
v_header_580_ = lean_string_append(v___x_578_, v___x_579_);
v___x_581_ = lean_string_append(v_header_580_, v_msg_571_);
v___x_582_ = lean_apply_2(v_putStr_574_, v___x_581_, lean_box(0));
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v___x_583_; 
lean_dec_ref(v___x_582_);
v___x_583_ = lean_apply_1(v_flush_573_, lean_box(0));
return v___x_583_;
}
else
{
lean_dec_ref(v_flush_573_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object* v_h_584_, lean_object* v_msg_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_IO_FS_Stream_writeSerializedLspMessage(v_h_584_, v_msg_585_);
lean_dec_ref(v_msg_585_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(lean_object* v_k_588_, lean_object* v_x_589_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
lean_object* v___x_590_; 
lean_dec_ref(v_k_588_);
v___x_590_ = lean_box(0);
return v___x_590_;
}
else
{
lean_object* v_val_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v_val_591_ = lean_ctor_get(v_x_589_, 0);
lean_inc(v_val_591_);
lean_dec_ref(v_x_589_);
v___x_592_ = l_Lean_Json_Structured_toJson(v_val_591_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_k_588_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = lean_box(0);
v___x_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(lean_object* v_k_596_, lean_object* v_x_597_){
_start:
{
if (lean_obj_tag(v_x_597_) == 0)
{
lean_object* v___x_598_; 
lean_dec_ref(v_k_596_);
v___x_598_ = lean_box(0);
return v___x_598_;
}
else
{
lean_object* v_val_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_val_599_ = lean_ctor_get(v_x_597_, 0);
lean_inc(v_val_599_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v_k_596_);
lean_ctor_set(v___x_600_, 1, v_val_599_);
v___x_601_ = lean_box(0);
v___x_602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1___boxed(lean_object* v_k_603_, lean_object* v_x_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(v_k_603_, v_x_604_);
lean_dec(v_x_604_);
return v_res_605_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__12(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(32700u);
v___x_622_ = lean_nat_to_int(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__13(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__12, &l_IO_FS_Stream_writeLspMessage___closed__12_once, _init_l_IO_FS_Stream_writeLspMessage___closed__12);
v___x_624_ = lean_int_neg(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__14(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__13, &l_IO_FS_Stream_writeLspMessage___closed__13_once, _init_l_IO_FS_Stream_writeLspMessage___closed__13);
v___x_626_ = l_Lean_JsonNumber_fromInt(v___x_625_);
return v___x_626_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__15(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__14, &l_IO_FS_Stream_writeLspMessage___closed__14_once, _init_l_IO_FS_Stream_writeLspMessage___closed__14);
v___x_628_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__16(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = lean_unsigned_to_nat(32600u);
v___x_630_ = lean_nat_to_int(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__17(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__16, &l_IO_FS_Stream_writeLspMessage___closed__16_once, _init_l_IO_FS_Stream_writeLspMessage___closed__16);
v___x_632_ = lean_int_neg(v___x_631_);
return v___x_632_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__18(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__17, &l_IO_FS_Stream_writeLspMessage___closed__17_once, _init_l_IO_FS_Stream_writeLspMessage___closed__17);
v___x_634_ = l_Lean_JsonNumber_fromInt(v___x_633_);
return v___x_634_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__19(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__18, &l_IO_FS_Stream_writeLspMessage___closed__18_once, _init_l_IO_FS_Stream_writeLspMessage___closed__18);
v___x_636_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__20(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_637_ = lean_unsigned_to_nat(32601u);
v___x_638_ = lean_nat_to_int(v___x_637_);
return v___x_638_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__21(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__20, &l_IO_FS_Stream_writeLspMessage___closed__20_once, _init_l_IO_FS_Stream_writeLspMessage___closed__20);
v___x_640_ = lean_int_neg(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__22(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__21, &l_IO_FS_Stream_writeLspMessage___closed__21_once, _init_l_IO_FS_Stream_writeLspMessage___closed__21);
v___x_642_ = l_Lean_JsonNumber_fromInt(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__23(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__22, &l_IO_FS_Stream_writeLspMessage___closed__22_once, _init_l_IO_FS_Stream_writeLspMessage___closed__22);
v___x_644_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__24(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_unsigned_to_nat(32602u);
v___x_646_ = lean_nat_to_int(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__25(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__24, &l_IO_FS_Stream_writeLspMessage___closed__24_once, _init_l_IO_FS_Stream_writeLspMessage___closed__24);
v___x_648_ = lean_int_neg(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__26(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__25, &l_IO_FS_Stream_writeLspMessage___closed__25_once, _init_l_IO_FS_Stream_writeLspMessage___closed__25);
v___x_650_ = l_Lean_JsonNumber_fromInt(v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__27(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__26, &l_IO_FS_Stream_writeLspMessage___closed__26_once, _init_l_IO_FS_Stream_writeLspMessage___closed__26);
v___x_652_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__28(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = lean_unsigned_to_nat(32603u);
v___x_654_ = lean_nat_to_int(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__29(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__28, &l_IO_FS_Stream_writeLspMessage___closed__28_once, _init_l_IO_FS_Stream_writeLspMessage___closed__28);
v___x_656_ = lean_int_neg(v___x_655_);
return v___x_656_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__30(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__29, &l_IO_FS_Stream_writeLspMessage___closed__29_once, _init_l_IO_FS_Stream_writeLspMessage___closed__29);
v___x_658_ = l_Lean_JsonNumber_fromInt(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__31(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__30, &l_IO_FS_Stream_writeLspMessage___closed__30_once, _init_l_IO_FS_Stream_writeLspMessage___closed__30);
v___x_660_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
return v___x_660_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__32(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = lean_unsigned_to_nat(32002u);
v___x_662_ = lean_nat_to_int(v___x_661_);
return v___x_662_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__33(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__32, &l_IO_FS_Stream_writeLspMessage___closed__32_once, _init_l_IO_FS_Stream_writeLspMessage___closed__32);
v___x_664_ = lean_int_neg(v___x_663_);
return v___x_664_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__34(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__33, &l_IO_FS_Stream_writeLspMessage___closed__33_once, _init_l_IO_FS_Stream_writeLspMessage___closed__33);
v___x_666_ = l_Lean_JsonNumber_fromInt(v___x_665_);
return v___x_666_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__35(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__34, &l_IO_FS_Stream_writeLspMessage___closed__34_once, _init_l_IO_FS_Stream_writeLspMessage___closed__34);
v___x_668_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__36(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_unsigned_to_nat(32001u);
v___x_670_ = lean_nat_to_int(v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__37(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__36, &l_IO_FS_Stream_writeLspMessage___closed__36_once, _init_l_IO_FS_Stream_writeLspMessage___closed__36);
v___x_672_ = lean_int_neg(v___x_671_);
return v___x_672_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__38(void){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__37, &l_IO_FS_Stream_writeLspMessage___closed__37_once, _init_l_IO_FS_Stream_writeLspMessage___closed__37);
v___x_674_ = l_Lean_JsonNumber_fromInt(v___x_673_);
return v___x_674_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__39(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__38, &l_IO_FS_Stream_writeLspMessage___closed__38_once, _init_l_IO_FS_Stream_writeLspMessage___closed__38);
v___x_676_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__40(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = lean_unsigned_to_nat(32801u);
v___x_678_ = lean_nat_to_int(v___x_677_);
return v___x_678_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__41(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__40, &l_IO_FS_Stream_writeLspMessage___closed__40_once, _init_l_IO_FS_Stream_writeLspMessage___closed__40);
v___x_680_ = lean_int_neg(v___x_679_);
return v___x_680_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__42(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__41, &l_IO_FS_Stream_writeLspMessage___closed__41_once, _init_l_IO_FS_Stream_writeLspMessage___closed__41);
v___x_682_ = l_Lean_JsonNumber_fromInt(v___x_681_);
return v___x_682_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__43(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__42, &l_IO_FS_Stream_writeLspMessage___closed__42_once, _init_l_IO_FS_Stream_writeLspMessage___closed__42);
v___x_684_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__44(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_unsigned_to_nat(32800u);
v___x_686_ = lean_nat_to_int(v___x_685_);
return v___x_686_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__45(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__44, &l_IO_FS_Stream_writeLspMessage___closed__44_once, _init_l_IO_FS_Stream_writeLspMessage___closed__44);
v___x_688_ = lean_int_neg(v___x_687_);
return v___x_688_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__46(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__45, &l_IO_FS_Stream_writeLspMessage___closed__45_once, _init_l_IO_FS_Stream_writeLspMessage___closed__45);
v___x_690_ = l_Lean_JsonNumber_fromInt(v___x_689_);
return v___x_690_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__47(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__46, &l_IO_FS_Stream_writeLspMessage___closed__46_once, _init_l_IO_FS_Stream_writeLspMessage___closed__46);
v___x_692_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__48(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_unsigned_to_nat(32900u);
v___x_694_ = lean_nat_to_int(v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__49(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__48, &l_IO_FS_Stream_writeLspMessage___closed__48_once, _init_l_IO_FS_Stream_writeLspMessage___closed__48);
v___x_696_ = lean_int_neg(v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__50(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__49, &l_IO_FS_Stream_writeLspMessage___closed__49_once, _init_l_IO_FS_Stream_writeLspMessage___closed__49);
v___x_698_ = l_Lean_JsonNumber_fromInt(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__51(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__50, &l_IO_FS_Stream_writeLspMessage___closed__50_once, _init_l_IO_FS_Stream_writeLspMessage___closed__50);
v___x_700_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__52(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_unsigned_to_nat(32901u);
v___x_702_ = lean_nat_to_int(v___x_701_);
return v___x_702_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__53(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__52, &l_IO_FS_Stream_writeLspMessage___closed__52_once, _init_l_IO_FS_Stream_writeLspMessage___closed__52);
v___x_704_ = lean_int_neg(v___x_703_);
return v___x_704_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__54(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_705_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__53, &l_IO_FS_Stream_writeLspMessage___closed__53_once, _init_l_IO_FS_Stream_writeLspMessage___closed__53);
v___x_706_ = l_Lean_JsonNumber_fromInt(v___x_705_);
return v___x_706_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__55(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__54, &l_IO_FS_Stream_writeLspMessage___closed__54_once, _init_l_IO_FS_Stream_writeLspMessage___closed__54);
v___x_708_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__56(void){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(32902u);
v___x_710_ = lean_nat_to_int(v___x_709_);
return v___x_710_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__57(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__56, &l_IO_FS_Stream_writeLspMessage___closed__56_once, _init_l_IO_FS_Stream_writeLspMessage___closed__56);
v___x_712_ = lean_int_neg(v___x_711_);
return v___x_712_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__58(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__57, &l_IO_FS_Stream_writeLspMessage___closed__57_once, _init_l_IO_FS_Stream_writeLspMessage___closed__57);
v___x_714_ = l_Lean_JsonNumber_fromInt(v___x_713_);
return v___x_714_;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__59(void){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__58, &l_IO_FS_Stream_writeLspMessage___closed__58_once, _init_l_IO_FS_Stream_writeLspMessage___closed__58);
v___x_716_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object* v_h_717_, lean_object* v_msg_718_){
_start:
{
lean_object* v___x_720_; lean_object* v___y_722_; 
v___x_720_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__3));
switch(lean_obj_tag(v_msg_718_))
{
case 0:
{
lean_object* v_id_727_; lean_object* v_method_728_; lean_object* v_params_x3f_729_; lean_object* v___x_730_; lean_object* v___y_732_; 
v_id_727_ = lean_ctor_get(v_msg_718_, 0);
lean_inc(v_id_727_);
v_method_728_ = lean_ctor_get(v_msg_718_, 1);
lean_inc_ref(v_method_728_);
v_params_x3f_729_ = lean_ctor_get(v_msg_718_, 2);
lean_inc(v_params_x3f_729_);
lean_dec_ref(v_msg_718_);
v___x_730_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_727_))
{
case 0:
{
lean_object* v_s_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
v_s_743_ = lean_ctor_get(v_id_727_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v_id_727_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v_id_727_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_s_743_);
lean_dec(v_id_727_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 3);
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_s_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
v___y_732_ = v___x_748_;
goto v___jp_731_;
}
}
}
case 1:
{
lean_object* v_n_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_n_751_ = lean_ctor_get(v_id_727_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_id_727_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v_id_727_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_n_751_);
lean_dec(v_id_727_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 2);
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_n_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
v___y_732_ = v___x_756_;
goto v___jp_731_;
}
}
}
default: 
{
lean_object* v___x_759_; 
v___x_759_ = lean_box(0);
v___y_732_ = v___x_759_;
goto v___jp_731_;
}
}
v___jp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_730_);
lean_ctor_set(v___x_733_, 1, v___y_732_);
v___x_734_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__5));
v___x_735_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_735_, 0, v_method_728_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_box(0);
v___x_738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_739_, 0, v___x_733_);
lean_ctor_set(v___x_739_, 1, v___x_738_);
v___x_740_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__6));
v___x_741_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(v___x_740_, v_params_x3f_729_);
v___x_742_ = l_List_appendTR___redArg(v___x_739_, v___x_741_);
v___y_722_ = v___x_742_;
goto v___jp_721_;
}
}
case 1:
{
lean_object* v_method_760_; lean_object* v_params_x3f_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_773_; 
v_method_760_ = lean_ctor_get(v_msg_718_, 0);
v_params_x3f_761_ = lean_ctor_get(v_msg_718_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_msg_718_);
if (v_isSharedCheck_773_ == 0)
{
v___x_763_ = v_msg_718_;
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_params_x3f_761_);
lean_inc(v_method_760_);
lean_dec(v_msg_718_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_773_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_765_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__5));
v___x_766_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_766_, 0, v_method_760_);
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 0);
lean_ctor_set(v___x_763_, 1, v___x_766_);
lean_ctor_set(v___x_763_, 0, v___x_765_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_772_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__6));
v___x_770_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(v___x_769_, v_params_x3f_761_);
v___x_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_768_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___y_722_ = v___x_771_;
goto v___jp_721_;
}
}
}
case 2:
{
lean_object* v_id_774_; lean_object* v_result_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_807_; 
v_id_774_ = lean_ctor_get(v_msg_718_, 0);
v_result_775_ = lean_ctor_get(v_msg_718_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_msg_718_);
if (v_isSharedCheck_807_ == 0)
{
v___x_777_ = v_msg_718_;
v_isShared_778_ = v_isSharedCheck_807_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_result_775_);
lean_inc(v_id_774_);
lean_dec(v_msg_718_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_807_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v___y_781_; 
v___x_779_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_774_))
{
case 0:
{
lean_object* v_s_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_s_790_ = lean_ctor_get(v_id_774_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v_id_774_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v_id_774_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_s_790_);
lean_dec(v_id_774_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 3);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_s_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v___y_781_ = v___x_795_;
goto v___jp_780_;
}
}
}
case 1:
{
lean_object* v_n_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_n_798_ = lean_ctor_get(v_id_774_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_id_774_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v_id_774_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_n_798_);
lean_dec(v_id_774_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set_tag(v___x_800_, 2);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_n_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v___y_781_ = v___x_803_;
goto v___jp_780_;
}
}
}
default: 
{
lean_object* v___x_806_; 
v___x_806_ = lean_box(0);
v___y_781_ = v___x_806_;
goto v___jp_780_;
}
}
v___jp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set_tag(v___x_777_, 0);
lean_ctor_set(v___x_777_, 1, v___y_781_);
lean_ctor_set(v___x_777_, 0, v___x_779_);
v___x_783_ = v___x_777_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_779_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___y_781_);
v___x_783_ = v_reuseFailAlloc_789_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_784_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__7));
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_784_);
lean_ctor_set(v___x_785_, 1, v_result_775_);
v___x_786_ = lean_box(0);
v___x_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_783_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
v___y_722_ = v___x_788_;
goto v___jp_721_;
}
}
}
}
default: 
{
lean_object* v_id_808_; uint8_t v_code_809_; lean_object* v_message_810_; lean_object* v_data_x3f_811_; lean_object* v___y_813_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v___y_816_; lean_object* v___x_831_; lean_object* v___y_833_; 
v_id_808_ = lean_ctor_get(v_msg_718_, 0);
lean_inc(v_id_808_);
v_code_809_ = lean_ctor_get_uint8(v_msg_718_, sizeof(void*)*3);
v_message_810_ = lean_ctor_get(v_msg_718_, 1);
lean_inc_ref(v_message_810_);
v_data_x3f_811_ = lean_ctor_get(v_msg_718_, 2);
lean_inc(v_data_x3f_811_);
lean_dec_ref(v_msg_718_);
v___x_831_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__4));
switch(lean_obj_tag(v_id_808_))
{
case 0:
{
lean_object* v_s_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_s_849_ = lean_ctor_get(v_id_808_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_id_808_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v_id_808_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_s_849_);
lean_dec(v_id_808_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set_tag(v___x_851_, 3);
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_s_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
v___y_833_ = v___x_854_;
goto v___jp_832_;
}
}
}
case 1:
{
lean_object* v_n_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
v_n_857_ = lean_ctor_get(v_id_808_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v_id_808_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v_id_808_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_n_857_);
lean_dec(v_id_808_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set_tag(v___x_859_, 2);
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_n_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
v___y_833_ = v___x_862_;
goto v___jp_832_;
}
}
}
default: 
{
lean_object* v___x_865_; 
v___x_865_ = lean_box(0);
v___y_833_ = v___x_865_;
goto v___jp_832_;
}
}
v___jp_812_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_inc(v___y_816_);
lean_inc_ref(v___y_814_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___y_814_);
lean_ctor_set(v___x_817_, 1, v___y_816_);
v___x_818_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__8));
v___x_819_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_819_, 0, v_message_810_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_817_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__9));
v___x_825_ = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(v___x_824_, v_data_x3f_811_);
lean_dec(v_data_x3f_811_);
v___x_826_ = l_List_appendTR___redArg(v___x_823_, v___x_825_);
v___x_827_ = l_Lean_Json_mkObj(v___x_826_);
lean_inc_ref(v___y_813_);
v___x_828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_828_, 0, v___y_813_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_821_);
v___x_830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_830_, 0, v___y_815_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___y_722_ = v___x_830_;
goto v___jp_721_;
}
v___jp_832_:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_831_);
lean_ctor_set(v___x_834_, 1, v___y_833_);
v___x_835_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__10));
v___x_836_ = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__11));
switch(v_code_809_)
{
case 0:
{
lean_object* v___x_837_; 
v___x_837_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__15, &l_IO_FS_Stream_writeLspMessage___closed__15_once, _init_l_IO_FS_Stream_writeLspMessage___closed__15);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_837_;
goto v___jp_812_;
}
case 1:
{
lean_object* v___x_838_; 
v___x_838_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__19, &l_IO_FS_Stream_writeLspMessage___closed__19_once, _init_l_IO_FS_Stream_writeLspMessage___closed__19);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_838_;
goto v___jp_812_;
}
case 2:
{
lean_object* v___x_839_; 
v___x_839_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__23, &l_IO_FS_Stream_writeLspMessage___closed__23_once, _init_l_IO_FS_Stream_writeLspMessage___closed__23);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_839_;
goto v___jp_812_;
}
case 3:
{
lean_object* v___x_840_; 
v___x_840_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__27, &l_IO_FS_Stream_writeLspMessage___closed__27_once, _init_l_IO_FS_Stream_writeLspMessage___closed__27);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_840_;
goto v___jp_812_;
}
case 4:
{
lean_object* v___x_841_; 
v___x_841_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__31, &l_IO_FS_Stream_writeLspMessage___closed__31_once, _init_l_IO_FS_Stream_writeLspMessage___closed__31);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_841_;
goto v___jp_812_;
}
case 5:
{
lean_object* v___x_842_; 
v___x_842_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__35, &l_IO_FS_Stream_writeLspMessage___closed__35_once, _init_l_IO_FS_Stream_writeLspMessage___closed__35);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_842_;
goto v___jp_812_;
}
case 6:
{
lean_object* v___x_843_; 
v___x_843_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__39, &l_IO_FS_Stream_writeLspMessage___closed__39_once, _init_l_IO_FS_Stream_writeLspMessage___closed__39);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_843_;
goto v___jp_812_;
}
case 7:
{
lean_object* v___x_844_; 
v___x_844_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__43, &l_IO_FS_Stream_writeLspMessage___closed__43_once, _init_l_IO_FS_Stream_writeLspMessage___closed__43);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_844_;
goto v___jp_812_;
}
case 8:
{
lean_object* v___x_845_; 
v___x_845_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__47, &l_IO_FS_Stream_writeLspMessage___closed__47_once, _init_l_IO_FS_Stream_writeLspMessage___closed__47);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_845_;
goto v___jp_812_;
}
case 9:
{
lean_object* v___x_846_; 
v___x_846_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__51, &l_IO_FS_Stream_writeLspMessage___closed__51_once, _init_l_IO_FS_Stream_writeLspMessage___closed__51);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_846_;
goto v___jp_812_;
}
case 10:
{
lean_object* v___x_847_; 
v___x_847_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__55, &l_IO_FS_Stream_writeLspMessage___closed__55_once, _init_l_IO_FS_Stream_writeLspMessage___closed__55);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_847_;
goto v___jp_812_;
}
default: 
{
lean_object* v___x_848_; 
v___x_848_ = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__59, &l_IO_FS_Stream_writeLspMessage___closed__59_once, _init_l_IO_FS_Stream_writeLspMessage___closed__59);
v___y_813_ = v___x_835_;
v___y_814_ = v___x_836_;
v___y_815_ = v___x_834_;
v___y_816_ = v___x_848_;
goto v___jp_812_;
}
}
}
}
}
v___jp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_720_);
lean_ctor_set(v___x_723_, 1, v___y_722_);
v___x_724_ = l_Lean_Json_mkObj(v___x_723_);
v___x_725_ = l_Lean_Json_compress(v___x_724_);
v___x_726_ = l_IO_FS_Stream_writeSerializedLspMessage(v_h_717_, v___x_725_);
lean_dec_ref(v___x_725_);
return v___x_726_;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage___boxed(lean_object* v_h_866_, lean_object* v_msg_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_IO_FS_Stream_writeLspMessage(v_h_866_, v_msg_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object* v_inst_870_, lean_object* v_h_871_, lean_object* v_r_872_){
_start:
{
lean_object* v_id_874_; lean_object* v_method_875_; lean_object* v_param_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_896_; 
v_id_874_ = lean_ctor_get(v_r_872_, 0);
v_method_875_ = lean_ctor_get(v_r_872_, 1);
v_param_876_ = lean_ctor_get(v_r_872_, 2);
v_isSharedCheck_896_ = !lean_is_exclusive(v_r_872_);
if (v_isSharedCheck_896_ == 0)
{
v___x_878_ = v_r_872_;
v_isShared_879_ = v_isSharedCheck_896_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_param_876_);
lean_inc(v_method_875_);
lean_inc(v_id_874_);
lean_dec(v_r_872_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_896_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___y_881_; lean_object* v___x_886_; 
v___x_886_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_870_, v_param_876_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v___x_887_; 
lean_dec_ref(v___x_886_);
v___x_887_ = lean_box(0);
v___y_881_ = v___x_887_;
goto v___jp_880_;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
v_a_888_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_886_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_886_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
v___y_881_ = v___x_893_;
goto v___jp_880_;
}
}
}
v___jp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 2, v___y_881_);
v___x_883_ = v___x_878_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_id_874_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_method_875_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v___y_881_);
v___x_883_ = v_reuseFailAlloc_885_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v___x_884_; 
v___x_884_ = l_IO_FS_Stream_writeLspMessage(v_h_871_, v___x_883_);
return v___x_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object* v_inst_897_, lean_object* v_h_898_, lean_object* v_r_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_IO_FS_Stream_writeLspRequest___redArg(v_inst_897_, v_h_898_, v_r_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object* v_00_u03b1_902_, lean_object* v_inst_903_, lean_object* v_h_904_, lean_object* v_r_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_IO_FS_Stream_writeLspRequest___redArg(v_inst_903_, v_h_904_, v_r_905_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___boxed(lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_h_910_, lean_object* v_r_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_IO_FS_Stream_writeLspRequest(v_00_u03b1_908_, v_inst_909_, v_h_910_, v_r_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object* v_inst_914_, lean_object* v_h_915_, lean_object* v_n_916_){
_start:
{
lean_object* v_method_918_; lean_object* v_param_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_939_; 
v_method_918_ = lean_ctor_get(v_n_916_, 0);
v_param_919_ = lean_ctor_get(v_n_916_, 1);
v_isSharedCheck_939_ = !lean_is_exclusive(v_n_916_);
if (v_isSharedCheck_939_ == 0)
{
v___x_921_ = v_n_916_;
v_isShared_922_ = v_isSharedCheck_939_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_param_919_);
lean_inc(v_method_918_);
lean_dec(v_n_916_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_939_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___y_924_; lean_object* v___x_929_; 
v___x_929_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_914_, v_param_919_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v___x_930_; 
lean_dec_ref(v___x_929_);
v___x_930_ = lean_box(0);
v___y_924_ = v___x_930_;
goto v___jp_923_;
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_a_931_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_929_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_929_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
v___y_924_ = v___x_936_;
goto v___jp_923_;
}
}
}
v___jp_923_:
{
lean_object* v___x_926_; 
if (v_isShared_922_ == 0)
{
lean_ctor_set_tag(v___x_921_, 1);
lean_ctor_set(v___x_921_, 1, v___y_924_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_method_918_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v___y_924_);
v___x_926_ = v_reuseFailAlloc_928_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; 
v___x_927_ = l_IO_FS_Stream_writeLspMessage(v_h_915_, v___x_926_);
return v___x_927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object* v_inst_940_, lean_object* v_h_941_, lean_object* v_n_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_IO_FS_Stream_writeLspNotification___redArg(v_inst_940_, v_h_941_, v_n_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object* v_00_u03b1_945_, lean_object* v_inst_946_, lean_object* v_h_947_, lean_object* v_n_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_IO_FS_Stream_writeLspNotification___redArg(v_inst_946_, v_h_947_, v_n_948_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___boxed(lean_object* v_00_u03b1_951_, lean_object* v_inst_952_, lean_object* v_h_953_, lean_object* v_n_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_IO_FS_Stream_writeLspNotification(v_00_u03b1_951_, v_inst_952_, v_h_953_, v_n_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg(lean_object* v_inst_957_, lean_object* v_h_958_, lean_object* v_r_959_){
_start:
{
lean_object* v_id_961_; lean_object* v_result_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_971_; 
v_id_961_ = lean_ctor_get(v_r_959_, 0);
v_result_962_ = lean_ctor_get(v_r_959_, 1);
v_isSharedCheck_971_ = !lean_is_exclusive(v_r_959_);
if (v_isSharedCheck_971_ == 0)
{
v___x_964_ = v_r_959_;
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_result_962_);
lean_inc(v_id_961_);
lean_dec(v_r_959_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_apply_1(v_inst_957_, v_result_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 2);
lean_ctor_set(v___x_964_, 1, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_id_961_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_970_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; 
v___x_969_ = l_IO_FS_Stream_writeLspMessage(v_h_958_, v___x_968_);
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object* v_inst_972_, lean_object* v_h_973_, lean_object* v_r_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_IO_FS_Stream_writeLspResponse___redArg(v_inst_972_, v_h_973_, v_r_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object* v_00_u03b1_977_, lean_object* v_inst_978_, lean_object* v_h_979_, lean_object* v_r_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_IO_FS_Stream_writeLspResponse___redArg(v_inst_978_, v_h_979_, v_r_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___boxed(lean_object* v_00_u03b1_983_, lean_object* v_inst_984_, lean_object* v_h_985_, lean_object* v_r_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_IO_FS_Stream_writeLspResponse(v_00_u03b1_983_, v_inst_984_, v_h_985_, v_r_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object* v_h_989_, lean_object* v_e_990_){
_start:
{
lean_object* v_id_992_; uint8_t v_code_993_; lean_object* v_message_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1003_; 
v_id_992_ = lean_ctor_get(v_e_990_, 0);
v_code_993_ = lean_ctor_get_uint8(v_e_990_, sizeof(void*)*3);
v_message_994_ = lean_ctor_get(v_e_990_, 1);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_e_990_);
if (v_isSharedCheck_1003_ == 0)
{
lean_object* v_unused_1004_; 
v_unused_1004_ = lean_ctor_get(v_e_990_, 2);
lean_dec(v_unused_1004_);
v___x_996_ = v_e_990_;
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_message_994_);
lean_inc(v_id_992_);
lean_dec(v_e_990_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_1000_; 
v___x_998_ = lean_box(0);
if (v_isShared_997_ == 0)
{
lean_ctor_set_tag(v___x_996_, 3);
lean_ctor_set(v___x_996_, 2, v___x_998_);
v___x_1000_ = v___x_996_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_id_992_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_message_994_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v___x_998_);
lean_ctor_set_uint8(v_reuseFailAlloc_1002_, sizeof(void*)*3, v_code_993_);
v___x_1000_ = v_reuseFailAlloc_1002_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_IO_FS_Stream_writeLspMessage(v_h_989_, v___x_1000_);
return v___x_1001_;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object* v_h_1005_, lean_object* v_e_1006_, lean_object* v_a_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_IO_FS_Stream_writeLspResponseError(v_h_1005_, v_e_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object* v_inst_1009_, lean_object* v_h_1010_, lean_object* v_e_1011_){
_start:
{
lean_object* v_id_1013_; uint8_t v_code_1014_; lean_object* v_message_1015_; lean_object* v_data_x3f_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1036_; 
v_id_1013_ = lean_ctor_get(v_e_1011_, 0);
v_code_1014_ = lean_ctor_get_uint8(v_e_1011_, sizeof(void*)*3);
v_message_1015_ = lean_ctor_get(v_e_1011_, 1);
v_data_x3f_1016_ = lean_ctor_get(v_e_1011_, 2);
v_isSharedCheck_1036_ = !lean_is_exclusive(v_e_1011_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1018_ = v_e_1011_;
v_isShared_1019_ = v_isSharedCheck_1036_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_data_x3f_1016_);
lean_inc(v_message_1015_);
lean_inc(v_id_1013_);
lean_dec(v_e_1011_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1036_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___y_1021_; 
if (lean_obj_tag(v_data_x3f_1016_) == 0)
{
lean_object* v___x_1026_; 
lean_dec_ref(v_inst_1009_);
v___x_1026_ = lean_box(0);
v___y_1021_ = v___x_1026_;
goto v___jp_1020_;
}
else
{
lean_object* v_val_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1035_; 
v_val_1027_ = lean_ctor_get(v_data_x3f_1016_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v_data_x3f_1016_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1029_ = v_data_x3f_1016_;
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_val_1027_);
lean_dec(v_data_x3f_1016_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1035_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1031_; lean_object* v___x_1033_; 
v___x_1031_ = lean_apply_1(v_inst_1009_, v_val_1027_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1031_);
v___x_1033_ = v___x_1029_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
v___y_1021_ = v___x_1033_;
goto v___jp_1020_;
}
}
}
v___jp_1020_:
{
lean_object* v___x_1023_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set_tag(v___x_1018_, 3);
lean_ctor_set(v___x_1018_, 2, v___y_1021_);
v___x_1023_ = v___x_1018_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_id_1013_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_message_1015_);
lean_ctor_set(v_reuseFailAlloc_1025_, 2, v___y_1021_);
lean_ctor_set_uint8(v_reuseFailAlloc_1025_, sizeof(void*)*3, v_code_1014_);
v___x_1023_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_IO_FS_Stream_writeLspMessage(v_h_1010_, v___x_1023_);
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object* v_inst_1037_, lean_object* v_h_1038_, lean_object* v_e_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1037_, v_h_1038_, v_e_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* v_00_u03b1_1042_, lean_object* v_inst_1043_, lean_object* v_h_1044_, lean_object* v_e_1045_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(v_inst_1043_, v_h_1044_, v_e_1045_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_inst_1049_, lean_object* v_h_1050_, lean_object* v_e_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_IO_FS_Stream_writeLspResponseErrorWithData(v_00_u03b1_1048_, v_inst_1049_, v_h_1050_, v_e_1051_);
return v_res_1053_;
}
}
lean_object* runtime_initialize_Lean_Data_JsonRpc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Communication(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

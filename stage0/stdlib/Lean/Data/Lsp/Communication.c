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
static const lean_string_object l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2;
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3;
lean_object* l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\r\n"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1_value;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
uint8_t l_String_Slice_beq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_Slice_intercalate(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "seq_num"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1_value;
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* l_Lean_Json_getObjVal_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(lean_object*);
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Invalid header field: "};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0_value;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 176, .m_capacity = 176, .m_length = 175, .m_data = "A Lean 3 request was received. Please ensure that your editor has a Lean 4 compatible extension installed. For VSCode, this is\n\n    https://github.com/leanprover/vscode-lean4 "};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1_value;
lean_object* lean_mk_io_user_error(lean_object*);
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2;
static const lean_string_object l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Stream was closed"};
static const lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3 = (const lean_object*)&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3_value;
static lean_once_cell_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4;
lean_object* l_String_quote(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1_value;
static const lean_string_object l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2 = (const lean_object*)&l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2_value;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0 = (const lean_object*)&l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0_value;
static const lean_string_object l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1 = (const lean_object*)&l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1_value;
static const lean_string_object l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2 = (const lean_object*)&l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2_value;
lean_object* lean_string_push(lean_object*, uint32_t);
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
lean_object* l_String_Slice_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readLspMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Cannot read LSP message: "};
static const lean_object* l_IO_FS_Stream_readLspMessage___closed__0 = (const lean_object*)&l_IO_FS_Stream_readLspMessage___closed__0_value;
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_IO_FS_Stream_readMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Stream_readUTF8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString___boxed(lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readLspRequestAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Cannot read LSP request: "};
static const lean_object* l_IO_FS_Stream_readLspRequestAs___redArg___closed__0 = (const lean_object*)&l_IO_FS_Stream_readLspRequestAs___redArg___closed__0_value;
lean_object* l_IO_FS_Stream_readRequestAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Cannot read LSP notification: "};
static const lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0 = (const lean_object*)&l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0_value;
lean_object* l_IO_FS_Stream_readNotificationAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_readLspResponseAs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Cannot read LSP response: "};
static const lean_object* l_IO_FS_Stream_readLspResponseAs___redArg___closed__0 = (const lean_object*)&l_IO_FS_Stream_readLspResponseAs___redArg___closed__0_value;
lean_object* l_IO_FS_Stream_readResponseAs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_IO_FS_Stream_writeSerializedLspMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Content-Length: "};
static const lean_object* l_IO_FS_Stream_writeSerializedLspMessage___closed__0 = (const lean_object*)&l_IO_FS_Stream_writeSerializedLspMessage___closed__0_value;
static const lean_string_object l_IO_FS_Stream_writeSerializedLspMessage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\r\n\r\n"};
static const lean_object* l_IO_FS_Stream_writeSerializedLspMessage___closed__1 = (const lean_object*)&l_IO_FS_Stream_writeSerializedLspMessage___closed__1_value;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_Structured_toJson(lean_object*);
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
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__12;
lean_object* lean_int_neg(lean_object*);
static lean_once_cell_t l_IO_FS_Stream_writeLspMessage___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_IO_FS_Stream_writeLspMessage___closed__13;
lean_object* l_Lean_JsonNumber_fromInt(lean_object*);
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
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_toStructured_x3f___redArg(lean_object*, lean_object*);
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
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static uint8_t _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1);
x_3 = lean_nat_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__0));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
x_2 = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(x_1);
return x_2;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__4);
x_3 = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
x_4 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__5);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_uint8_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__2);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__6);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__8));
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_118; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_118 = !lean_is_exclusive(x_4);
if (x_118 == 0)
{
x_15 = x_4;
x_16 = x_118;
goto block_117;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = x_118;
goto block_117;
}
block_117:
{
lean_object* x_17; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_51; 
lean_del_object(x_15);
x_39 = lean_ctor_get(x_14, 0);
x_51 = !lean_is_exclusive(x_14);
if (x_51 == 0)
{
x_40 = x_14;
x_41 = x_51;
goto block_50;
}
else
{
lean_inc(x_39);
lean_dec(x_14);
x_40 = lean_box(0);
x_41 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_2, 1);
x_43 = lean_ctor_get(x_2, 2);
x_44 = lean_nat_sub(x_43, x_42);
x_45 = lean_nat_dec_eq(x_39, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
lean_inc(x_39);
if (x_41 == 0)
{
lean_ctor_set_tag(x_40, 1);
x_46 = x_40;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_39);
x_46 = x_48;
goto block_47;
}
block_47:
{
lean_inc(x_39);
x_23 = x_46;
x_24 = x_39;
x_25 = x_39;
goto block_36;
}
}
else
{
lean_object* x_49; 
lean_del_object(x_40);
x_49 = lean_box(3);
lean_inc(x_39);
x_23 = x_49;
x_24 = x_39;
x_25 = x_39;
goto block_36;
}
}
}
case 1:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_60; 
x_52 = lean_ctor_get(x_14, 0);
x_60 = !lean_is_exclusive(x_14);
if (x_60 == 0)
{
x_53 = x_14;
x_54 = x_60;
goto block_59;
}
else
{
lean_inc(x_52);
lean_dec(x_14);
x_53 = lean_box(0);
x_54 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_string_utf8_next_fast(x_1, x_52);
lean_dec(x_52);
if (x_54 == 0)
{
lean_ctor_set_tag(x_53, 0);
lean_ctor_set(x_53, 0, x_55);
x_56 = x_53;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_55);
x_56 = x_58;
goto block_57;
}
block_57:
{
x_17 = x_56;
goto block_22;
}
}
}
case 2:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_116; 
x_61 = lean_ctor_get(x_14, 0);
x_62 = lean_ctor_get(x_14, 1);
x_63 = lean_ctor_get(x_14, 2);
x_64 = lean_ctor_get(x_14, 3);
x_116 = !lean_is_exclusive(x_14);
if (x_116 == 0)
{
x_65 = x_14;
x_66 = x_116;
goto block_115;
}
else
{
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_14);
x_65 = lean_box(0);
x_66 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_61, 0);
x_68 = lean_ctor_get(x_61, 1);
x_69 = lean_ctor_get(x_61, 2);
x_70 = lean_nat_sub(x_63, x_64);
x_71 = lean_nat_sub(x_69, x_68);
x_72 = lean_nat_add(x_70, x_71);
x_73 = lean_nat_dec_le(x_72, x_3);
lean_dec(x_72);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_71);
lean_del_object(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
x_74 = lean_nat_dec_lt(x_70, x_3);
lean_dec(x_70);
if (x_74 == 0)
{
lean_del_object(x_15);
goto block_38;
}
else
{
lean_object* x_75; 
x_75 = lean_box(3);
x_17 = x_75;
goto block_22;
}
}
else
{
uint8_t x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; 
lean_dec(x_70);
lean_inc(x_63);
x_76 = lean_string_get_byte_fast(x_1, x_63);
x_77 = lean_nat_add(x_68, x_64);
x_78 = lean_string_get_byte_fast(x_67, x_77);
x_79 = lean_uint8_dec_eq(x_76, x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
lean_dec(x_71);
x_80 = lean_unsigned_to_nat(0u);
x_81 = lean_nat_dec_eq(x_64, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_sub(x_64, x_82);
lean_dec(x_64);
x_84 = lean_array_fget_borrowed(x_62, x_83);
lean_dec(x_83);
x_85 = lean_nat_dec_eq(x_84, x_80);
if (x_85 == 0)
{
lean_object* x_86; 
lean_inc(x_84);
if (x_66 == 0)
{
lean_ctor_set(x_65, 3, x_84);
x_86 = x_65;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_88, 0, x_61);
lean_ctor_set(x_88, 1, x_62);
lean_ctor_set(x_88, 2, x_63);
lean_ctor_set(x_88, 3, x_84);
x_86 = x_88;
goto block_87;
}
block_87:
{
x_17 = x_86;
goto block_22;
}
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_String_Slice_posGE___redArg(x_2, x_63);
if (x_66 == 0)
{
lean_ctor_set(x_65, 3, x_80);
lean_ctor_set(x_65, 2, x_89);
x_90 = x_65;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_92, 0, x_61);
lean_ctor_set(x_92, 1, x_62);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_80);
x_90 = x_92;
goto block_91;
}
block_91:
{
x_17 = x_90;
goto block_22;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_64);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_63, x_93);
lean_dec(x_63);
x_95 = l_String_Slice_posGE___redArg(x_2, x_94);
if (x_66 == 0)
{
lean_ctor_set(x_65, 3, x_80);
lean_ctor_set(x_65, 2, x_95);
x_96 = x_65;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_98, 0, x_61);
lean_ctor_set(x_98, 1, x_62);
lean_ctor_set(x_98, 2, x_95);
lean_ctor_set(x_98, 3, x_80);
x_96 = x_98;
goto block_97;
}
block_97:
{
x_17 = x_96;
goto block_22;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_del_object(x_15);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_63, x_99);
lean_dec(x_63);
x_101 = lean_nat_add(x_64, x_99);
lean_dec(x_64);
x_102 = lean_nat_dec_eq(x_101, x_71);
lean_dec(x_71);
if (x_102 == 0)
{
lean_object* x_103; 
if (x_66 == 0)
{
lean_ctor_set(x_65, 3, x_101);
lean_ctor_set(x_65, 2, x_100);
x_103 = x_65;
goto block_106;
}
else
{
lean_object* x_107; 
x_107 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_107, 0, x_61);
lean_ctor_set(x_107, 1, x_62);
lean_ctor_set(x_107, 2, x_100);
lean_ctor_set(x_107, 3, x_101);
x_103 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_13);
lean_ctor_set(x_104, 1, x_103);
x_4 = x_104;
goto _start;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_nat_sub(x_100, x_101);
lean_dec(x_101);
x_109 = l_String_Slice_pos_x21(x_2, x_108);
lean_dec(x_108);
x_110 = l_String_Slice_pos_x21(x_2, x_100);
x_111 = lean_unsigned_to_nat(0u);
if (x_66 == 0)
{
lean_ctor_set(x_65, 3, x_111);
lean_ctor_set(x_65, 2, x_100);
x_112 = x_65;
goto block_113;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_114, 0, x_61);
lean_ctor_set(x_114, 1, x_62);
lean_ctor_set(x_114, 2, x_100);
lean_ctor_set(x_114, 3, x_111);
x_112 = x_114;
goto block_113;
}
block_113:
{
x_23 = x_112;
x_24 = x_109;
x_25 = x_110;
goto block_36;
}
}
}
}
}
}
default: 
{
lean_del_object(x_15);
goto block_38;
}
}
block_22:
{
lean_object* x_18; 
if (x_16 == 0)
{
lean_ctor_set(x_15, 1, x_17);
x_18 = x_15;
goto block_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_17);
x_18 = x_21;
goto block_20;
}
block_20:
{
x_4 = x_18;
goto _start;
}
}
block_36:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_35; 
x_26 = l_String_Slice_subslice_x21(x_2, x_13, x_24);
x_27 = lean_ctor_get(x_26, 0);
x_28 = lean_ctor_get(x_26, 1);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
x_29 = x_26;
x_30 = x_35;
goto block_34;
}
else
{
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_31; 
if (x_30 == 0)
{
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 0, x_25);
x_31 = x_29;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_23);
x_31 = x_33;
goto block_32;
}
block_32:
{
x_6 = x_31;
x_7 = x_27;
x_8 = x_28;
goto block_12;
}
}
}
block_38:
{
lean_object* x_37; 
x_37 = lean_box(1);
lean_inc(x_3);
x_6 = x_37;
x_7 = x_13;
x_8 = x_3;
goto block_12;
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_5;
}
block_12:
{
lean_object* x_9; lean_object* x_10; 
lean_inc_ref(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_array_push(x_5, x_9);
x_4 = x_6;
x_5 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2, &l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__2);
x_2 = lean_unsigned_to_nat(0u);
x_3 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1));
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__0));
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_String_Slice_Pos_prevn(x_7, x_6, x_4);
lean_dec_ref(x_7);
lean_inc(x_8);
lean_inc_ref(x_1);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_9, 2, x_6);
x_10 = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3, &l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3_once, _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__3);
x_11 = l_String_Slice_beq(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_8);
lean_inc_ref(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_8);
x_14 = l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0(x_13);
x_15 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__4));
x_16 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(x_1, x_13, x_8, x_14, x_15);
lean_dec_ref(x_13);
x_17 = lean_array_to_list(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_dec_ref(x_17);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_35; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec_ref(x_17);
x_22 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3, &l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__0___closed__3);
x_26 = l_String_Slice_intercalate(x_25, x_19);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_19, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_19, 0);
lean_dec(x_37);
x_27 = x_19;
x_28 = x_35;
goto block_34;
}
else
{
lean_dec(x_19);
x_27 = lean_box(0);
x_28 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_string_utf8_extract(x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 0, x_29);
x_30 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_26);
x_30 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
}
else
{
lean_object* x_38; 
lean_dec_ref(x_1);
x_38 = lean_box(0);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Json_parse(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec_ref(x_2);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__0));
lean_inc(x_4);
x_6 = l_Lean_Json_getObjVal_x3f(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_dec_ref(x_6);
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_6);
x_8 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___closed__1));
x_9 = l_Lean_Json_getObjVal_x3f(x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec_ref(x_9);
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
lean_dec_ref(x_9);
x_11 = 1;
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__1));
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__3));
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_3);
x_4 = lean_apply_1(x_3, lean_box(0));
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_49; 
x_5 = lean_ctor_get(x_4, 0);
x_49 = !lean_is_exclusive(x_4);
if (x_49 == 0)
{
x_6 = x_4;
x_7 = x_49;
goto block_48;
}
else
{
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_utf8_byte_size(x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField___closed__1));
x_12 = lean_string_dec_eq(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_5);
x_13 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_parseHeaderField(x_5);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec_ref(x_1);
lean_inc(x_5);
x_14 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_isLean3Request(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__0));
x_16 = l_String_quote(x_5);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Std_Format_defWidth;
x_19 = l_Std_Format_pretty(x_17, x_18, x_9, x_9);
x_20 = lean_string_append(x_15, x_19);
lean_dec_ref(x_19);
x_21 = lean_mk_io_user_error(x_20);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_21);
x_22 = x_6;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
x_25 = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2, &l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2_once, _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__2);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_25);
x_26 = x_6;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_del_object(x_6);
lean_dec(x_5);
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
lean_dec_ref(x_13);
x_30 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_39; 
x_31 = lean_ctor_get(x_30, 0);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
x_32 = x_30;
x_33 = x_39;
goto block_38;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_31);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_34);
x_35 = x_32;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
lean_dec(x_29);
return x_30;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_40 = lean_box(0);
if (x_7 == 0)
{
lean_ctor_set(x_6, 0, x_40);
x_41 = x_6;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_5);
lean_dec_ref(x_1);
x_44 = lean_obj_once(&l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4, &l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4_once, _init_l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___closed__4);
if (x_7 == 0)
{
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_44);
x_45 = x_6;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_4, 0);
x_57 = !lean_is_exclusive(x_4);
if (x_57 == 0)
{
x_51 = x_4;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_4);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
x_8 = lean_string_append(x_1, x_7);
x_9 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
x_10 = lean_string_append(x_9, x_5);
x_11 = lean_string_append(x_10, x_7);
x_12 = lean_string_append(x_11, x_6);
x_13 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_8, x_14);
lean_dec_ref(x_14);
x_1 = x_15;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__0));
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1));
x_8 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
x_9 = lean_string_append(x_8, x_5);
x_10 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_6);
x_13 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_7, x_14);
lean_dec_ref(x_14);
x_16 = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__2));
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_18, 0);
x_20 = lean_ctor_get(x_18, 1);
x_21 = ((lean_object*)(l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___closed__1));
x_22 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__1));
x_23 = lean_string_append(x_22, x_19);
x_24 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__0));
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_string_append(x_25, x_20);
x_27 = ((lean_object*)(l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1___closed__2));
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_21, x_28);
lean_dec_ref(x_28);
x_30 = l_List_foldl___at___00List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1_spec__1(x_29, x_3);
x_31 = 93;
x_32 = lean_string_push(x_30, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_string_dec_eq(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readHeaderFields(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_34; 
x_4 = lean_ctor_get(x_3, 0);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
x_5 = x_3;
x_6 = x_34;
goto block_33;
}
else
{
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_7; lean_object* x_8; 
x_7 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__0));
x_8 = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_7, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__1));
x_10 = l_List_toString___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__1(x_4);
lean_dec(x_4);
x_11 = lean_string_append(x_9, x_10);
lean_dec_ref(x_10);
x_12 = lean_mk_io_user_error(x_11);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_12);
x_13 = x_5;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec_ref(x_8);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_string_utf8_byte_size(x_16);
lean_inc(x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_String_Slice_toNat_x3f(x_19);
lean_dec_ref(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__2));
x_22 = lean_string_append(x_21, x_16);
lean_dec(x_16);
x_23 = ((lean_object*)(l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___closed__3));
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_mk_io_user_error(x_24);
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_25);
x_26 = x_5;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_16);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec_ref(x_20);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_29);
x_30 = x_5;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
x_35 = lean_ctor_get(x_3, 0);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
x_36 = x_3;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_3);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at___00__private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_10; 
lean_inc_ref(x_1);
x_10 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_IO_FS_Stream_readMessage(x_1, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_3 = x_13;
goto block_9;
}
}
else
{
lean_object* x_14; 
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec_ref(x_10);
x_3 = x_14;
goto block_9;
}
block_9:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_IO_FS_Stream_readLspMessage___closed__0));
x_5 = lean_io_error_to_string(x_3);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = lean_mk_io_user_error(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessage___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_readLspMessage(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_10; 
lean_inc_ref(x_1);
x_10 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_IO_FS_Stream_readUTF8(x_1, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_3 = x_13;
goto block_9;
}
}
else
{
lean_object* x_14; 
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec_ref(x_10);
x_3 = x_14;
goto block_9;
}
block_9:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(l_IO_FS_Stream_readLspMessage___closed__0));
x_5 = lean_io_error_to_string(x_3);
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = lean_mk_io_user_error(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspMessageAsString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_Stream_readLspMessageAsString(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_12; 
lean_inc_ref(x_1);
x_12 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_IO_FS_Stream_readRequestAs___redArg(x_1, x_13, x_2, x_3);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_5 = x_15;
goto block_11;
}
}
else
{
lean_object* x_16; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec_ref(x_12);
x_5 = x_16;
goto block_11;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = ((lean_object*)(l_IO_FS_Stream_readLspRequestAs___redArg___closed__0));
x_7 = lean_io_error_to_string(x_5);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = lean_mk_io_user_error(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readLspRequestAs___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspRequestAs___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspRequestAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspRequestAs(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_12; 
lean_inc_ref(x_1);
x_12 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_IO_FS_Stream_readNotificationAs___redArg(x_1, x_13, x_2, x_3);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_5 = x_15;
goto block_11;
}
}
else
{
lean_object* x_16; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec_ref(x_12);
x_5 = x_16;
goto block_11;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = ((lean_object*)(l_IO_FS_Stream_readLspNotificationAs___redArg___closed__0));
x_7 = lean_io_error_to_string(x_5);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = lean_mk_io_user_error(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readLspNotificationAs___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspNotificationAs___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspNotificationAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspNotificationAs(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_12; 
lean_inc_ref(x_1);
x_12 = l___private_Lean_Data_Lsp_Communication_0__IO_FS_Stream_readLspHeader(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_IO_FS_Stream_readResponseAs___redArg(x_1, x_13, x_2, x_3);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_5 = x_15;
goto block_11;
}
}
else
{
lean_object* x_16; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec_ref(x_12);
x_5 = x_16;
goto block_11;
}
block_11:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = ((lean_object*)(l_IO_FS_Stream_readLspResponseAs___redArg___closed__0));
x_7 = lean_io_error_to_string(x_5);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = lean_mk_io_user_error(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_readLspResponseAs___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspResponseAs___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_readLspResponseAs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_readLspResponseAs(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = ((lean_object*)(l_IO_FS_Stream_writeSerializedLspMessage___closed__0));
x_7 = lean_string_utf8_byte_size(x_2);
x_8 = l_Nat_reprFast(x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = ((lean_object*)(l_IO_FS_Stream_writeSerializedLspMessage___closed__1));
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = lean_apply_2(x_5, x_12, lean_box(0));
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec_ref(x_13);
x_14 = lean_apply_1(x_4, lean_box(0));
return x_14;
}
else
{
lean_dec_ref(x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeSerializedLspMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeSerializedLspMessage(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_Lean_Json_Structured_toJson(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec_ref(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32700u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__12, &l_IO_FS_Stream_writeLspMessage___closed__12_once, _init_l_IO_FS_Stream_writeLspMessage___closed__12);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__13, &l_IO_FS_Stream_writeLspMessage___closed__13_once, _init_l_IO_FS_Stream_writeLspMessage___closed__13);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__14, &l_IO_FS_Stream_writeLspMessage___closed__14_once, _init_l_IO_FS_Stream_writeLspMessage___closed__14);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32600u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__16, &l_IO_FS_Stream_writeLspMessage___closed__16_once, _init_l_IO_FS_Stream_writeLspMessage___closed__16);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__17, &l_IO_FS_Stream_writeLspMessage___closed__17_once, _init_l_IO_FS_Stream_writeLspMessage___closed__17);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__18, &l_IO_FS_Stream_writeLspMessage___closed__18_once, _init_l_IO_FS_Stream_writeLspMessage___closed__18);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32601u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__20, &l_IO_FS_Stream_writeLspMessage___closed__20_once, _init_l_IO_FS_Stream_writeLspMessage___closed__20);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__21, &l_IO_FS_Stream_writeLspMessage___closed__21_once, _init_l_IO_FS_Stream_writeLspMessage___closed__21);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__23(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__22, &l_IO_FS_Stream_writeLspMessage___closed__22_once, _init_l_IO_FS_Stream_writeLspMessage___closed__22);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32602u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__25(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__24, &l_IO_FS_Stream_writeLspMessage___closed__24_once, _init_l_IO_FS_Stream_writeLspMessage___closed__24);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__26(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__25, &l_IO_FS_Stream_writeLspMessage___closed__25_once, _init_l_IO_FS_Stream_writeLspMessage___closed__25);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__27(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__26, &l_IO_FS_Stream_writeLspMessage___closed__26_once, _init_l_IO_FS_Stream_writeLspMessage___closed__26);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__28(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32603u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__29(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__28, &l_IO_FS_Stream_writeLspMessage___closed__28_once, _init_l_IO_FS_Stream_writeLspMessage___closed__28);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__30(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__29, &l_IO_FS_Stream_writeLspMessage___closed__29_once, _init_l_IO_FS_Stream_writeLspMessage___closed__29);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__31(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__30, &l_IO_FS_Stream_writeLspMessage___closed__30_once, _init_l_IO_FS_Stream_writeLspMessage___closed__30);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__32(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32002u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__33(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__32, &l_IO_FS_Stream_writeLspMessage___closed__32_once, _init_l_IO_FS_Stream_writeLspMessage___closed__32);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__34(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__33, &l_IO_FS_Stream_writeLspMessage___closed__33_once, _init_l_IO_FS_Stream_writeLspMessage___closed__33);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__35(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__34, &l_IO_FS_Stream_writeLspMessage___closed__34_once, _init_l_IO_FS_Stream_writeLspMessage___closed__34);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__36(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32001u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__37(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__36, &l_IO_FS_Stream_writeLspMessage___closed__36_once, _init_l_IO_FS_Stream_writeLspMessage___closed__36);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__38(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__37, &l_IO_FS_Stream_writeLspMessage___closed__37_once, _init_l_IO_FS_Stream_writeLspMessage___closed__37);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__39(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__38, &l_IO_FS_Stream_writeLspMessage___closed__38_once, _init_l_IO_FS_Stream_writeLspMessage___closed__38);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__40(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32801u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__41(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__40, &l_IO_FS_Stream_writeLspMessage___closed__40_once, _init_l_IO_FS_Stream_writeLspMessage___closed__40);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__42(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__41, &l_IO_FS_Stream_writeLspMessage___closed__41_once, _init_l_IO_FS_Stream_writeLspMessage___closed__41);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__43(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__42, &l_IO_FS_Stream_writeLspMessage___closed__42_once, _init_l_IO_FS_Stream_writeLspMessage___closed__42);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__44(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32800u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__45(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__44, &l_IO_FS_Stream_writeLspMessage___closed__44_once, _init_l_IO_FS_Stream_writeLspMessage___closed__44);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__46(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__45, &l_IO_FS_Stream_writeLspMessage___closed__45_once, _init_l_IO_FS_Stream_writeLspMessage___closed__45);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__47(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__46, &l_IO_FS_Stream_writeLspMessage___closed__46_once, _init_l_IO_FS_Stream_writeLspMessage___closed__46);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__48(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32900u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__49(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__48, &l_IO_FS_Stream_writeLspMessage___closed__48_once, _init_l_IO_FS_Stream_writeLspMessage___closed__48);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__50(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__49, &l_IO_FS_Stream_writeLspMessage___closed__49_once, _init_l_IO_FS_Stream_writeLspMessage___closed__49);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__51(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__50, &l_IO_FS_Stream_writeLspMessage___closed__50_once, _init_l_IO_FS_Stream_writeLspMessage___closed__50);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__52(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32901u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__53(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__52, &l_IO_FS_Stream_writeLspMessage___closed__52_once, _init_l_IO_FS_Stream_writeLspMessage___closed__52);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__54(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__53, &l_IO_FS_Stream_writeLspMessage___closed__53_once, _init_l_IO_FS_Stream_writeLspMessage___closed__53);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__55(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__54, &l_IO_FS_Stream_writeLspMessage___closed__54_once, _init_l_IO_FS_Stream_writeLspMessage___closed__54);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__56(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32902u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__57(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__56, &l_IO_FS_Stream_writeLspMessage___closed__56_once, _init_l_IO_FS_Stream_writeLspMessage___closed__56);
x_2 = lean_int_neg(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__58(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__57, &l_IO_FS_Stream_writeLspMessage___closed__57_once, _init_l_IO_FS_Stream_writeLspMessage___closed__57);
x_2 = l_Lean_JsonNumber_fromInt(x_1);
return x_2;
}
}
static lean_object* _init_l_IO_FS_Stream_writeLspMessage___closed__59(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__58, &l_IO_FS_Stream_writeLspMessage___closed__58_once, _init_l_IO_FS_Stream_writeLspMessage___closed__58);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__3));
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__4));
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
x_27 = lean_ctor_get(x_11, 0);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
x_28 = x_11;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 3);
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
x_15 = x_30;
goto block_26;
}
}
}
case 1:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
x_35 = lean_ctor_get(x_11, 0);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
x_36 = x_11;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
lean_ctor_set_tag(x_36, 2);
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
x_15 = x_38;
goto block_26;
}
}
}
default: 
{
lean_object* x_43; 
x_43 = lean_box(0);
x_15 = x_43;
goto block_26;
}
}
block_26:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__5));
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__6));
x_24 = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(x_23, x_13);
x_25 = l_List_appendTR___redArg(x_22, x_24);
x_5 = x_25;
goto block_10;
}
}
case 1:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_57; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_57 = !lean_is_exclusive(x_2);
if (x_57 == 0)
{
x_46 = x_2;
x_47 = x_57;
goto block_56;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_2);
x_46 = lean_box(0);
x_47 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__5));
x_49 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_49, 0, x_44);
if (x_47 == 0)
{
lean_ctor_set_tag(x_46, 0);
lean_ctor_set(x_46, 1, x_49);
lean_ctor_set(x_46, 0, x_48);
x_50 = x_46;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_49);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__6));
x_52 = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__0(x_51, x_45);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_5 = x_53;
goto block_10;
}
}
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_91; 
x_58 = lean_ctor_get(x_2, 0);
x_59 = lean_ctor_get(x_2, 1);
x_91 = !lean_is_exclusive(x_2);
if (x_91 == 0)
{
x_60 = x_2;
x_61 = x_91;
goto block_90;
}
else
{
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_2);
x_60 = lean_box(0);
x_61 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_62; lean_object* x_63; 
x_62 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__4));
switch (lean_obj_tag(x_58)) {
case 0:
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
x_73 = lean_ctor_get(x_58, 0);
x_80 = !lean_is_exclusive(x_58);
if (x_80 == 0)
{
x_74 = x_58;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_58);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
lean_ctor_set_tag(x_74, 3);
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
x_63 = x_76;
goto block_72;
}
}
}
case 1:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
x_81 = lean_ctor_get(x_58, 0);
x_88 = !lean_is_exclusive(x_58);
if (x_88 == 0)
{
x_82 = x_58;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_58);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
lean_ctor_set_tag(x_82, 2);
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
x_63 = x_84;
goto block_72;
}
}
}
default: 
{
lean_object* x_89; 
x_89 = lean_box(0);
x_63 = x_89;
goto block_72;
}
}
block_72:
{
lean_object* x_64; 
if (x_61 == 0)
{
lean_ctor_set_tag(x_60, 0);
lean_ctor_set(x_60, 1, x_63);
lean_ctor_set(x_60, 0, x_62);
x_64 = x_60;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_63);
x_64 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__7));
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_59);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_68);
x_5 = x_69;
goto block_10;
}
}
}
}
default: 
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_115; lean_object* x_116; 
x_92 = lean_ctor_get(x_2, 0);
lean_inc(x_92);
x_93 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_94 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_2, 2);
lean_inc(x_95);
lean_dec_ref(x_2);
x_115 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__4));
switch (lean_obj_tag(x_92)) {
case 0:
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_140; 
x_133 = lean_ctor_get(x_92, 0);
x_140 = !lean_is_exclusive(x_92);
if (x_140 == 0)
{
x_134 = x_92;
x_135 = x_140;
goto block_139;
}
else
{
lean_inc(x_133);
lean_dec(x_92);
x_134 = lean_box(0);
x_135 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_136; 
if (x_135 == 0)
{
lean_ctor_set_tag(x_134, 3);
x_136 = x_134;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_138, 0, x_133);
x_136 = x_138;
goto block_137;
}
block_137:
{
x_116 = x_136;
goto block_132;
}
}
}
case 1:
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_148; 
x_141 = lean_ctor_get(x_92, 0);
x_148 = !lean_is_exclusive(x_92);
if (x_148 == 0)
{
x_142 = x_92;
x_143 = x_148;
goto block_147;
}
else
{
lean_inc(x_141);
lean_dec(x_92);
x_142 = lean_box(0);
x_143 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_144; 
if (x_143 == 0)
{
lean_ctor_set_tag(x_142, 2);
x_144 = x_142;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_146, 0, x_141);
x_144 = x_146;
goto block_145;
}
block_145:
{
x_116 = x_144;
goto block_132;
}
}
}
default: 
{
lean_object* x_149; 
x_149 = lean_box(0);
x_116 = x_149;
goto block_132;
}
}
block_114:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_96);
lean_ctor_set(x_100, 1, x_99);
x_101 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__8));
x_102 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_102, 0, x_94);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_105);
x_107 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__9));
x_108 = l_Lean_Json_opt___at___00IO_FS_Stream_writeLspMessage_spec__1(x_107, x_95);
lean_dec(x_95);
x_109 = l_List_appendTR___redArg(x_106, x_108);
x_110 = l_Lean_Json_mkObj(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_97);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_98);
lean_ctor_set(x_113, 1, x_112);
x_5 = x_113;
goto block_10;
}
block_132:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__10));
x_119 = ((lean_object*)(l_IO_FS_Stream_writeLspMessage___closed__11));
switch (x_93) {
case 0:
{
lean_object* x_120; 
x_120 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__15, &l_IO_FS_Stream_writeLspMessage___closed__15_once, _init_l_IO_FS_Stream_writeLspMessage___closed__15);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_120;
goto block_114;
}
case 1:
{
lean_object* x_121; 
x_121 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__19, &l_IO_FS_Stream_writeLspMessage___closed__19_once, _init_l_IO_FS_Stream_writeLspMessage___closed__19);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_121;
goto block_114;
}
case 2:
{
lean_object* x_122; 
x_122 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__23, &l_IO_FS_Stream_writeLspMessage___closed__23_once, _init_l_IO_FS_Stream_writeLspMessage___closed__23);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_122;
goto block_114;
}
case 3:
{
lean_object* x_123; 
x_123 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__27, &l_IO_FS_Stream_writeLspMessage___closed__27_once, _init_l_IO_FS_Stream_writeLspMessage___closed__27);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_123;
goto block_114;
}
case 4:
{
lean_object* x_124; 
x_124 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__31, &l_IO_FS_Stream_writeLspMessage___closed__31_once, _init_l_IO_FS_Stream_writeLspMessage___closed__31);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_124;
goto block_114;
}
case 5:
{
lean_object* x_125; 
x_125 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__35, &l_IO_FS_Stream_writeLspMessage___closed__35_once, _init_l_IO_FS_Stream_writeLspMessage___closed__35);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_125;
goto block_114;
}
case 6:
{
lean_object* x_126; 
x_126 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__39, &l_IO_FS_Stream_writeLspMessage___closed__39_once, _init_l_IO_FS_Stream_writeLspMessage___closed__39);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_126;
goto block_114;
}
case 7:
{
lean_object* x_127; 
x_127 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__43, &l_IO_FS_Stream_writeLspMessage___closed__43_once, _init_l_IO_FS_Stream_writeLspMessage___closed__43);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_127;
goto block_114;
}
case 8:
{
lean_object* x_128; 
x_128 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__47, &l_IO_FS_Stream_writeLspMessage___closed__47_once, _init_l_IO_FS_Stream_writeLspMessage___closed__47);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_128;
goto block_114;
}
case 9:
{
lean_object* x_129; 
x_129 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__51, &l_IO_FS_Stream_writeLspMessage___closed__51_once, _init_l_IO_FS_Stream_writeLspMessage___closed__51);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_129;
goto block_114;
}
case 10:
{
lean_object* x_130; 
x_130 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__55, &l_IO_FS_Stream_writeLspMessage___closed__55_once, _init_l_IO_FS_Stream_writeLspMessage___closed__55);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_130;
goto block_114;
}
default: 
{
lean_object* x_131; 
x_131 = lean_obj_once(&l_IO_FS_Stream_writeLspMessage___closed__59, &l_IO_FS_Stream_writeLspMessage___closed__59_once, _init_l_IO_FS_Stream_writeLspMessage___closed__59);
x_96 = x_119;
x_97 = x_118;
x_98 = x_117;
x_99 = x_131;
goto block_114;
}
}
}
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_Json_mkObj(x_6);
x_8 = l_Lean_Json_compress(x_7);
x_9 = l_IO_FS_Stream_writeSerializedLspMessage(x_1, x_8);
lean_dec_ref(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspMessage___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspMessage(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_27; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
x_8 = x_3;
x_9 = x_27;
goto block_26;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_10; lean_object* x_16; 
x_16 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
x_17 = lean_box(0);
x_10 = x_17;
goto block_15;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
x_18 = lean_ctor_get(x_16, 0);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
x_19 = x_16;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
x_10 = x_21;
goto block_15;
}
}
}
block_15:
{
lean_object* x_11; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 2, x_10);
x_11 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_10);
x_11 = x_14;
goto block_13;
}
block_13:
{
lean_object* x_12; 
x_12 = l_IO_FS_Stream_writeLspMessage(x_2, x_11);
return x_12;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeLspRequest___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspRequest___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspRequest___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspRequest(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_26; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
x_7 = x_3;
x_8 = x_26;
goto block_25;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_9; lean_object* x_15; 
x_15 = l_Lean_Json_toStructured_x3f___redArg(x_1, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_15);
x_16 = lean_box(0);
x_9 = x_16;
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
x_18 = x_15;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
x_9 = x_20;
goto block_14;
}
}
}
block_14:
{
lean_object* x_10; 
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_9);
x_10 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_9);
x_10 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_11; 
x_11 = l_IO_FS_Stream_writeLspMessage(x_2, x_10);
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeLspNotification___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspNotification___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspNotification___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspNotification(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_15; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
x_7 = x_3;
x_8 = x_15;
goto block_14;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_apply_1(x_1, x_6);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 2);
lean_ctor_set(x_7, 1, x_9);
x_10 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_9);
x_10 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_11; 
x_11 = l_IO_FS_Stream_writeLspMessage(x_2, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeLspResponse___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponse___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponse(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_15; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 1);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_2, 2);
lean_dec(x_16);
x_7 = x_2;
x_8 = x_15;
goto block_14;
}
else
{
lean_inc(x_6);
lean_inc(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 2, x_9);
x_10 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_6);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_5);
x_10 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_11; 
x_11 = l_IO_FS_Stream_writeLspMessage(x_1, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_Stream_writeLspResponseError(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_28; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
x_9 = x_3;
x_10 = x_28;
goto block_27;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_11; 
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_1);
x_17 = lean_box(0);
x_11 = x_17;
goto block_16;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_26; 
x_18 = lean_ctor_get(x_8, 0);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
x_19 = x_8;
x_20 = x_26;
goto block_25;
}
else
{
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_box(0);
x_20 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_apply_1(x_1, x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
x_11 = x_22;
goto block_16;
}
}
}
block_16:
{
lean_object* x_12; 
if (x_10 == 0)
{
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 2, x_11);
x_12 = x_9;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_6);
x_12 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_13; 
x_13 = l_IO_FS_Stream_writeLspMessage(x_2, x_12);
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponseErrorWithData___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IO_FS_Stream_writeLspResponseErrorWithData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_IO_FS_Stream_writeLspResponseErrorWithData(x_1, x_2, x_3, x_4);
return x_6;
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
res = runtime_initialize_Lean_Data_JsonRpc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin)
;
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
res = initialize_Lean_Data_JsonRpc(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Communication(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Communication(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Communication(builtin);
}
#ifdef __cplusplus
}
#endif

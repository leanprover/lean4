// Lean compiler output
// Module: Lean.Server.Completion.CompletionItemCompression
// Imports: public import Lean.Data.Lsp.LanguageFeatures import Init.Omega
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
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object*, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* l_Lean_Lsp_CompletionItemKind_ctorIdx(uint8_t);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\"c"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\"f"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "{\"kind\":\""};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\",\"value\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "plaintext"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "markdown"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "{\"character\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ",\"line\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "{\"end\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ",\"start\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "{\"insert\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ",\"newText\":\""};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ",\"replace\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ",\"tags\":["};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ",\"data\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ",\"sortText\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = ",\"textEdit\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ",\"kind\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = ",\"documentation\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ",\"detail\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6_value;
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "{\"label\":"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "{\"isIncomplete\":"};
static const lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0 = (const lean_object*)&l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0_value;
static const lean_string_object l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ",\"items\":["};
static const lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1 = (const lean_object*)&l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1_value;
static const lean_string_object l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]}"};
static const lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2 = (const lean_object*)&l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2_value;
static const lean_string_object l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3 = (const lean_object*)&l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3_value;
static const lean_string_object l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4 = (const lean_object*)&l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v_it_3_, lean_object* v_acc_4_, lean_object* v_hP_5_, lean_object* v_recur_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_nat_dec_eq(v_it_3_, v___x_1_);
if (v___x_7_ == 0)
{
uint32_t v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_8_ = lean_string_utf8_get_fast(v___x_2_, v_it_3_);
v___x_9_ = lean_string_utf8_next_fast(v___x_2_, v_it_3_);
v___x_10_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_4_, v___x_8_);
v___x_11_ = lean_apply_4(v_recur_6_, v___x_9_, v___x_10_, lean_box(0), lean_box(0));
return v___x_11_;
}
else
{
lean_dec_ref(v_recur_6_);
return v_acc_4_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed(lean_object* v___x_12_, lean_object* v___x_13_, lean_object* v_it_14_, lean_object* v_acc_15_, lean_object* v_hP_16_, lean_object* v_recur_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0(v___x_12_, v___x_13_, v_it_14_, v_acc_15_, v_hP_16_, v_recur_17_);
lean_dec(v_it_14_);
lean_dec_ref(v___x_13_);
lean_dec(v___x_12_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2(lean_object* v___x_19_, lean_object* v_uri_20_, lean_object* v_it_21_, lean_object* v_acc_22_, lean_object* v_hP_23_, lean_object* v_recur_24_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = lean_nat_dec_eq(v_it_21_, v___x_19_);
if (v___x_25_ == 0)
{
uint32_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_26_ = lean_string_utf8_get_fast(v_uri_20_, v_it_21_);
v___x_27_ = lean_string_utf8_next_fast(v_uri_20_, v_it_21_);
v___x_28_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_22_, v___x_26_);
v___x_29_ = lean_apply_4(v_recur_24_, v___x_27_, v___x_28_, lean_box(0), lean_box(0));
return v___x_29_;
}
else
{
lean_dec_ref(v_recur_24_);
return v_acc_22_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed(lean_object* v___x_30_, lean_object* v_uri_31_, lean_object* v_it_32_, lean_object* v_acc_33_, lean_object* v_hP_34_, lean_object* v_recur_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2(v___x_30_, v_uri_31_, v_it_32_, v_acc_33_, v_hP_34_, v_recur_35_);
lean_dec(v_it_32_);
lean_dec_ref(v_uri_31_);
lean_dec(v___x_30_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast(lean_object* v_acc_43_, lean_object* v_data_44_){
_start:
{
lean_object* v_acc_46_; lean_object* v___y_50_; lean_object* v___y_54_; lean_object* v_uri_57_; lean_object* v_pos_58_; lean_object* v_cPos_x3f_59_; lean_object* v_id_x3f_60_; lean_object* v___y_62_; lean_object* v_acc_63_; lean_object* v___y_93_; lean_object* v___x_107_; lean_object* v_acc_108_; lean_object* v___x_109_; lean_object* v_acc_110_; uint8_t v___x_111_; 
v_uri_57_ = lean_ctor_get(v_data_44_, 0);
lean_inc_ref(v_uri_57_);
v_pos_58_ = lean_ctor_get(v_data_44_, 1);
lean_inc_ref(v_pos_58_);
v_cPos_x3f_59_ = lean_ctor_get(v_data_44_, 2);
lean_inc(v_cPos_x3f_59_);
v_id_x3f_60_ = lean_ctor_get(v_data_44_, 3);
lean_inc(v_id_x3f_60_);
lean_dec_ref(v_data_44_);
v___x_107_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
v_acc_108_ = lean_string_append(v_acc_43_, v___x_107_);
v___x_109_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_110_ = lean_string_append(v_acc_108_, v___x_109_);
v___x_111_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_57_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_string_append(v_acc_110_, v_uri_57_);
lean_dec_ref(v_uri_57_);
v___x_113_ = lean_string_append(v___x_112_, v___x_109_);
v___y_93_ = v___x_113_;
goto v___jp_92_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_string_utf8_byte_size(v_uri_57_);
lean_inc_ref(v_uri_57_);
v___f_116_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed), 6, 2);
lean_closure_set(v___f_116_, 0, v___x_115_);
lean_closure_set(v___f_116_, 1, v_uri_57_);
v___x_117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_117_, 0, v_uri_57_);
lean_ctor_set(v___x_117_, 1, v___x_114_);
lean_ctor_set(v___x_117_, 2, v___x_115_);
v___x_118_ = l_String_Slice_positions(v___x_117_);
lean_dec_ref(v___x_117_);
v___x_119_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_116_, v___x_118_, v_acc_110_, lean_box(0));
v___x_120_ = lean_string_append(v___x_119_, v___x_109_);
v___y_93_ = v___x_120_;
goto v___jp_92_;
}
v___jp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v___x_48_ = lean_string_append(v_acc_46_, v___x_47_);
return v___x_48_;
}
v___jp_49_:
{
lean_object* v___x_51_; lean_object* v_acc_52_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_52_ = lean_string_append(v___y_50_, v___x_51_);
v_acc_46_ = v_acc_52_;
goto v___jp_45_;
}
v___jp_53_:
{
lean_object* v___x_55_; lean_object* v_acc_56_; 
v___x_55_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_56_ = lean_string_append(v___y_54_, v___x_55_);
v_acc_46_ = v_acc_56_;
goto v___jp_45_;
}
v___jp_61_:
{
if (lean_obj_tag(v_id_x3f_60_) == 1)
{
lean_object* v_val_64_; lean_object* v_acc_65_; 
v_val_64_ = lean_ctor_get(v_id_x3f_60_, 0);
lean_inc(v_val_64_);
lean_dec_ref(v_id_x3f_60_);
v_acc_65_ = lean_string_append(v_acc_63_, v___y_62_);
if (lean_obj_tag(v_val_64_) == 0)
{
lean_object* v_declName_66_; lean_object* v___x_67_; lean_object* v_acc_68_; uint8_t v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v_declName_66_ = lean_ctor_get(v_val_64_, 0);
lean_inc(v_declName_66_);
lean_dec_ref(v_val_64_);
v___x_67_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2));
v_acc_68_ = lean_string_append(v_acc_65_, v___x_67_);
v___x_69_ = 1;
v___x_70_ = l_Lean_Name_toString(v_declName_66_, v___x_69_);
v___x_71_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
v___x_72_ = lean_string_append(v_acc_68_, v___x_70_);
lean_dec_ref(v___x_70_);
v___y_50_ = v___x_72_;
goto v___jp_49_;
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___f_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_73_ = lean_unsigned_to_nat(0u);
v___x_74_ = lean_string_utf8_byte_size(v___x_70_);
lean_inc_ref(v___x_70_);
v___f_75_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_75_, 0, v___x_74_);
lean_closure_set(v___f_75_, 1, v___x_70_);
v___x_76_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_76_, 0, v___x_70_);
lean_ctor_set(v___x_76_, 1, v___x_73_);
lean_ctor_set(v___x_76_, 2, v___x_74_);
v___x_77_ = l_String_Slice_positions(v___x_76_);
lean_dec_ref(v___x_76_);
v___x_78_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_75_, v___x_77_, v_acc_68_, lean_box(0));
v___y_50_ = v___x_78_;
goto v___jp_49_;
}
}
else
{
lean_object* v_id_79_; lean_object* v___x_80_; lean_object* v_acc_81_; uint8_t v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_id_79_ = lean_ctor_get(v_val_64_, 0);
lean_inc(v_id_79_);
lean_dec_ref(v_val_64_);
v___x_80_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
v_acc_81_ = lean_string_append(v_acc_65_, v___x_80_);
v___x_82_ = 1;
v___x_83_ = l_Lean_Name_toString(v_id_79_, v___x_82_);
v___x_84_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; 
v___x_85_ = lean_string_append(v_acc_81_, v___x_83_);
lean_dec_ref(v___x_83_);
v___y_54_ = v___x_85_;
goto v___jp_53_;
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_string_utf8_byte_size(v___x_83_);
lean_inc_ref(v___x_83_);
v___f_88_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_88_, 0, v___x_87_);
lean_closure_set(v___f_88_, 1, v___x_83_);
v___x_89_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_89_, 0, v___x_83_);
lean_ctor_set(v___x_89_, 1, v___x_86_);
lean_ctor_set(v___x_89_, 2, v___x_87_);
v___x_90_ = l_String_Slice_positions(v___x_89_);
lean_dec_ref(v___x_89_);
v___x_91_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_88_, v___x_90_, v_acc_81_, lean_box(0));
v___y_54_ = v___x_91_;
goto v___jp_53_;
}
}
}
else
{
lean_dec(v_id_x3f_60_);
v_acc_46_ = v_acc_63_;
goto v___jp_45_;
}
}
v___jp_92_:
{
lean_object* v_line_94_; lean_object* v_character_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v_acc_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_acc_102_; 
v_line_94_ = lean_ctor_get(v_pos_58_, 0);
lean_inc(v_line_94_);
v_character_95_ = lean_ctor_get(v_pos_58_, 1);
lean_inc(v_character_95_);
lean_dec_ref(v_pos_58_);
v___x_96_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_97_ = lean_string_append(v___y_93_, v___x_96_);
v___x_98_ = l_Nat_reprFast(v_line_94_);
v_acc_99_ = lean_string_append(v___x_97_, v___x_98_);
lean_dec_ref(v___x_98_);
v___x_100_ = lean_string_append(v_acc_99_, v___x_96_);
v___x_101_ = l_Nat_reprFast(v_character_95_);
v_acc_102_ = lean_string_append(v___x_100_, v___x_101_);
lean_dec_ref(v___x_101_);
if (lean_obj_tag(v_cPos_x3f_59_) == 1)
{
lean_object* v_val_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v_acc_106_; 
v_val_103_ = lean_ctor_get(v_cPos_x3f_59_, 0);
lean_inc(v_val_103_);
lean_dec_ref(v_cPos_x3f_59_);
v___x_104_ = lean_string_append(v_acc_102_, v___x_96_);
v___x_105_ = l_Nat_reprFast(v_val_103_);
v_acc_106_ = lean_string_append(v___x_104_, v___x_105_);
lean_dec_ref(v___x_105_);
v___y_62_ = v___x_96_;
v_acc_63_ = v_acc_106_;
goto v___jp_61_;
}
else
{
lean_dec(v_cPos_x3f_59_);
v___y_62_ = v___x_96_;
v_acc_63_ = v_acc_102_;
goto v___jp_61_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0(lean_object* v___x_121_, lean_object* v_value_122_, lean_object* v_it_123_, lean_object* v_acc_124_, lean_object* v_hP_125_, lean_object* v_recur_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = lean_nat_dec_eq(v_it_123_, v___x_121_);
if (v___x_127_ == 0)
{
uint32_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = lean_string_utf8_get_fast(v_value_122_, v_it_123_);
v___x_129_ = lean_string_utf8_next_fast(v_value_122_, v_it_123_);
v___x_130_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_124_, v___x_128_);
v___x_131_ = lean_apply_4(v_recur_126_, v___x_129_, v___x_130_, lean_box(0), lean_box(0));
return v___x_131_;
}
else
{
lean_dec_ref(v_recur_126_);
return v_acc_124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed(lean_object* v___x_132_, lean_object* v_value_133_, lean_object* v_it_134_, lean_object* v_acc_135_, lean_object* v_hP_136_, lean_object* v_recur_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0(v___x_132_, v_value_133_, v_it_134_, v_acc_135_, v_hP_136_, v_recur_137_);
lean_dec(v_it_134_);
lean_dec_ref(v_value_133_);
lean_dec(v___x_132_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast(lean_object* v_acc_144_, lean_object* v_c_145_){
_start:
{
lean_object* v___y_147_; uint8_t v_kind_150_; lean_object* v_value_151_; lean_object* v___y_153_; 
v_kind_150_ = lean_ctor_get_uint8(v_c_145_, sizeof(void*)*1);
v_value_151_ = lean_ctor_get(v_c_145_, 0);
lean_inc_ref(v_value_151_);
lean_dec_ref(v_c_145_);
if (v_kind_150_ == 0)
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
v___y_153_ = v___x_171_;
goto v___jp_152_;
}
else
{
lean_object* v___x_172_; 
v___x_172_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
v___y_153_ = v___x_172_;
goto v___jp_152_;
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_149_ = lean_string_append(v___y_147_, v___x_148_);
return v___x_149_;
}
v___jp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_acc_158_; lean_object* v___x_159_; lean_object* v_acc_160_; uint8_t v___x_161_; 
v___x_154_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
v___x_155_ = lean_string_append(v_acc_144_, v___x_154_);
v___x_156_ = lean_string_append(v___x_155_, v___y_153_);
v___x_157_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
v_acc_158_ = lean_string_append(v___x_156_, v___x_157_);
v___x_159_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_160_ = lean_string_append(v_acc_158_, v___x_159_);
v___x_161_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_151_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_string_append(v_acc_160_, v_value_151_);
lean_dec_ref(v_value_151_);
v___x_163_ = lean_string_append(v___x_162_, v___x_159_);
v___y_147_ = v___x_163_;
goto v___jp_146_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_string_utf8_byte_size(v_value_151_);
lean_inc_ref(v_value_151_);
v___f_166_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_166_, 0, v___x_165_);
lean_closure_set(v___f_166_, 1, v_value_151_);
v___x_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_167_, 0, v_value_151_);
lean_ctor_set(v___x_167_, 1, v___x_164_);
lean_ctor_set(v___x_167_, 2, v___x_165_);
v___x_168_ = l_String_Slice_positions(v___x_167_);
lean_dec_ref(v___x_167_);
v___x_169_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_166_, v___x_168_, v_acc_160_, lean_box(0));
v___x_170_ = lean_string_append(v___x_169_, v___x_159_);
v___y_147_ = v___x_170_;
goto v___jp_146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast(lean_object* v_acc_175_, lean_object* v_p_176_){
_start:
{
lean_object* v_line_177_; lean_object* v_character_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_line_177_ = lean_ctor_get(v_p_176_, 0);
lean_inc(v_line_177_);
v_character_178_ = lean_ctor_get(v_p_176_, 1);
lean_inc(v_character_178_);
lean_dec_ref(v_p_176_);
v___x_179_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_180_ = lean_string_append(v_acc_175_, v___x_179_);
v___x_181_ = l_Nat_reprFast(v_character_178_);
v___x_182_ = lean_string_append(v___x_180_, v___x_181_);
lean_dec_ref(v___x_181_);
v___x_183_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_184_ = lean_string_append(v___x_182_, v___x_183_);
v___x_185_ = l_Nat_reprFast(v_line_177_);
v___x_186_ = lean_string_append(v___x_184_, v___x_185_);
lean_dec_ref(v___x_185_);
v___x_187_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_188_ = lean_string_append(v___x_186_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast(lean_object* v_acc_191_, lean_object* v_range_192_){
_start:
{
lean_object* v_end_193_; lean_object* v_start_194_; lean_object* v_line_195_; lean_object* v_character_196_; lean_object* v_line_197_; lean_object* v_character_198_; lean_object* v___x_199_; lean_object* v_acc_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v_acc_210_; lean_object* v___x_211_; lean_object* v_acc_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_acc_219_; lean_object* v___x_220_; 
v_end_193_ = lean_ctor_get(v_range_192_, 1);
lean_inc_ref(v_end_193_);
v_start_194_ = lean_ctor_get(v_range_192_, 0);
lean_inc_ref(v_start_194_);
lean_dec_ref(v_range_192_);
v_line_195_ = lean_ctor_get(v_end_193_, 0);
lean_inc(v_line_195_);
v_character_196_ = lean_ctor_get(v_end_193_, 1);
lean_inc(v_character_196_);
lean_dec_ref(v_end_193_);
v_line_197_ = lean_ctor_get(v_start_194_, 0);
lean_inc(v_line_197_);
v_character_198_ = lean_ctor_get(v_start_194_, 1);
lean_inc(v_character_198_);
lean_dec_ref(v_start_194_);
v___x_199_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
v_acc_200_ = lean_string_append(v_acc_191_, v___x_199_);
v___x_201_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_202_ = lean_string_append(v_acc_200_, v___x_201_);
v___x_203_ = l_Nat_reprFast(v_character_196_);
v___x_204_ = lean_string_append(v___x_202_, v___x_203_);
lean_dec_ref(v___x_203_);
v___x_205_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_206_ = lean_string_append(v___x_204_, v___x_205_);
v___x_207_ = l_Nat_reprFast(v_line_195_);
v___x_208_ = lean_string_append(v___x_206_, v___x_207_);
lean_dec_ref(v___x_207_);
v___x_209_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v_acc_210_ = lean_string_append(v___x_208_, v___x_209_);
v___x_211_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
v_acc_212_ = lean_string_append(v_acc_210_, v___x_211_);
v___x_213_ = lean_string_append(v_acc_212_, v___x_201_);
v___x_214_ = l_Nat_reprFast(v_character_198_);
v___x_215_ = lean_string_append(v___x_213_, v___x_214_);
lean_dec_ref(v___x_214_);
v___x_216_ = lean_string_append(v___x_215_, v___x_205_);
v___x_217_ = l_Nat_reprFast(v_line_197_);
v___x_218_ = lean_string_append(v___x_216_, v___x_217_);
lean_dec_ref(v___x_217_);
v_acc_219_ = lean_string_append(v___x_218_, v___x_209_);
v___x_220_ = lean_string_append(v_acc_219_, v___x_209_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast(lean_object* v_acc_224_, lean_object* v_edit_225_){
_start:
{
lean_object* v_insert_226_; lean_object* v_end_227_; lean_object* v_start_228_; lean_object* v_replace_229_; lean_object* v_end_230_; lean_object* v_start_231_; lean_object* v_newText_232_; lean_object* v_line_233_; lean_object* v_character_234_; lean_object* v_line_235_; lean_object* v_character_236_; lean_object* v_line_237_; lean_object* v_character_238_; lean_object* v_line_239_; lean_object* v_character_240_; lean_object* v___x_241_; lean_object* v_acc_242_; lean_object* v___x_243_; lean_object* v_acc_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v_acc_254_; lean_object* v___x_255_; lean_object* v_acc_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v_acc_263_; lean_object* v_acc_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v_acc_269_; lean_object* v___x_270_; lean_object* v_acc_271_; lean_object* v_acc_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_acc_279_; lean_object* v_acc_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_acc_287_; lean_object* v_acc_288_; lean_object* v___x_289_; 
v_insert_226_ = lean_ctor_get(v_edit_225_, 1);
v_end_227_ = lean_ctor_get(v_insert_226_, 1);
lean_inc_ref(v_end_227_);
v_start_228_ = lean_ctor_get(v_insert_226_, 0);
lean_inc_ref(v_start_228_);
v_replace_229_ = lean_ctor_get(v_edit_225_, 2);
v_end_230_ = lean_ctor_get(v_replace_229_, 1);
lean_inc_ref(v_end_230_);
v_start_231_ = lean_ctor_get(v_replace_229_, 0);
lean_inc_ref(v_start_231_);
v_newText_232_ = lean_ctor_get(v_edit_225_, 0);
lean_inc_ref(v_newText_232_);
lean_dec_ref(v_edit_225_);
v_line_233_ = lean_ctor_get(v_end_227_, 0);
lean_inc(v_line_233_);
v_character_234_ = lean_ctor_get(v_end_227_, 1);
lean_inc(v_character_234_);
lean_dec_ref(v_end_227_);
v_line_235_ = lean_ctor_get(v_start_228_, 0);
lean_inc(v_line_235_);
v_character_236_ = lean_ctor_get(v_start_228_, 1);
lean_inc(v_character_236_);
lean_dec_ref(v_start_228_);
v_line_237_ = lean_ctor_get(v_end_230_, 0);
lean_inc(v_line_237_);
v_character_238_ = lean_ctor_get(v_end_230_, 1);
lean_inc(v_character_238_);
lean_dec_ref(v_end_230_);
v_line_239_ = lean_ctor_get(v_start_231_, 0);
lean_inc(v_line_239_);
v_character_240_ = lean_ctor_get(v_start_231_, 1);
lean_inc(v_character_240_);
lean_dec_ref(v_start_231_);
v___x_241_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
v_acc_242_ = lean_string_append(v_acc_224_, v___x_241_);
v___x_243_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
v_acc_244_ = lean_string_append(v_acc_242_, v___x_243_);
v___x_245_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_246_ = lean_string_append(v_acc_244_, v___x_245_);
v___x_247_ = l_Nat_reprFast(v_character_234_);
v___x_248_ = lean_string_append(v___x_246_, v___x_247_);
lean_dec_ref(v___x_247_);
v___x_249_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_250_ = lean_string_append(v___x_248_, v___x_249_);
v___x_251_ = l_Nat_reprFast(v_line_233_);
v___x_252_ = lean_string_append(v___x_250_, v___x_251_);
lean_dec_ref(v___x_251_);
v___x_253_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v_acc_254_ = lean_string_append(v___x_252_, v___x_253_);
v___x_255_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
v_acc_256_ = lean_string_append(v_acc_254_, v___x_255_);
v___x_257_ = lean_string_append(v_acc_256_, v___x_245_);
v___x_258_ = l_Nat_reprFast(v_character_236_);
v___x_259_ = lean_string_append(v___x_257_, v___x_258_);
lean_dec_ref(v___x_258_);
v___x_260_ = lean_string_append(v___x_259_, v___x_249_);
v___x_261_ = l_Nat_reprFast(v_line_235_);
v___x_262_ = lean_string_append(v___x_260_, v___x_261_);
lean_dec_ref(v___x_261_);
v_acc_263_ = lean_string_append(v___x_262_, v___x_253_);
v_acc_264_ = lean_string_append(v_acc_263_, v___x_253_);
v___x_265_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
v___x_266_ = lean_string_append(v_acc_264_, v___x_265_);
v___x_267_ = lean_string_append(v___x_266_, v_newText_232_);
lean_dec_ref(v_newText_232_);
v___x_268_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_269_ = lean_string_append(v___x_267_, v___x_268_);
v___x_270_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
v_acc_271_ = lean_string_append(v_acc_269_, v___x_270_);
v_acc_272_ = lean_string_append(v_acc_271_, v___x_243_);
v___x_273_ = lean_string_append(v_acc_272_, v___x_245_);
v___x_274_ = l_Nat_reprFast(v_character_238_);
v___x_275_ = lean_string_append(v___x_273_, v___x_274_);
lean_dec_ref(v___x_274_);
v___x_276_ = lean_string_append(v___x_275_, v___x_249_);
v___x_277_ = l_Nat_reprFast(v_line_237_);
v___x_278_ = lean_string_append(v___x_276_, v___x_277_);
lean_dec_ref(v___x_277_);
v_acc_279_ = lean_string_append(v___x_278_, v___x_253_);
v_acc_280_ = lean_string_append(v_acc_279_, v___x_255_);
v___x_281_ = lean_string_append(v_acc_280_, v___x_245_);
v___x_282_ = l_Nat_reprFast(v_character_240_);
v___x_283_ = lean_string_append(v___x_281_, v___x_282_);
lean_dec_ref(v___x_282_);
v___x_284_ = lean_string_append(v___x_283_, v___x_249_);
v___x_285_ = l_Nat_reprFast(v_line_239_);
v___x_286_ = lean_string_append(v___x_284_, v___x_285_);
lean_dec_ref(v___x_285_);
v_acc_287_ = lean_string_append(v___x_286_, v___x_253_);
v_acc_288_ = lean_string_append(v_acc_287_, v___x_253_);
v___x_289_ = lean_string_append(v_acc_288_, v___x_253_);
return v___x_289_;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(1u);
v___x_291_ = l_Nat_reprFast(v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(lean_object* v_acc_292_, lean_object* v_tags_293_, lean_object* v_i_294_){
_start:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_array_get_size(v_tags_293_);
v___x_296_ = lean_nat_dec_lt(v_i_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_dec(v_i_294_);
return v_acc_292_;
}
else
{
lean_object* v___x_297_; lean_object* v___y_299_; lean_object* v___x_302_; lean_object* v_acc_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0, &l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0);
v_acc_303_ = lean_string_append(v_acc_292_, v___x_302_);
v___x_304_ = lean_nat_sub(v___x_295_, v___x_297_);
v___x_305_ = lean_nat_dec_lt(v_i_294_, v___x_304_);
lean_dec(v___x_304_);
if (v___x_305_ == 0)
{
v___y_299_ = v_acc_303_;
goto v___jp_298_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_307_ = lean_string_append(v_acc_303_, v___x_306_);
v___y_299_ = v___x_307_;
goto v___jp_298_;
}
v___jp_298_:
{
lean_object* v___x_300_; 
v___x_300_ = lean_nat_add(v_i_294_, v___x_297_);
lean_dec(v_i_294_);
v_acc_292_ = v___y_299_;
v_i_294_ = v___x_300_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___boxed(lean_object* v_acc_308_, lean_object* v_tags_309_, lean_object* v_i_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_308_, v_tags_309_, v_i_310_);
lean_dec_ref(v_tags_309_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(lean_object* v___x_312_, lean_object* v_val_313_, lean_object* v_it_314_, lean_object* v_acc_315_, lean_object* v_hP_316_, lean_object* v_recur_317_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = lean_nat_dec_eq(v_it_314_, v___x_312_);
if (v___x_318_ == 0)
{
uint32_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_string_utf8_get_fast(v_val_313_, v_it_314_);
v___x_320_ = lean_string_utf8_next_fast(v_val_313_, v_it_314_);
v___x_321_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_315_, v___x_319_);
v___x_322_ = lean_apply_4(v_recur_317_, v___x_320_, v___x_321_, lean_box(0), lean_box(0));
return v___x_322_;
}
else
{
lean_dec_ref(v_recur_317_);
return v_acc_315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed(lean_object* v___x_323_, lean_object* v_val_324_, lean_object* v_it_325_, lean_object* v_acc_326_, lean_object* v_hP_327_, lean_object* v_recur_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(v___x_323_, v_val_324_, v_it_325_, v_acc_326_, v_hP_327_, v_recur_328_);
lean_dec(v_it_325_);
lean_dec_ref(v_val_324_);
lean_dec(v___x_323_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(lean_object* v___x_330_, lean_object* v_label_331_, lean_object* v_it_332_, lean_object* v_acc_333_, lean_object* v_hP_334_, lean_object* v_recur_335_){
_start:
{
uint8_t v___x_336_; 
v___x_336_ = lean_nat_dec_eq(v_it_332_, v___x_330_);
if (v___x_336_ == 0)
{
uint32_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_337_ = lean_string_utf8_get_fast(v_label_331_, v_it_332_);
v___x_338_ = lean_string_utf8_next_fast(v_label_331_, v_it_332_);
v___x_339_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_333_, v___x_337_);
v___x_340_ = lean_apply_4(v_recur_335_, v___x_338_, v___x_339_, lean_box(0), lean_box(0));
return v___x_340_;
}
else
{
lean_dec_ref(v_recur_335_);
return v_acc_333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed(lean_object* v___x_341_, lean_object* v_label_342_, lean_object* v_it_343_, lean_object* v_acc_344_, lean_object* v_hP_345_, lean_object* v_recur_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(v___x_341_, v_label_342_, v_it_343_, v_acc_344_, v_hP_345_, v_recur_346_);
lean_dec(v_it_343_);
lean_dec_ref(v_label_342_);
lean_dec(v___x_341_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast(lean_object* v_acc_356_, lean_object* v_item_357_){
_start:
{
lean_object* v_acc_359_; lean_object* v_acc_363_; lean_object* v_label_366_; lean_object* v_detail_x3f_367_; lean_object* v_documentation_x3f_368_; lean_object* v_kind_x3f_369_; lean_object* v_textEdit_x3f_370_; lean_object* v_sortText_x3f_371_; lean_object* v_data_x3f_372_; lean_object* v_tags_x3f_373_; lean_object* v_acc_375_; lean_object* v_acc_388_; lean_object* v___y_392_; lean_object* v___y_396_; lean_object* v___y_400_; lean_object* v_id_x3f_401_; lean_object* v_acc_402_; lean_object* v_pos_432_; lean_object* v_cPos_x3f_433_; lean_object* v_id_x3f_434_; lean_object* v___y_435_; lean_object* v_acc_450_; lean_object* v_acc_473_; lean_object* v_acc_490_; lean_object* v_acc_559_; lean_object* v___y_570_; lean_object* v_value_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v_acc_595_; lean_object* v___y_604_; lean_object* v___x_620_; lean_object* v_acc_621_; lean_object* v___x_622_; lean_object* v_acc_623_; uint8_t v___x_624_; 
v_label_366_ = lean_ctor_get(v_item_357_, 0);
lean_inc_ref(v_label_366_);
v_detail_x3f_367_ = lean_ctor_get(v_item_357_, 1);
lean_inc(v_detail_x3f_367_);
v_documentation_x3f_368_ = lean_ctor_get(v_item_357_, 2);
lean_inc(v_documentation_x3f_368_);
v_kind_x3f_369_ = lean_ctor_get(v_item_357_, 3);
lean_inc(v_kind_x3f_369_);
v_textEdit_x3f_370_ = lean_ctor_get(v_item_357_, 4);
lean_inc(v_textEdit_x3f_370_);
v_sortText_x3f_371_ = lean_ctor_get(v_item_357_, 5);
lean_inc(v_sortText_x3f_371_);
v_data_x3f_372_ = lean_ctor_get(v_item_357_, 6);
lean_inc(v_data_x3f_372_);
v_tags_x3f_373_ = lean_ctor_get(v_item_357_, 7);
lean_inc(v_tags_x3f_373_);
lean_dec_ref(v_item_357_);
v___x_620_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7));
v_acc_621_ = lean_string_append(v_acc_356_, v___x_620_);
v___x_622_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_623_ = lean_string_append(v_acc_621_, v___x_622_);
v___x_624_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_label_366_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = lean_string_append(v_acc_623_, v_label_366_);
lean_dec_ref(v_label_366_);
v___x_626_ = lean_string_append(v___x_625_, v___x_622_);
v___y_604_ = v___x_626_;
goto v___jp_603_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___f_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_string_utf8_byte_size(v_label_366_);
lean_inc_ref(v_label_366_);
v___f_629_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed), 6, 2);
lean_closure_set(v___f_629_, 0, v___x_628_);
lean_closure_set(v___f_629_, 1, v_label_366_);
v___x_630_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_630_, 0, v_label_366_);
lean_ctor_set(v___x_630_, 1, v___x_627_);
lean_ctor_set(v___x_630_, 2, v___x_628_);
v___x_631_ = l_String_Slice_positions(v___x_630_);
lean_dec_ref(v___x_630_);
v___x_632_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_629_, v___x_631_, v_acc_623_, lean_box(0));
v___x_633_ = lean_string_append(v___x_632_, v___x_622_);
v___y_604_ = v___x_633_;
goto v___jp_603_;
}
v___jp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_361_ = lean_string_append(v_acc_359_, v___x_360_);
return v___x_361_;
}
v___jp_362_:
{
lean_object* v___x_364_; lean_object* v_acc_365_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v_acc_365_ = lean_string_append(v_acc_363_, v___x_364_);
v_acc_359_ = v_acc_365_;
goto v___jp_358_;
}
v___jp_374_:
{
if (lean_obj_tag(v_tags_x3f_373_) == 1)
{
lean_object* v_val_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v_val_376_ = lean_ctor_get(v_tags_x3f_373_, 0);
lean_inc(v_val_376_);
lean_dec_ref(v_tags_x3f_373_);
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = lean_array_get_size(v_val_376_);
v___x_379_ = lean_nat_dec_lt(v___x_377_, v___x_378_);
if (v___x_379_ == 0)
{
lean_dec(v_val_376_);
v_acc_359_ = v_acc_375_;
goto v___jp_358_;
}
else
{
lean_object* v___x_380_; lean_object* v_acc_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0));
v_acc_381_ = lean_string_append(v_acc_375_, v___x_380_);
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_nat_dec_eq(v___x_378_, v___x_382_);
if (v___x_383_ == 0)
{
lean_object* v_acc_384_; 
v_acc_384_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_381_, v_val_376_, v___x_377_);
lean_dec(v_val_376_);
v_acc_363_ = v_acc_384_;
goto v___jp_362_;
}
else
{
lean_object* v___x_385_; lean_object* v_acc_386_; 
lean_dec(v_val_376_);
v___x_385_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0, &l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0);
v_acc_386_ = lean_string_append(v_acc_381_, v___x_385_);
v_acc_363_ = v_acc_386_;
goto v___jp_362_;
}
}
}
else
{
lean_dec(v_tags_x3f_373_);
v_acc_359_ = v_acc_375_;
goto v___jp_358_;
}
}
v___jp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v___x_390_ = lean_string_append(v_acc_388_, v___x_389_);
v_acc_375_ = v___x_390_;
goto v___jp_374_;
}
v___jp_391_:
{
lean_object* v___x_393_; lean_object* v_acc_394_; 
v___x_393_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_394_ = lean_string_append(v___y_392_, v___x_393_);
v_acc_388_ = v_acc_394_;
goto v___jp_387_;
}
v___jp_395_:
{
lean_object* v___x_397_; lean_object* v_acc_398_; 
v___x_397_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_398_ = lean_string_append(v___y_396_, v___x_397_);
v_acc_388_ = v_acc_398_;
goto v___jp_387_;
}
v___jp_399_:
{
if (lean_obj_tag(v_id_x3f_401_) == 1)
{
lean_object* v_val_403_; lean_object* v_acc_404_; 
v_val_403_ = lean_ctor_get(v_id_x3f_401_, 0);
lean_inc(v_val_403_);
lean_dec_ref(v_id_x3f_401_);
v_acc_404_ = lean_string_append(v_acc_402_, v___y_400_);
if (lean_obj_tag(v_val_403_) == 0)
{
lean_object* v_declName_405_; lean_object* v___x_406_; lean_object* v_acc_407_; uint8_t v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_declName_405_ = lean_ctor_get(v_val_403_, 0);
lean_inc(v_declName_405_);
lean_dec_ref(v_val_403_);
v___x_406_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2));
v_acc_407_ = lean_string_append(v_acc_404_, v___x_406_);
v___x_408_ = 1;
v___x_409_ = l_Lean_Name_toString(v_declName_405_, v___x_408_);
v___x_410_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
v___x_411_ = lean_string_append(v_acc_407_, v___x_409_);
lean_dec_ref(v___x_409_);
v___y_396_ = v___x_411_;
goto v___jp_395_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_string_utf8_byte_size(v___x_409_);
lean_inc_ref(v___x_409_);
v___f_414_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_414_, 0, v___x_413_);
lean_closure_set(v___f_414_, 1, v___x_409_);
v___x_415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_415_, 0, v___x_409_);
lean_ctor_set(v___x_415_, 1, v___x_412_);
lean_ctor_set(v___x_415_, 2, v___x_413_);
v___x_416_ = l_String_Slice_positions(v___x_415_);
lean_dec_ref(v___x_415_);
v___x_417_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_414_, v___x_416_, v_acc_407_, lean_box(0));
v___y_396_ = v___x_417_;
goto v___jp_395_;
}
}
else
{
lean_object* v_id_418_; lean_object* v___x_419_; lean_object* v_acc_420_; uint8_t v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_id_418_ = lean_ctor_get(v_val_403_, 0);
lean_inc(v_id_418_);
lean_dec_ref(v_val_403_);
v___x_419_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
v_acc_420_ = lean_string_append(v_acc_404_, v___x_419_);
v___x_421_ = 1;
v___x_422_ = l_Lean_Name_toString(v_id_418_, v___x_421_);
v___x_423_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
v___x_424_ = lean_string_append(v_acc_420_, v___x_422_);
lean_dec_ref(v___x_422_);
v___y_392_ = v___x_424_;
goto v___jp_391_;
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___f_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = lean_string_utf8_byte_size(v___x_422_);
lean_inc_ref(v___x_422_);
v___f_427_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_427_, 0, v___x_426_);
lean_closure_set(v___f_427_, 1, v___x_422_);
v___x_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_428_, 0, v___x_422_);
lean_ctor_set(v___x_428_, 1, v___x_425_);
lean_ctor_set(v___x_428_, 2, v___x_426_);
v___x_429_ = l_String_Slice_positions(v___x_428_);
lean_dec_ref(v___x_428_);
v___x_430_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_427_, v___x_429_, v_acc_420_, lean_box(0));
v___y_392_ = v___x_430_;
goto v___jp_391_;
}
}
}
else
{
lean_dec(v_id_x3f_401_);
v_acc_388_ = v_acc_402_;
goto v___jp_387_;
}
}
v___jp_431_:
{
lean_object* v_line_436_; lean_object* v_character_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v_acc_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_acc_444_; 
v_line_436_ = lean_ctor_get(v_pos_432_, 0);
lean_inc(v_line_436_);
v_character_437_ = lean_ctor_get(v_pos_432_, 1);
lean_inc(v_character_437_);
lean_dec_ref(v_pos_432_);
v___x_438_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_439_ = lean_string_append(v___y_435_, v___x_438_);
v___x_440_ = l_Nat_reprFast(v_line_436_);
v_acc_441_ = lean_string_append(v___x_439_, v___x_440_);
lean_dec_ref(v___x_440_);
v___x_442_ = lean_string_append(v_acc_441_, v___x_438_);
v___x_443_ = l_Nat_reprFast(v_character_437_);
v_acc_444_ = lean_string_append(v___x_442_, v___x_443_);
lean_dec_ref(v___x_443_);
if (lean_obj_tag(v_cPos_x3f_433_) == 1)
{
lean_object* v_val_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_acc_448_; 
v_val_445_ = lean_ctor_get(v_cPos_x3f_433_, 0);
lean_inc(v_val_445_);
lean_dec_ref(v_cPos_x3f_433_);
v___x_446_ = lean_string_append(v_acc_444_, v___x_438_);
v___x_447_ = l_Nat_reprFast(v_val_445_);
v_acc_448_ = lean_string_append(v___x_446_, v___x_447_);
lean_dec_ref(v___x_447_);
v___y_400_ = v___x_438_;
v_id_x3f_401_ = v_id_x3f_434_;
v_acc_402_ = v_acc_448_;
goto v___jp_399_;
}
else
{
lean_dec(v_cPos_x3f_433_);
v___y_400_ = v___x_438_;
v_id_x3f_401_ = v_id_x3f_434_;
v_acc_402_ = v_acc_444_;
goto v___jp_399_;
}
}
v___jp_449_:
{
if (lean_obj_tag(v_data_x3f_372_) == 1)
{
lean_object* v_val_451_; lean_object* v_uri_452_; lean_object* v_pos_453_; lean_object* v_cPos_x3f_454_; lean_object* v_id_x3f_455_; lean_object* v___x_456_; lean_object* v_acc_457_; lean_object* v___x_458_; lean_object* v_acc_459_; lean_object* v___x_460_; lean_object* v_acc_461_; uint8_t v___x_462_; 
v_val_451_ = lean_ctor_get(v_data_x3f_372_, 0);
lean_inc(v_val_451_);
lean_dec_ref(v_data_x3f_372_);
v_uri_452_ = lean_ctor_get(v_val_451_, 0);
lean_inc_ref(v_uri_452_);
v_pos_453_ = lean_ctor_get(v_val_451_, 1);
lean_inc_ref(v_pos_453_);
v_cPos_x3f_454_ = lean_ctor_get(v_val_451_, 2);
lean_inc(v_cPos_x3f_454_);
v_id_x3f_455_ = lean_ctor_get(v_val_451_, 3);
lean_inc(v_id_x3f_455_);
lean_dec(v_val_451_);
v___x_456_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1));
v_acc_457_ = lean_string_append(v_acc_450_, v___x_456_);
v___x_458_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
v_acc_459_ = lean_string_append(v_acc_457_, v___x_458_);
v___x_460_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_461_ = lean_string_append(v_acc_459_, v___x_460_);
v___x_462_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_452_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_string_append(v_acc_461_, v_uri_452_);
lean_dec_ref(v_uri_452_);
v___x_464_ = lean_string_append(v___x_463_, v___x_460_);
v_pos_432_ = v_pos_453_;
v_cPos_x3f_433_ = v_cPos_x3f_454_;
v_id_x3f_434_ = v_id_x3f_455_;
v___y_435_ = v___x_464_;
goto v___jp_431_;
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___f_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_string_utf8_byte_size(v_uri_452_);
lean_inc_ref(v_uri_452_);
v___f_467_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed), 6, 2);
lean_closure_set(v___f_467_, 0, v___x_466_);
lean_closure_set(v___f_467_, 1, v_uri_452_);
v___x_468_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_468_, 0, v_uri_452_);
lean_ctor_set(v___x_468_, 1, v___x_465_);
lean_ctor_set(v___x_468_, 2, v___x_466_);
v___x_469_ = l_String_Slice_positions(v___x_468_);
lean_dec_ref(v___x_468_);
v___x_470_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_467_, v___x_469_, v_acc_461_, lean_box(0));
v___x_471_ = lean_string_append(v___x_470_, v___x_460_);
v_pos_432_ = v_pos_453_;
v_cPos_x3f_433_ = v_cPos_x3f_454_;
v_id_x3f_434_ = v_id_x3f_455_;
v___y_435_ = v___x_471_;
goto v___jp_431_;
}
}
else
{
lean_dec(v_data_x3f_372_);
v_acc_375_ = v_acc_450_;
goto v___jp_374_;
}
}
v___jp_472_:
{
if (lean_obj_tag(v_sortText_x3f_371_) == 1)
{
lean_object* v_val_474_; lean_object* v___x_475_; lean_object* v_acc_476_; lean_object* v___x_477_; lean_object* v_acc_478_; uint8_t v___x_479_; 
v_val_474_ = lean_ctor_get(v_sortText_x3f_371_, 0);
lean_inc(v_val_474_);
lean_dec_ref(v_sortText_x3f_371_);
v___x_475_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2));
v_acc_476_ = lean_string_append(v_acc_473_, v___x_475_);
v___x_477_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_478_ = lean_string_append(v_acc_476_, v___x_477_);
v___x_479_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_474_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_string_append(v_acc_478_, v_val_474_);
lean_dec(v_val_474_);
v___x_481_ = lean_string_append(v___x_480_, v___x_477_);
v_acc_450_ = v___x_481_;
goto v___jp_449_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___f_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = lean_string_utf8_byte_size(v_val_474_);
lean_inc(v_val_474_);
v___f_484_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed), 6, 2);
lean_closure_set(v___f_484_, 0, v___x_483_);
lean_closure_set(v___f_484_, 1, v_val_474_);
v___x_485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_485_, 0, v_val_474_);
lean_ctor_set(v___x_485_, 1, v___x_482_);
lean_ctor_set(v___x_485_, 2, v___x_483_);
v___x_486_ = l_String_Slice_positions(v___x_485_);
lean_dec_ref(v___x_485_);
v___x_487_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_484_, v___x_486_, v_acc_478_, lean_box(0));
v___x_488_ = lean_string_append(v___x_487_, v___x_477_);
v_acc_450_ = v___x_488_;
goto v___jp_449_;
}
}
else
{
lean_dec(v_sortText_x3f_371_);
v_acc_450_ = v_acc_473_;
goto v___jp_449_;
}
}
v___jp_489_:
{
if (lean_obj_tag(v_textEdit_x3f_370_) == 1)
{
lean_object* v_val_491_; lean_object* v_insert_492_; lean_object* v_end_493_; lean_object* v_start_494_; lean_object* v_replace_495_; lean_object* v_end_496_; lean_object* v_start_497_; lean_object* v_newText_498_; lean_object* v_line_499_; lean_object* v_character_500_; lean_object* v_line_501_; lean_object* v_character_502_; lean_object* v_line_503_; lean_object* v_character_504_; lean_object* v_line_505_; lean_object* v_character_506_; lean_object* v___x_507_; lean_object* v_acc_508_; lean_object* v___x_509_; lean_object* v_acc_510_; lean_object* v___x_511_; lean_object* v_acc_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v_acc_522_; lean_object* v___x_523_; lean_object* v_acc_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_acc_531_; lean_object* v_acc_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_acc_537_; lean_object* v___x_538_; lean_object* v_acc_539_; lean_object* v_acc_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_acc_547_; lean_object* v_acc_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v_acc_555_; lean_object* v_acc_556_; lean_object* v_acc_557_; 
v_val_491_ = lean_ctor_get(v_textEdit_x3f_370_, 0);
lean_inc(v_val_491_);
lean_dec_ref(v_textEdit_x3f_370_);
v_insert_492_ = lean_ctor_get(v_val_491_, 1);
v_end_493_ = lean_ctor_get(v_insert_492_, 1);
lean_inc_ref(v_end_493_);
v_start_494_ = lean_ctor_get(v_insert_492_, 0);
lean_inc_ref(v_start_494_);
v_replace_495_ = lean_ctor_get(v_val_491_, 2);
v_end_496_ = lean_ctor_get(v_replace_495_, 1);
lean_inc_ref(v_end_496_);
v_start_497_ = lean_ctor_get(v_replace_495_, 0);
lean_inc_ref(v_start_497_);
v_newText_498_ = lean_ctor_get(v_val_491_, 0);
lean_inc_ref(v_newText_498_);
lean_dec(v_val_491_);
v_line_499_ = lean_ctor_get(v_end_493_, 0);
lean_inc(v_line_499_);
v_character_500_ = lean_ctor_get(v_end_493_, 1);
lean_inc(v_character_500_);
lean_dec_ref(v_end_493_);
v_line_501_ = lean_ctor_get(v_start_494_, 0);
lean_inc(v_line_501_);
v_character_502_ = lean_ctor_get(v_start_494_, 1);
lean_inc(v_character_502_);
lean_dec_ref(v_start_494_);
v_line_503_ = lean_ctor_get(v_end_496_, 0);
lean_inc(v_line_503_);
v_character_504_ = lean_ctor_get(v_end_496_, 1);
lean_inc(v_character_504_);
lean_dec_ref(v_end_496_);
v_line_505_ = lean_ctor_get(v_start_497_, 0);
lean_inc(v_line_505_);
v_character_506_ = lean_ctor_get(v_start_497_, 1);
lean_inc(v_character_506_);
lean_dec_ref(v_start_497_);
v___x_507_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3));
v_acc_508_ = lean_string_append(v_acc_490_, v___x_507_);
v___x_509_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
v_acc_510_ = lean_string_append(v_acc_508_, v___x_509_);
v___x_511_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
v_acc_512_ = lean_string_append(v_acc_510_, v___x_511_);
v___x_513_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_514_ = lean_string_append(v_acc_512_, v___x_513_);
v___x_515_ = l_Nat_reprFast(v_character_500_);
v___x_516_ = lean_string_append(v___x_514_, v___x_515_);
lean_dec_ref(v___x_515_);
v___x_517_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_518_ = lean_string_append(v___x_516_, v___x_517_);
v___x_519_ = l_Nat_reprFast(v_line_499_);
v___x_520_ = lean_string_append(v___x_518_, v___x_519_);
lean_dec_ref(v___x_519_);
v___x_521_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v_acc_522_ = lean_string_append(v___x_520_, v___x_521_);
v___x_523_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
v_acc_524_ = lean_string_append(v_acc_522_, v___x_523_);
v___x_525_ = lean_string_append(v_acc_524_, v___x_513_);
v___x_526_ = l_Nat_reprFast(v_character_502_);
v___x_527_ = lean_string_append(v___x_525_, v___x_526_);
lean_dec_ref(v___x_526_);
v___x_528_ = lean_string_append(v___x_527_, v___x_517_);
v___x_529_ = l_Nat_reprFast(v_line_501_);
v___x_530_ = lean_string_append(v___x_528_, v___x_529_);
lean_dec_ref(v___x_529_);
v_acc_531_ = lean_string_append(v___x_530_, v___x_521_);
v_acc_532_ = lean_string_append(v_acc_531_, v___x_521_);
v___x_533_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
v___x_534_ = lean_string_append(v_acc_532_, v___x_533_);
v___x_535_ = lean_string_append(v___x_534_, v_newText_498_);
lean_dec_ref(v_newText_498_);
v___x_536_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_537_ = lean_string_append(v___x_535_, v___x_536_);
v___x_538_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
v_acc_539_ = lean_string_append(v_acc_537_, v___x_538_);
v_acc_540_ = lean_string_append(v_acc_539_, v___x_511_);
v___x_541_ = lean_string_append(v_acc_540_, v___x_513_);
v___x_542_ = l_Nat_reprFast(v_character_504_);
v___x_543_ = lean_string_append(v___x_541_, v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = lean_string_append(v___x_543_, v___x_517_);
v___x_545_ = l_Nat_reprFast(v_line_503_);
v___x_546_ = lean_string_append(v___x_544_, v___x_545_);
lean_dec_ref(v___x_545_);
v_acc_547_ = lean_string_append(v___x_546_, v___x_521_);
v_acc_548_ = lean_string_append(v_acc_547_, v___x_523_);
v___x_549_ = lean_string_append(v_acc_548_, v___x_513_);
v___x_550_ = l_Nat_reprFast(v_character_506_);
v___x_551_ = lean_string_append(v___x_549_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = lean_string_append(v___x_551_, v___x_517_);
v___x_553_ = l_Nat_reprFast(v_line_505_);
v___x_554_ = lean_string_append(v___x_552_, v___x_553_);
lean_dec_ref(v___x_553_);
v_acc_555_ = lean_string_append(v___x_554_, v___x_521_);
v_acc_556_ = lean_string_append(v_acc_555_, v___x_521_);
v_acc_557_ = lean_string_append(v_acc_556_, v___x_521_);
v_acc_473_ = v_acc_557_;
goto v___jp_472_;
}
else
{
lean_dec(v_textEdit_x3f_370_);
v_acc_473_ = v_acc_490_;
goto v___jp_472_;
}
}
v___jp_558_:
{
if (lean_obj_tag(v_kind_x3f_369_) == 1)
{
lean_object* v_val_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v_acc_568_; 
v_val_560_ = lean_ctor_get(v_kind_x3f_369_, 0);
lean_inc(v_val_560_);
lean_dec_ref(v_kind_x3f_369_);
v___x_561_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4));
v___x_562_ = lean_string_append(v_acc_559_, v___x_561_);
v___x_563_ = lean_unbox(v_val_560_);
lean_dec(v_val_560_);
v___x_564_ = l_Lean_Lsp_CompletionItemKind_ctorIdx(v___x_563_);
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_add(v___x_564_, v___x_565_);
lean_dec(v___x_564_);
v___x_567_ = l_Nat_reprFast(v___x_566_);
v_acc_568_ = lean_string_append(v___x_562_, v___x_567_);
lean_dec_ref(v___x_567_);
v_acc_490_ = v_acc_568_;
goto v___jp_489_;
}
else
{
lean_dec(v_kind_x3f_369_);
v_acc_490_ = v_acc_559_;
goto v___jp_489_;
}
}
v___jp_569_:
{
lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_571_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_572_ = lean_string_append(v___y_570_, v___x_571_);
v_acc_559_ = v___x_572_;
goto v___jp_558_;
}
v___jp_573_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_acc_581_; lean_object* v___x_582_; lean_object* v_acc_583_; uint8_t v___x_584_; 
v___x_577_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
v___x_578_ = lean_string_append(v___y_575_, v___x_577_);
v___x_579_ = lean_string_append(v___x_578_, v___y_576_);
v___x_580_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
v_acc_581_ = lean_string_append(v___x_579_, v___x_580_);
v___x_582_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_583_ = lean_string_append(v_acc_581_, v___x_582_);
v___x_584_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_574_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = lean_string_append(v_acc_583_, v_value_574_);
lean_dec_ref(v_value_574_);
v___x_586_ = lean_string_append(v___x_585_, v___x_582_);
v___y_570_ = v___x_586_;
goto v___jp_569_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_string_utf8_byte_size(v_value_574_);
lean_inc_ref(v_value_574_);
v___f_589_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_589_, 0, v___x_588_);
lean_closure_set(v___f_589_, 1, v_value_574_);
v___x_590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_590_, 0, v_value_574_);
lean_ctor_set(v___x_590_, 1, v___x_587_);
lean_ctor_set(v___x_590_, 2, v___x_588_);
v___x_591_ = l_String_Slice_positions(v___x_590_);
lean_dec_ref(v___x_590_);
v___x_592_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_589_, v___x_591_, v_acc_583_, lean_box(0));
v___x_593_ = lean_string_append(v___x_592_, v___x_582_);
v___y_570_ = v___x_593_;
goto v___jp_569_;
}
}
v___jp_594_:
{
if (lean_obj_tag(v_documentation_x3f_368_) == 1)
{
lean_object* v_val_596_; uint8_t v_kind_597_; lean_object* v_value_598_; lean_object* v___x_599_; lean_object* v_acc_600_; 
v_val_596_ = lean_ctor_get(v_documentation_x3f_368_, 0);
lean_inc(v_val_596_);
lean_dec_ref(v_documentation_x3f_368_);
v_kind_597_ = lean_ctor_get_uint8(v_val_596_, sizeof(void*)*1);
v_value_598_ = lean_ctor_get(v_val_596_, 0);
lean_inc_ref(v_value_598_);
lean_dec(v_val_596_);
v___x_599_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5));
v_acc_600_ = lean_string_append(v_acc_595_, v___x_599_);
if (v_kind_597_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
v_value_574_ = v_value_598_;
v___y_575_ = v_acc_600_;
v___y_576_ = v___x_601_;
goto v___jp_573_;
}
else
{
lean_object* v___x_602_; 
v___x_602_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
v_value_574_ = v_value_598_;
v___y_575_ = v_acc_600_;
v___y_576_ = v___x_602_;
goto v___jp_573_;
}
}
else
{
lean_dec(v_documentation_x3f_368_);
v_acc_559_ = v_acc_595_;
goto v___jp_558_;
}
}
v___jp_603_:
{
if (lean_obj_tag(v_detail_x3f_367_) == 1)
{
lean_object* v_val_605_; lean_object* v___x_606_; lean_object* v_acc_607_; lean_object* v___x_608_; lean_object* v_acc_609_; uint8_t v___x_610_; 
v_val_605_ = lean_ctor_get(v_detail_x3f_367_, 0);
lean_inc(v_val_605_);
lean_dec_ref(v_detail_x3f_367_);
v___x_606_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6));
v_acc_607_ = lean_string_append(v___y_604_, v___x_606_);
v___x_608_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_609_ = lean_string_append(v_acc_607_, v___x_608_);
v___x_610_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_605_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_string_append(v_acc_609_, v_val_605_);
lean_dec(v_val_605_);
v___x_612_ = lean_string_append(v___x_611_, v___x_608_);
v_acc_595_ = v___x_612_;
goto v___jp_594_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___f_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_string_utf8_byte_size(v_val_605_);
lean_inc(v_val_605_);
v___f_615_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed), 6, 2);
lean_closure_set(v___f_615_, 0, v___x_614_);
lean_closure_set(v___f_615_, 1, v_val_605_);
v___x_616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_616_, 0, v_val_605_);
lean_ctor_set(v___x_616_, 1, v___x_613_);
lean_ctor_set(v___x_616_, 2, v___x_614_);
v___x_617_ = l_String_Slice_positions(v___x_616_);
lean_dec_ref(v___x_616_);
v___x_618_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_615_, v___x_617_, v_acc_609_, lean_box(0));
v___x_619_ = lean_string_append(v___x_618_, v___x_608_);
v_acc_595_ = v___x_619_;
goto v___jp_594_;
}
}
else
{
lean_dec(v_detail_x3f_367_);
v_acc_595_ = v___y_604_;
goto v___jp_594_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(lean_object* v___x_634_, lean_object* v___x_635_, lean_object* v_a_636_, lean_object* v_b_637_){
_start:
{
lean_object* v_startInclusive_638_; lean_object* v_endExclusive_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_startInclusive_638_ = lean_ctor_get(v___x_634_, 1);
v_endExclusive_639_ = lean_ctor_get(v___x_634_, 2);
v___x_640_ = lean_nat_sub(v_endExclusive_639_, v_startInclusive_638_);
v___x_641_ = lean_nat_dec_eq(v_a_636_, v___x_640_);
lean_dec(v___x_640_);
if (v___x_641_ == 0)
{
uint32_t v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_string_utf8_get_fast(v___x_635_, v_a_636_);
v___x_643_ = lean_string_utf8_next_fast(v___x_635_, v_a_636_);
lean_dec(v_a_636_);
v___x_644_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_b_637_, v___x_642_);
v_a_636_ = v___x_643_;
v_b_637_ = v___x_644_;
goto _start;
}
else
{
lean_dec(v_a_636_);
return v_b_637_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg___boxed(lean_object* v___x_646_, lean_object* v___x_647_, lean_object* v_a_648_, lean_object* v_b_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_646_, v___x_647_, v_a_648_, v_b_649_);
lean_dec_ref(v___x_647_);
lean_dec_ref(v___x_646_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(lean_object* v_acc_651_, lean_object* v_items_652_, lean_object* v_i_653_){
_start:
{
lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___x_659_; lean_object* v_acc_661_; lean_object* v_acc_670_; uint8_t v___x_673_; 
v___x_659_ = lean_array_get_size(v_items_652_);
v___x_673_ = lean_nat_dec_lt(v_i_653_, v___x_659_);
if (v___x_673_ == 0)
{
lean_dec(v_i_653_);
return v_acc_651_;
}
else
{
lean_object* v___x_674_; lean_object* v_acc_676_; lean_object* v_acc_690_; lean_object* v___y_694_; lean_object* v___y_698_; lean_object* v___y_702_; lean_object* v_id_x3f_703_; lean_object* v_acc_704_; lean_object* v_pos_730_; lean_object* v_cPos_x3f_731_; lean_object* v_id_x3f_732_; lean_object* v___y_733_; lean_object* v_acc_748_; lean_object* v_acc_771_; lean_object* v_acc_788_; lean_object* v_acc_858_; lean_object* v___y_870_; lean_object* v___y_874_; lean_object* v_value_875_; lean_object* v___y_876_; lean_object* v_acc_894_; lean_object* v___y_904_; lean_object* v_label_920_; lean_object* v___x_921_; lean_object* v_acc_922_; lean_object* v___x_923_; lean_object* v_acc_924_; uint8_t v___x_925_; 
v___x_674_ = lean_array_fget_borrowed(v_items_652_, v_i_653_);
v_label_920_ = lean_ctor_get(v___x_674_, 0);
v___x_921_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7));
v_acc_922_ = lean_string_append(v_acc_651_, v___x_921_);
v___x_923_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_924_ = lean_string_append(v_acc_922_, v___x_923_);
v___x_925_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_label_920_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_string_append(v_acc_924_, v_label_920_);
v___x_927_ = lean_string_append(v___x_926_, v___x_923_);
v___y_904_ = v___x_927_;
goto v___jp_903_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_string_utf8_byte_size(v_label_920_);
lean_inc_ref(v_label_920_);
v___x_930_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_930_, 0, v_label_920_);
lean_ctor_set(v___x_930_, 1, v___x_928_);
lean_ctor_set(v___x_930_, 2, v___x_929_);
v___x_931_ = l_String_Slice_positions(v___x_930_);
v___x_932_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_930_, v_label_920_, v___x_931_, v_acc_924_);
lean_dec_ref(v___x_930_);
v___x_933_ = lean_string_append(v___x_932_, v___x_923_);
v___y_904_ = v___x_933_;
goto v___jp_903_;
}
v___jp_675_:
{
lean_object* v_tags_x3f_677_; 
v_tags_x3f_677_ = lean_ctor_get(v___x_674_, 7);
if (lean_obj_tag(v_tags_x3f_677_) == 1)
{
lean_object* v_val_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_val_678_ = lean_ctor_get(v_tags_x3f_677_, 0);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_array_get_size(v_val_678_);
v___x_681_ = lean_nat_dec_lt(v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
v_acc_661_ = v_acc_676_;
goto v___jp_660_;
}
else
{
lean_object* v___x_682_; lean_object* v_acc_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_682_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0));
v_acc_683_ = lean_string_append(v_acc_676_, v___x_682_);
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = lean_nat_dec_eq(v___x_680_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v_acc_686_; 
v_acc_686_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_683_, v_val_678_, v___x_679_);
v_acc_670_ = v_acc_686_;
goto v___jp_669_;
}
else
{
lean_object* v___x_687_; lean_object* v_acc_688_; 
v___x_687_ = lean_obj_once(&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0, &l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0_once, _init_l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0);
v_acc_688_ = lean_string_append(v_acc_683_, v___x_687_);
v_acc_670_ = v_acc_688_;
goto v___jp_669_;
}
}
}
else
{
v_acc_661_ = v_acc_676_;
goto v___jp_660_;
}
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v___x_692_ = lean_string_append(v_acc_690_, v___x_691_);
v_acc_676_ = v___x_692_;
goto v___jp_675_;
}
v___jp_693_:
{
lean_object* v___x_695_; lean_object* v_acc_696_; 
v___x_695_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_696_ = lean_string_append(v___y_694_, v___x_695_);
v_acc_690_ = v_acc_696_;
goto v___jp_689_;
}
v___jp_697_:
{
lean_object* v___x_699_; lean_object* v_acc_700_; 
v___x_699_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_700_ = lean_string_append(v___y_698_, v___x_699_);
v_acc_690_ = v_acc_700_;
goto v___jp_689_;
}
v___jp_701_:
{
if (lean_obj_tag(v_id_x3f_703_) == 1)
{
lean_object* v_val_705_; lean_object* v_acc_706_; 
v_val_705_ = lean_ctor_get(v_id_x3f_703_, 0);
lean_inc(v_val_705_);
lean_dec_ref(v_id_x3f_703_);
v_acc_706_ = lean_string_append(v_acc_704_, v___y_702_);
if (lean_obj_tag(v_val_705_) == 0)
{
lean_object* v_declName_707_; lean_object* v___x_708_; lean_object* v_acc_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_declName_707_ = lean_ctor_get(v_val_705_, 0);
lean_inc(v_declName_707_);
lean_dec_ref(v_val_705_);
v___x_708_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2));
v_acc_709_ = lean_string_append(v_acc_706_, v___x_708_);
v___x_710_ = l_Lean_Name_toString(v_declName_707_, v___x_673_);
v___x_711_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
v___x_712_ = lean_string_append(v_acc_709_, v___x_710_);
lean_dec_ref(v___x_710_);
v___y_694_ = v___x_712_;
goto v___jp_693_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_713_ = lean_unsigned_to_nat(0u);
v___x_714_ = lean_string_utf8_byte_size(v___x_710_);
lean_inc_ref(v___x_710_);
v___x_715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_715_, 0, v___x_710_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
lean_ctor_set(v___x_715_, 2, v___x_714_);
v___x_716_ = l_String_Slice_positions(v___x_715_);
v___x_717_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_715_, v___x_710_, v___x_716_, v_acc_709_);
lean_dec_ref(v___x_710_);
lean_dec_ref(v___x_715_);
v___y_694_ = v___x_717_;
goto v___jp_693_;
}
}
else
{
lean_object* v_id_718_; lean_object* v___x_719_; lean_object* v_acc_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_id_718_ = lean_ctor_get(v_val_705_, 0);
lean_inc(v_id_718_);
lean_dec_ref(v_val_705_);
v___x_719_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
v_acc_720_ = lean_string_append(v_acc_706_, v___x_719_);
v___x_721_ = l_Lean_Name_toString(v_id_718_, v___x_673_);
v___x_722_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
v___x_723_ = lean_string_append(v_acc_720_, v___x_721_);
lean_dec_ref(v___x_721_);
v___y_698_ = v___x_723_;
goto v___jp_697_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_724_ = lean_unsigned_to_nat(0u);
v___x_725_ = lean_string_utf8_byte_size(v___x_721_);
lean_inc_ref(v___x_721_);
v___x_726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_726_, 0, v___x_721_);
lean_ctor_set(v___x_726_, 1, v___x_724_);
lean_ctor_set(v___x_726_, 2, v___x_725_);
v___x_727_ = l_String_Slice_positions(v___x_726_);
v___x_728_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_726_, v___x_721_, v___x_727_, v_acc_720_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v___x_726_);
v___y_698_ = v___x_728_;
goto v___jp_697_;
}
}
}
else
{
lean_dec(v_id_x3f_703_);
v_acc_690_ = v_acc_704_;
goto v___jp_689_;
}
}
v___jp_729_:
{
lean_object* v_line_734_; lean_object* v_character_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v_acc_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v_acc_742_; 
v_line_734_ = lean_ctor_get(v_pos_730_, 0);
lean_inc(v_line_734_);
v_character_735_ = lean_ctor_get(v_pos_730_, 1);
lean_inc(v_character_735_);
lean_dec_ref(v_pos_730_);
v___x_736_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_737_ = lean_string_append(v___y_733_, v___x_736_);
v___x_738_ = l_Nat_reprFast(v_line_734_);
v_acc_739_ = lean_string_append(v___x_737_, v___x_738_);
lean_dec_ref(v___x_738_);
v___x_740_ = lean_string_append(v_acc_739_, v___x_736_);
v___x_741_ = l_Nat_reprFast(v_character_735_);
v_acc_742_ = lean_string_append(v___x_740_, v___x_741_);
lean_dec_ref(v___x_741_);
if (lean_obj_tag(v_cPos_x3f_731_) == 1)
{
lean_object* v_val_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_acc_746_; 
v_val_743_ = lean_ctor_get(v_cPos_x3f_731_, 0);
lean_inc(v_val_743_);
lean_dec_ref(v_cPos_x3f_731_);
v___x_744_ = lean_string_append(v_acc_742_, v___x_736_);
v___x_745_ = l_Nat_reprFast(v_val_743_);
v_acc_746_ = lean_string_append(v___x_744_, v___x_745_);
lean_dec_ref(v___x_745_);
v___y_702_ = v___x_736_;
v_id_x3f_703_ = v_id_x3f_732_;
v_acc_704_ = v_acc_746_;
goto v___jp_701_;
}
else
{
lean_dec(v_cPos_x3f_731_);
v___y_702_ = v___x_736_;
v_id_x3f_703_ = v_id_x3f_732_;
v_acc_704_ = v_acc_742_;
goto v___jp_701_;
}
}
v___jp_747_:
{
lean_object* v_data_x3f_749_; 
v_data_x3f_749_ = lean_ctor_get(v___x_674_, 6);
if (lean_obj_tag(v_data_x3f_749_) == 1)
{
lean_object* v_val_750_; lean_object* v_uri_751_; lean_object* v_pos_752_; lean_object* v_cPos_x3f_753_; lean_object* v_id_x3f_754_; lean_object* v___x_755_; lean_object* v_acc_756_; lean_object* v___x_757_; lean_object* v_acc_758_; lean_object* v___x_759_; lean_object* v_acc_760_; uint8_t v___x_761_; 
v_val_750_ = lean_ctor_get(v_data_x3f_749_, 0);
v_uri_751_ = lean_ctor_get(v_val_750_, 0);
v_pos_752_ = lean_ctor_get(v_val_750_, 1);
v_cPos_x3f_753_ = lean_ctor_get(v_val_750_, 2);
v_id_x3f_754_ = lean_ctor_get(v_val_750_, 3);
v___x_755_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1));
v_acc_756_ = lean_string_append(v_acc_748_, v___x_755_);
v___x_757_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
v_acc_758_ = lean_string_append(v_acc_756_, v___x_757_);
v___x_759_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_760_ = lean_string_append(v_acc_758_, v___x_759_);
v___x_761_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_751_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_string_append(v_acc_760_, v_uri_751_);
v___x_763_ = lean_string_append(v___x_762_, v___x_759_);
lean_inc(v_id_x3f_754_);
lean_inc(v_cPos_x3f_753_);
lean_inc_ref(v_pos_752_);
v_pos_730_ = v_pos_752_;
v_cPos_x3f_731_ = v_cPos_x3f_753_;
v_id_x3f_732_ = v_id_x3f_754_;
v___y_733_ = v___x_763_;
goto v___jp_729_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_string_utf8_byte_size(v_uri_751_);
lean_inc_ref(v_uri_751_);
v___x_766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_766_, 0, v_uri_751_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
lean_ctor_set(v___x_766_, 2, v___x_765_);
v___x_767_ = l_String_Slice_positions(v___x_766_);
v___x_768_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_766_, v_uri_751_, v___x_767_, v_acc_760_);
lean_dec_ref(v___x_766_);
v___x_769_ = lean_string_append(v___x_768_, v___x_759_);
lean_inc(v_id_x3f_754_);
lean_inc(v_cPos_x3f_753_);
lean_inc_ref(v_pos_752_);
v_pos_730_ = v_pos_752_;
v_cPos_x3f_731_ = v_cPos_x3f_753_;
v_id_x3f_732_ = v_id_x3f_754_;
v___y_733_ = v___x_769_;
goto v___jp_729_;
}
}
else
{
v_acc_676_ = v_acc_748_;
goto v___jp_675_;
}
}
v___jp_770_:
{
lean_object* v_sortText_x3f_772_; 
v_sortText_x3f_772_ = lean_ctor_get(v___x_674_, 5);
if (lean_obj_tag(v_sortText_x3f_772_) == 1)
{
lean_object* v_val_773_; lean_object* v___x_774_; lean_object* v_acc_775_; lean_object* v___x_776_; lean_object* v_acc_777_; uint8_t v___x_778_; 
v_val_773_ = lean_ctor_get(v_sortText_x3f_772_, 0);
v___x_774_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2));
v_acc_775_ = lean_string_append(v_acc_771_, v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_777_ = lean_string_append(v_acc_775_, v___x_776_);
v___x_778_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_773_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_string_append(v_acc_777_, v_val_773_);
v___x_780_ = lean_string_append(v___x_779_, v___x_776_);
v_acc_748_ = v___x_780_;
goto v___jp_747_;
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_string_utf8_byte_size(v_val_773_);
lean_inc(v_val_773_);
v___x_783_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_783_, 0, v_val_773_);
lean_ctor_set(v___x_783_, 1, v___x_781_);
lean_ctor_set(v___x_783_, 2, v___x_782_);
v___x_784_ = l_String_Slice_positions(v___x_783_);
v___x_785_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_783_, v_val_773_, v___x_784_, v_acc_777_);
lean_dec_ref(v___x_783_);
v___x_786_ = lean_string_append(v___x_785_, v___x_776_);
v_acc_748_ = v___x_786_;
goto v___jp_747_;
}
}
else
{
v_acc_748_ = v_acc_771_;
goto v___jp_747_;
}
}
v___jp_787_:
{
lean_object* v_textEdit_x3f_789_; 
v_textEdit_x3f_789_ = lean_ctor_get(v___x_674_, 4);
if (lean_obj_tag(v_textEdit_x3f_789_) == 1)
{
lean_object* v_val_790_; lean_object* v_insert_791_; lean_object* v_end_792_; lean_object* v_start_793_; lean_object* v_replace_794_; lean_object* v_end_795_; lean_object* v_start_796_; lean_object* v_newText_797_; lean_object* v_line_798_; lean_object* v_character_799_; lean_object* v_line_800_; lean_object* v_character_801_; lean_object* v_line_802_; lean_object* v_character_803_; lean_object* v_line_804_; lean_object* v_character_805_; lean_object* v___x_806_; lean_object* v_acc_807_; lean_object* v___x_808_; lean_object* v_acc_809_; lean_object* v___x_810_; lean_object* v_acc_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v_acc_821_; lean_object* v___x_822_; lean_object* v_acc_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v_acc_830_; lean_object* v_acc_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v_acc_836_; lean_object* v___x_837_; lean_object* v_acc_838_; lean_object* v_acc_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v_acc_846_; lean_object* v_acc_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v_acc_854_; lean_object* v_acc_855_; lean_object* v_acc_856_; 
v_val_790_ = lean_ctor_get(v_textEdit_x3f_789_, 0);
v_insert_791_ = lean_ctor_get(v_val_790_, 1);
v_end_792_ = lean_ctor_get(v_insert_791_, 1);
v_start_793_ = lean_ctor_get(v_insert_791_, 0);
v_replace_794_ = lean_ctor_get(v_val_790_, 2);
v_end_795_ = lean_ctor_get(v_replace_794_, 1);
v_start_796_ = lean_ctor_get(v_replace_794_, 0);
v_newText_797_ = lean_ctor_get(v_val_790_, 0);
v_line_798_ = lean_ctor_get(v_end_792_, 0);
v_character_799_ = lean_ctor_get(v_end_792_, 1);
v_line_800_ = lean_ctor_get(v_start_793_, 0);
v_character_801_ = lean_ctor_get(v_start_793_, 1);
v_line_802_ = lean_ctor_get(v_end_795_, 0);
v_character_803_ = lean_ctor_get(v_end_795_, 1);
v_line_804_ = lean_ctor_get(v_start_796_, 0);
v_character_805_ = lean_ctor_get(v_start_796_, 1);
v___x_806_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3));
v_acc_807_ = lean_string_append(v_acc_788_, v___x_806_);
v___x_808_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
v_acc_809_ = lean_string_append(v_acc_807_, v___x_808_);
v___x_810_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
v_acc_811_ = lean_string_append(v_acc_809_, v___x_810_);
v___x_812_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_813_ = lean_string_append(v_acc_811_, v___x_812_);
lean_inc(v_character_799_);
v___x_814_ = l_Nat_reprFast(v_character_799_);
v___x_815_ = lean_string_append(v___x_813_, v___x_814_);
lean_dec_ref(v___x_814_);
v___x_816_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_817_ = lean_string_append(v___x_815_, v___x_816_);
lean_inc(v_line_798_);
v___x_818_ = l_Nat_reprFast(v_line_798_);
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
lean_dec_ref(v___x_818_);
v___x_820_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v_acc_821_ = lean_string_append(v___x_819_, v___x_820_);
v___x_822_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
v_acc_823_ = lean_string_append(v_acc_821_, v___x_822_);
v___x_824_ = lean_string_append(v_acc_823_, v___x_812_);
lean_inc(v_character_801_);
v___x_825_ = l_Nat_reprFast(v_character_801_);
v___x_826_ = lean_string_append(v___x_824_, v___x_825_);
lean_dec_ref(v___x_825_);
v___x_827_ = lean_string_append(v___x_826_, v___x_816_);
lean_inc(v_line_800_);
v___x_828_ = l_Nat_reprFast(v_line_800_);
v___x_829_ = lean_string_append(v___x_827_, v___x_828_);
lean_dec_ref(v___x_828_);
v_acc_830_ = lean_string_append(v___x_829_, v___x_820_);
v_acc_831_ = lean_string_append(v_acc_830_, v___x_820_);
v___x_832_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
v___x_833_ = lean_string_append(v_acc_831_, v___x_832_);
v___x_834_ = lean_string_append(v___x_833_, v_newText_797_);
v___x_835_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_836_ = lean_string_append(v___x_834_, v___x_835_);
v___x_837_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
v_acc_838_ = lean_string_append(v_acc_836_, v___x_837_);
v_acc_839_ = lean_string_append(v_acc_838_, v___x_810_);
v___x_840_ = lean_string_append(v_acc_839_, v___x_812_);
lean_inc(v_character_803_);
v___x_841_ = l_Nat_reprFast(v_character_803_);
v___x_842_ = lean_string_append(v___x_840_, v___x_841_);
lean_dec_ref(v___x_841_);
v___x_843_ = lean_string_append(v___x_842_, v___x_816_);
lean_inc(v_line_802_);
v___x_844_ = l_Nat_reprFast(v_line_802_);
v___x_845_ = lean_string_append(v___x_843_, v___x_844_);
lean_dec_ref(v___x_844_);
v_acc_846_ = lean_string_append(v___x_845_, v___x_820_);
v_acc_847_ = lean_string_append(v_acc_846_, v___x_822_);
v___x_848_ = lean_string_append(v_acc_847_, v___x_812_);
lean_inc(v_character_805_);
v___x_849_ = l_Nat_reprFast(v_character_805_);
v___x_850_ = lean_string_append(v___x_848_, v___x_849_);
lean_dec_ref(v___x_849_);
v___x_851_ = lean_string_append(v___x_850_, v___x_816_);
lean_inc(v_line_804_);
v___x_852_ = l_Nat_reprFast(v_line_804_);
v___x_853_ = lean_string_append(v___x_851_, v___x_852_);
lean_dec_ref(v___x_852_);
v_acc_854_ = lean_string_append(v___x_853_, v___x_820_);
v_acc_855_ = lean_string_append(v_acc_854_, v___x_820_);
v_acc_856_ = lean_string_append(v_acc_855_, v___x_820_);
v_acc_771_ = v_acc_856_;
goto v___jp_770_;
}
else
{
v_acc_771_ = v_acc_788_;
goto v___jp_770_;
}
}
v___jp_857_:
{
lean_object* v_kind_x3f_859_; 
v_kind_x3f_859_ = lean_ctor_get(v___x_674_, 3);
if (lean_obj_tag(v_kind_x3f_859_) == 1)
{
lean_object* v_val_860_; lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v_acc_868_; 
v_val_860_ = lean_ctor_get(v_kind_x3f_859_, 0);
v___x_861_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4));
v___x_862_ = lean_string_append(v_acc_858_, v___x_861_);
v___x_863_ = lean_unbox(v_val_860_);
v___x_864_ = l_Lean_Lsp_CompletionItemKind_ctorIdx(v___x_863_);
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_nat_add(v___x_864_, v___x_865_);
lean_dec(v___x_864_);
v___x_867_ = l_Nat_reprFast(v___x_866_);
v_acc_868_ = lean_string_append(v___x_862_, v___x_867_);
lean_dec_ref(v___x_867_);
v_acc_788_ = v_acc_868_;
goto v___jp_787_;
}
else
{
v_acc_788_ = v_acc_858_;
goto v___jp_787_;
}
}
v___jp_869_:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_872_ = lean_string_append(v___y_870_, v___x_871_);
v_acc_858_ = v___x_872_;
goto v___jp_857_;
}
v___jp_873_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_acc_881_; lean_object* v___x_882_; lean_object* v_acc_883_; uint8_t v___x_884_; 
v___x_877_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
v___x_878_ = lean_string_append(v___y_874_, v___x_877_);
v___x_879_ = lean_string_append(v___x_878_, v___y_876_);
v___x_880_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
v_acc_881_ = lean_string_append(v___x_879_, v___x_880_);
v___x_882_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_883_ = lean_string_append(v_acc_881_, v___x_882_);
v___x_884_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_875_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = lean_string_append(v_acc_883_, v_value_875_);
lean_dec_ref(v_value_875_);
v___x_886_ = lean_string_append(v___x_885_, v___x_882_);
v___y_870_ = v___x_886_;
goto v___jp_869_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_887_ = lean_unsigned_to_nat(0u);
v___x_888_ = lean_string_utf8_byte_size(v_value_875_);
lean_inc_ref(v_value_875_);
v___x_889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_889_, 0, v_value_875_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
lean_ctor_set(v___x_889_, 2, v___x_888_);
v___x_890_ = l_String_Slice_positions(v___x_889_);
v___x_891_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_889_, v_value_875_, v___x_890_, v_acc_883_);
lean_dec_ref(v_value_875_);
lean_dec_ref(v___x_889_);
v___x_892_ = lean_string_append(v___x_891_, v___x_882_);
v___y_870_ = v___x_892_;
goto v___jp_869_;
}
}
v___jp_893_:
{
lean_object* v_documentation_x3f_895_; 
v_documentation_x3f_895_ = lean_ctor_get(v___x_674_, 2);
if (lean_obj_tag(v_documentation_x3f_895_) == 1)
{
lean_object* v_val_896_; uint8_t v_kind_897_; lean_object* v_value_898_; lean_object* v___x_899_; lean_object* v_acc_900_; 
v_val_896_ = lean_ctor_get(v_documentation_x3f_895_, 0);
v_kind_897_ = lean_ctor_get_uint8(v_val_896_, sizeof(void*)*1);
v_value_898_ = lean_ctor_get(v_val_896_, 0);
v___x_899_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5));
v_acc_900_ = lean_string_append(v_acc_894_, v___x_899_);
if (v_kind_897_ == 0)
{
lean_object* v___x_901_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
lean_inc_ref(v_value_898_);
v___y_874_ = v_acc_900_;
v_value_875_ = v_value_898_;
v___y_876_ = v___x_901_;
goto v___jp_873_;
}
else
{
lean_object* v___x_902_; 
v___x_902_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
lean_inc_ref(v_value_898_);
v___y_874_ = v_acc_900_;
v_value_875_ = v_value_898_;
v___y_876_ = v___x_902_;
goto v___jp_873_;
}
}
else
{
v_acc_858_ = v_acc_894_;
goto v___jp_857_;
}
}
v___jp_903_:
{
lean_object* v_detail_x3f_905_; 
v_detail_x3f_905_ = lean_ctor_get(v___x_674_, 1);
if (lean_obj_tag(v_detail_x3f_905_) == 1)
{
lean_object* v_val_906_; lean_object* v___x_907_; lean_object* v_acc_908_; lean_object* v___x_909_; lean_object* v_acc_910_; uint8_t v___x_911_; 
v_val_906_ = lean_ctor_get(v_detail_x3f_905_, 0);
v___x_907_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6));
v_acc_908_ = lean_string_append(v___y_904_, v___x_907_);
v___x_909_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_910_ = lean_string_append(v_acc_908_, v___x_909_);
v___x_911_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_906_);
if (v___x_911_ == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_string_append(v_acc_910_, v_val_906_);
v___x_913_ = lean_string_append(v___x_912_, v___x_909_);
v_acc_894_ = v___x_913_;
goto v___jp_893_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_string_utf8_byte_size(v_val_906_);
lean_inc(v_val_906_);
v___x_916_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_916_, 0, v_val_906_);
lean_ctor_set(v___x_916_, 1, v___x_914_);
lean_ctor_set(v___x_916_, 2, v___x_915_);
v___x_917_ = l_String_Slice_positions(v___x_916_);
v___x_918_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_916_, v_val_906_, v___x_917_, v_acc_910_);
lean_dec_ref(v___x_916_);
v___x_919_ = lean_string_append(v___x_918_, v___x_909_);
v_acc_894_ = v___x_919_;
goto v___jp_893_;
}
}
else
{
v_acc_894_ = v___y_904_;
goto v___jp_893_;
}
}
}
v___jp_654_:
{
lean_object* v___x_657_; 
v___x_657_ = lean_nat_add(v_i_653_, v___y_655_);
lean_dec(v_i_653_);
v_acc_651_ = v___y_656_;
v_i_653_ = v___x_657_;
goto _start;
}
v___jp_660_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_662_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_663_ = lean_string_append(v_acc_661_, v___x_662_);
v___x_664_ = lean_unsigned_to_nat(1u);
v___x_665_ = lean_nat_sub(v___x_659_, v___x_664_);
v___x_666_ = lean_nat_dec_lt(v_i_653_, v___x_665_);
lean_dec(v___x_665_);
if (v___x_666_ == 0)
{
v___y_655_ = v___x_664_;
v___y_656_ = v___x_663_;
goto v___jp_654_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_668_ = lean_string_append(v___x_663_, v___x_667_);
v___y_655_ = v___x_664_;
v___y_656_ = v___x_668_;
goto v___jp_654_;
}
}
v___jp_669_:
{
lean_object* v___x_671_; lean_object* v_acc_672_; 
v___x_671_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v_acc_672_ = lean_string_append(v_acc_670_, v___x_671_);
v_acc_661_ = v_acc_672_;
goto v___jp_660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast___boxed(lean_object* v_acc_934_, lean_object* v_items_935_, lean_object* v_i_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(v_acc_934_, v_items_935_, v_i_936_);
lean_dec_ref(v_items_935_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(lean_object* v___x_938_, lean_object* v___x_939_, lean_object* v_inst_940_, lean_object* v_R_941_, lean_object* v_a_942_, lean_object* v_b_943_, lean_object* v_c_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_938_, v___x_939_, v_a_942_, v_b_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___boxed(lean_object* v___x_946_, lean_object* v___x_947_, lean_object* v_inst_948_, lean_object* v_R_949_, lean_object* v_a_950_, lean_object* v_b_951_, lean_object* v_c_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(v___x_946_, v___x_947_, v_inst_948_, v_R_949_, v_a_950_, v_b_951_, v_c_952_);
lean_dec_ref(v___x_947_);
lean_dec_ref(v___x_946_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast(lean_object* v_l_959_){
_start:
{
uint8_t v_isIncomplete_960_; lean_object* v_items_961_; lean_object* v___x_962_; lean_object* v___y_964_; 
v_isIncomplete_960_ = lean_ctor_get_uint8(v_l_959_, sizeof(void*)*1);
v_items_961_ = lean_ctor_get(v_l_959_, 0);
v___x_962_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0));
if (v_isIncomplete_960_ == 0)
{
lean_object* v___x_972_; 
v___x_972_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3));
v___y_964_ = v___x_972_;
goto v___jp_963_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4));
v___y_964_ = v___x_973_;
goto v___jp_963_;
}
v___jp_963_:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_acc_967_; lean_object* v___x_968_; lean_object* v_acc_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_965_ = lean_string_append(v___x_962_, v___y_964_);
v___x_966_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1));
v_acc_967_ = lean_string_append(v___x_965_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(0u);
v_acc_969_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(v_acc_967_, v_items_961_, v___x_968_);
v___x_970_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2));
v___x_971_ = lean_string_append(v_acc_969_, v___x_970_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___boxed(lean_object* v_l_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Lsp_ResolvableCompletionList_compressFast(v_l_974_);
lean_dec_ref(v_l_974_);
return v_res_975_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_CompletionItemCompression(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Completion_CompletionItemCompression(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionItemCompression(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Completion_CompletionItemCompression(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Completion_CompletionItemCompression(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Completion_CompletionItemCompression(builtin);
}
#ifdef __cplusplus
}
#endif

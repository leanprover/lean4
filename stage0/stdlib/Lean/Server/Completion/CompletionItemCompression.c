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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object*, uint32_t);
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
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
static lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
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
lean_object* l_Lean_Lsp_CompletionItemKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_3, x_1);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_string_utf8_next_fast(x_2, x_3);
x_9 = lean_string_utf8_get_fast(x_2, x_3);
x_10 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(x_4, x_9);
x_11 = lean_apply_4(x_6, x_8, x_10, lean_box(0), lean_box(0));
return x_11;
}
else
{
lean_dec_ref(x_6);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_3, x_1);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_string_utf8_next_fast(x_2, x_3);
x_9 = lean_string_utf8_get_fast(x_2, x_3);
x_10 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(x_4, x_9);
x_11 = lean_apply_4(x_6, x_8, x_10, lean_box(0), lean_box(0));
return x_11;
}
else
{
lean_dec_ref(x_6);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_50; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 3);
lean_inc(x_18);
lean_dec_ref(x_2);
x_65 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
x_66 = lean_string_append(x_1, x_65);
x_67 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_68 = lean_string_append(x_66, x_67);
x_69 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_15);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_string_append(x_68, x_15);
lean_dec_ref(x_15);
x_71 = lean_string_append(x_70, x_67);
x_50 = x_71;
goto block_64;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_string_utf8_byte_size(x_15);
lean_inc_ref(x_15);
x_74 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed), 6, 2);
lean_closure_set(x_74, 0, x_73);
lean_closure_set(x_74, 1, x_15);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_15);
lean_ctor_set(x_75, 1, x_72);
lean_ctor_set(x_75, 2, x_73);
x_76 = l_String_Slice_positions(x_75);
lean_dec_ref(x_75);
x_77 = l_WellFounded_opaqueFix_u2083___redArg(x_74, x_76, x_68, lean_box(0));
x_78 = lean_string_append(x_77, x_67);
x_50 = x_78;
goto block_64;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_9 = lean_string_append(x_7, x_8);
x_3 = x_9;
goto block_6;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_3 = x_13;
goto block_6;
}
block_49:
{
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_string_append(x_20, x_19);
lean_dec_ref(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2));
x_25 = lean_string_append(x_22, x_24);
x_26 = 1;
x_27 = l_Lean_Name_toString(x_23, x_26);
x_28 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_string_append(x_25, x_27);
lean_dec_ref(x_27);
x_7 = x_29;
goto block_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_string_utf8_byte_size(x_27);
lean_inc_ref(x_27);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(x_32, 0, x_31);
lean_closure_set(x_32, 1, x_27);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
x_34 = l_String_Slice_positions(x_33);
lean_dec_ref(x_33);
x_35 = l_WellFounded_opaqueFix_u2083___redArg(x_32, x_34, x_25, lean_box(0));
x_7 = x_35;
goto block_10;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_21, 0);
lean_inc(x_36);
lean_dec_ref(x_21);
x_37 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
x_38 = lean_string_append(x_22, x_37);
x_39 = 1;
x_40 = l_Lean_Name_toString(x_36, x_39);
x_41 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_string_append(x_38, x_40);
lean_dec_ref(x_40);
x_11 = x_42;
goto block_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_string_utf8_byte_size(x_40);
lean_inc_ref(x_40);
x_45 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(x_45, 0, x_44);
lean_closure_set(x_45, 1, x_40);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_44);
x_47 = l_String_Slice_positions(x_46);
lean_dec_ref(x_46);
x_48 = l_WellFounded_opaqueFix_u2083___redArg(x_45, x_47, x_38, lean_box(0));
x_11 = x_48;
goto block_14;
}
}
}
else
{
lean_dec_ref(x_19);
lean_dec(x_18);
x_3 = x_20;
goto block_6;
}
}
block_64:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_16, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_dec_ref(x_16);
x_53 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
x_54 = lean_string_append(x_50, x_53);
x_55 = l_Nat_reprFast(x_51);
x_56 = lean_string_append(x_54, x_55);
lean_dec_ref(x_55);
x_57 = lean_string_append(x_56, x_53);
x_58 = l_Nat_reprFast(x_52);
x_59 = lean_string_append(x_57, x_58);
lean_dec_ref(x_58);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_17, 0);
lean_inc(x_60);
lean_dec_ref(x_17);
x_61 = lean_string_append(x_59, x_53);
x_62 = l_Nat_reprFast(x_60);
x_63 = lean_string_append(x_61, x_62);
lean_dec_ref(x_62);
x_19 = x_53;
x_20 = x_63;
goto block_49;
}
else
{
lean_dec(x_17);
x_19 = x_53;
x_20 = x_59;
goto block_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_3, x_1);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_string_utf8_next_fast(x_2, x_3);
x_9 = lean_string_utf8_get_fast(x_2, x_3);
x_10 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(x_4, x_9);
x_11 = lean_apply_4(x_6, x_8, x_10, lean_box(0), lean_box(0));
return x_11;
}
else
{
lean_dec_ref(x_6);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_2);
if (x_7 == 0)
{
lean_object* x_28; 
x_28 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
x_9 = x_28;
goto block_27;
}
else
{
lean_object* x_29; 
x_29 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
x_9 = x_29;
goto block_27;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
block_27:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
x_11 = lean_string_append(x_1, x_10);
x_12 = lean_string_append(x_11, x_9);
lean_dec_ref(x_9);
x_13 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
x_14 = lean_string_append(x_12, x_13);
x_15 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_string_append(x_16, x_8);
lean_dec_ref(x_8);
x_19 = lean_string_append(x_18, x_15);
x_3 = x_19;
goto block_6;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_string_utf8_byte_size(x_8);
lean_inc_ref(x_8);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed), 6, 2);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_8);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_21);
x_24 = l_String_Slice_positions(x_23);
lean_dec_ref(x_23);
x_25 = l_WellFounded_opaqueFix_u2083___redArg(x_22, x_24, x_16, lean_box(0));
x_26 = lean_string_append(x_25, x_15);
x_3 = x_26;
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
x_6 = lean_string_append(x_1, x_5);
x_7 = l_Nat_reprFast(x_4);
x_8 = lean_string_append(x_6, x_7);
lean_dec_ref(x_7);
x_9 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Nat_reprFast(x_3);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
x_10 = lean_string_append(x_1, x_9);
x_11 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
x_12 = lean_string_append(x_10, x_11);
x_13 = l_Nat_reprFast(x_6);
x_14 = lean_string_append(x_12, x_13);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
x_16 = lean_string_append(x_14, x_15);
x_17 = l_Nat_reprFast(x_5);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
x_20 = lean_string_append(x_18, x_19);
x_21 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_string_append(x_22, x_11);
x_24 = l_Nat_reprFast(x_8);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = lean_string_append(x_25, x_15);
x_27 = l_Nat_reprFast(x_7);
x_28 = lean_string_append(x_26, x_27);
lean_dec_ref(x_27);
x_29 = lean_string_append(x_28, x_19);
x_30 = lean_string_append(x_29, x_19);
return x_30;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec_ref(x_5);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec_ref(x_7);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec_ref(x_8);
x_18 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
x_19 = lean_string_append(x_1, x_18);
x_20 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
x_21 = lean_string_append(x_19, x_20);
x_22 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
x_23 = lean_string_append(x_21, x_22);
x_24 = l_Nat_reprFast(x_11);
x_25 = lean_string_append(x_23, x_24);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
x_27 = lean_string_append(x_25, x_26);
x_28 = l_Nat_reprFast(x_10);
x_29 = lean_string_append(x_27, x_28);
lean_dec_ref(x_28);
x_30 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
x_31 = lean_string_append(x_29, x_30);
x_32 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
x_33 = lean_string_append(x_31, x_32);
x_34 = lean_string_append(x_33, x_22);
x_35 = l_Nat_reprFast(x_13);
x_36 = lean_string_append(x_34, x_35);
lean_dec_ref(x_35);
x_37 = lean_string_append(x_36, x_26);
x_38 = l_Nat_reprFast(x_12);
x_39 = lean_string_append(x_37, x_38);
lean_dec_ref(x_38);
x_40 = lean_string_append(x_39, x_30);
x_41 = lean_string_append(x_40, x_30);
x_42 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_string_append(x_43, x_9);
lean_dec_ref(x_9);
x_45 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_46 = lean_string_append(x_44, x_45);
x_47 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
x_48 = lean_string_append(x_46, x_47);
x_49 = lean_string_append(x_48, x_20);
x_50 = lean_string_append(x_49, x_22);
x_51 = l_Nat_reprFast(x_15);
x_52 = lean_string_append(x_50, x_51);
lean_dec_ref(x_51);
x_53 = lean_string_append(x_52, x_26);
x_54 = l_Nat_reprFast(x_14);
x_55 = lean_string_append(x_53, x_54);
lean_dec_ref(x_54);
x_56 = lean_string_append(x_55, x_30);
x_57 = lean_string_append(x_56, x_32);
x_58 = lean_string_append(x_57, x_22);
x_59 = l_Nat_reprFast(x_17);
x_60 = lean_string_append(x_58, x_59);
lean_dec_ref(x_59);
x_61 = lean_string_append(x_60, x_26);
x_62 = l_Nat_reprFast(x_16);
x_63 = lean_string_append(x_61, x_62);
lean_dec_ref(x_62);
x_64 = lean_string_append(x_63, x_30);
x_65 = lean_string_append(x_64, x_30);
x_66 = lean_string_append(x_65, x_30);
return x_66;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Nat_reprFast(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_unsigned_to_nat(1u);
x_11 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0;
x_12 = lean_string_append(x_1, x_11);
x_13 = lean_nat_sub(x_4, x_6);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
x_7 = x_12;
goto block_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
x_16 = lean_string_append(x_12, x_15);
x_7 = x_16;
goto block_10;
}
block_10:
{
lean_object* x_8; 
x_8 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
x_1 = x_7;
x_3 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_3, x_1);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_string_utf8_next_fast(x_2, x_3);
x_9 = lean_string_utf8_get_fast(x_2, x_3);
x_10 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(x_4, x_9);
x_11 = lean_apply_4(x_6, x_8, x_10, lean_box(0), lean_box(0));
return x_11;
}
else
{
lean_dec_ref(x_6);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_eq(x_3, x_1);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_string_utf8_next_fast(x_2, x_3);
x_9 = lean_string_utf8_get_fast(x_2, x_3);
x_10 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(x_4, x_9);
x_11 = lean_apply_4(x_6, x_8, x_10, lean_box(0), lean_box(0));
return x_11;
}
else
{
lean_dec_ref(x_6);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_32; lean_object* x_36; lean_object* x_40; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_94; lean_object* x_117; lean_object* x_134; lean_object* x_203; lean_object* x_214; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_239; lean_object* x_248; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 7);
lean_inc(x_18);
lean_dec_ref(x_2);
x_265 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7));
x_266 = lean_string_append(x_1, x_265);
x_267 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_268 = lean_string_append(x_266, x_267);
x_269 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_11);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_string_append(x_268, x_11);
lean_dec_ref(x_11);
x_271 = lean_string_append(x_270, x_267);
x_248 = x_271;
goto block_264;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_272 = lean_unsigned_to_nat(0u);
x_273 = lean_string_utf8_byte_size(x_11);
lean_inc_ref(x_11);
x_274 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed), 6, 2);
lean_closure_set(x_274, 0, x_273);
lean_closure_set(x_274, 1, x_11);
x_275 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_275, 0, x_11);
lean_ctor_set(x_275, 1, x_272);
lean_ctor_set(x_275, 2, x_273);
x_276 = l_String_Slice_positions(x_275);
lean_dec_ref(x_275);
x_277 = l_WellFounded_opaqueFix_u2083___redArg(x_274, x_276, x_268, lean_box(0));
x_278 = lean_string_append(x_277, x_267);
x_248 = x_278;
goto block_264;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
x_9 = lean_string_append(x_7, x_8);
x_3 = x_9;
goto block_6;
}
block_31:
{
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_20);
x_3 = x_19;
goto block_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0));
x_25 = lean_string_append(x_19, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_dec_eq(x_22, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(x_25, x_20, x_21);
lean_dec(x_20);
x_7 = x_28;
goto block_10;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_20);
x_29 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0;
x_30 = lean_string_append(x_25, x_29);
x_7 = x_30;
goto block_10;
}
}
}
else
{
lean_dec(x_18);
x_3 = x_19;
goto block_6;
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
x_34 = lean_string_append(x_32, x_33);
x_19 = x_34;
goto block_31;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_38 = lean_string_append(x_36, x_37);
x_32 = x_38;
goto block_35;
}
block_43:
{
lean_object* x_41; lean_object* x_42; 
x_41 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_42 = lean_string_append(x_40, x_41);
x_32 = x_42;
goto block_35;
}
block_75:
{
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_string_append(x_46, x_44);
lean_dec_ref(x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2));
x_51 = lean_string_append(x_48, x_50);
x_52 = 1;
x_53 = l_Lean_Name_toString(x_49, x_52);
x_54 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_string_append(x_51, x_53);
lean_dec_ref(x_53);
x_40 = x_55;
goto block_43;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_string_utf8_byte_size(x_53);
lean_inc_ref(x_53);
x_58 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(x_58, 0, x_57);
lean_closure_set(x_58, 1, x_53);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_56);
lean_ctor_set(x_59, 2, x_57);
x_60 = l_String_Slice_positions(x_59);
lean_dec_ref(x_59);
x_61 = l_WellFounded_opaqueFix_u2083___redArg(x_58, x_60, x_51, lean_box(0));
x_40 = x_61;
goto block_43;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_47, 0);
lean_inc(x_62);
lean_dec_ref(x_47);
x_63 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
x_64 = lean_string_append(x_48, x_63);
x_65 = 1;
x_66 = l_Lean_Name_toString(x_62, x_65);
x_67 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_string_append(x_64, x_66);
lean_dec_ref(x_66);
x_36 = x_68;
goto block_39;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_string_utf8_byte_size(x_66);
lean_inc_ref(x_66);
x_71 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(x_71, 0, x_70);
lean_closure_set(x_71, 1, x_66);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_70);
x_73 = l_String_Slice_positions(x_72);
lean_dec_ref(x_72);
x_74 = l_WellFounded_opaqueFix_u2083___redArg(x_71, x_73, x_64, lean_box(0));
x_36 = x_74;
goto block_39;
}
}
}
else
{
lean_dec(x_45);
lean_dec_ref(x_44);
x_32 = x_46;
goto block_35;
}
}
block_93:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 1);
lean_inc(x_81);
lean_dec_ref(x_76);
x_82 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
x_83 = lean_string_append(x_79, x_82);
x_84 = l_Nat_reprFast(x_80);
x_85 = lean_string_append(x_83, x_84);
lean_dec_ref(x_84);
x_86 = lean_string_append(x_85, x_82);
x_87 = l_Nat_reprFast(x_81);
x_88 = lean_string_append(x_86, x_87);
lean_dec_ref(x_87);
if (lean_obj_tag(x_77) == 1)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_77, 0);
lean_inc(x_89);
lean_dec_ref(x_77);
x_90 = lean_string_append(x_88, x_82);
x_91 = l_Nat_reprFast(x_89);
x_92 = lean_string_append(x_90, x_91);
lean_dec_ref(x_91);
x_44 = x_82;
x_45 = x_78;
x_46 = x_92;
goto block_75;
}
else
{
lean_dec(x_77);
x_44 = x_82;
x_45 = x_78;
x_46 = x_88;
goto block_75;
}
}
block_116:
{
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_95 = lean_ctor_get(x_17, 0);
lean_inc(x_95);
lean_dec_ref(x_17);
x_96 = lean_ctor_get(x_95, 0);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_95, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 3);
lean_inc(x_99);
lean_dec(x_95);
x_100 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1));
x_101 = lean_string_append(x_94, x_100);
x_102 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
x_103 = lean_string_append(x_101, x_102);
x_104 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_105 = lean_string_append(x_103, x_104);
x_106 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_96);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_string_append(x_105, x_96);
lean_dec_ref(x_96);
x_108 = lean_string_append(x_107, x_104);
x_76 = x_97;
x_77 = x_98;
x_78 = x_99;
x_79 = x_108;
goto block_93;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_string_utf8_byte_size(x_96);
lean_inc_ref(x_96);
x_111 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed), 6, 2);
lean_closure_set(x_111, 0, x_110);
lean_closure_set(x_111, 1, x_96);
x_112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_112, 0, x_96);
lean_ctor_set(x_112, 1, x_109);
lean_ctor_set(x_112, 2, x_110);
x_113 = l_String_Slice_positions(x_112);
lean_dec_ref(x_112);
x_114 = l_WellFounded_opaqueFix_u2083___redArg(x_111, x_113, x_105, lean_box(0));
x_115 = lean_string_append(x_114, x_104);
x_76 = x_97;
x_77 = x_98;
x_78 = x_99;
x_79 = x_115;
goto block_93;
}
}
else
{
lean_dec(x_17);
x_19 = x_94;
goto block_31;
}
}
block_133:
{
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_118 = lean_ctor_get(x_16, 0);
lean_inc(x_118);
lean_dec_ref(x_16);
x_119 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2));
x_120 = lean_string_append(x_117, x_119);
x_121 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_122 = lean_string_append(x_120, x_121);
x_123 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_118);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_string_append(x_122, x_118);
lean_dec(x_118);
x_125 = lean_string_append(x_124, x_121);
x_94 = x_125;
goto block_116;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_unsigned_to_nat(0u);
x_127 = lean_string_utf8_byte_size(x_118);
lean_inc(x_118);
x_128 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed), 6, 2);
lean_closure_set(x_128, 0, x_127);
lean_closure_set(x_128, 1, x_118);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_118);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_127);
x_130 = l_String_Slice_positions(x_129);
lean_dec_ref(x_129);
x_131 = l_WellFounded_opaqueFix_u2083___redArg(x_128, x_130, x_122, lean_box(0));
x_132 = lean_string_append(x_131, x_121);
x_94 = x_132;
goto block_116;
}
}
else
{
lean_dec(x_16);
x_94 = x_117;
goto block_116;
}
}
block_202:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_135 = lean_ctor_get(x_15, 0);
lean_inc(x_135);
lean_dec_ref(x_15);
x_136 = lean_ctor_get(x_135, 1);
x_137 = lean_ctor_get(x_136, 1);
lean_inc_ref(x_137);
x_138 = lean_ctor_get(x_136, 0);
lean_inc_ref(x_138);
x_139 = lean_ctor_get(x_135, 2);
x_140 = lean_ctor_get(x_139, 1);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_139, 0);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_135, 0);
lean_inc_ref(x_142);
lean_dec(x_135);
x_143 = lean_ctor_get(x_137, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_137, 1);
lean_inc(x_144);
lean_dec_ref(x_137);
x_145 = lean_ctor_get(x_138, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_138, 1);
lean_inc(x_146);
lean_dec_ref(x_138);
x_147 = lean_ctor_get(x_140, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_140, 1);
lean_inc(x_148);
lean_dec_ref(x_140);
x_149 = lean_ctor_get(x_141, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_141, 1);
lean_inc(x_150);
lean_dec_ref(x_141);
x_151 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3));
x_152 = lean_string_append(x_134, x_151);
x_153 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
x_154 = lean_string_append(x_152, x_153);
x_155 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
x_156 = lean_string_append(x_154, x_155);
x_157 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
x_158 = lean_string_append(x_156, x_157);
x_159 = l_Nat_reprFast(x_144);
x_160 = lean_string_append(x_158, x_159);
lean_dec_ref(x_159);
x_161 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
x_162 = lean_string_append(x_160, x_161);
x_163 = l_Nat_reprFast(x_143);
x_164 = lean_string_append(x_162, x_163);
lean_dec_ref(x_163);
x_165 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
x_166 = lean_string_append(x_164, x_165);
x_167 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
x_168 = lean_string_append(x_166, x_167);
x_169 = lean_string_append(x_168, x_157);
x_170 = l_Nat_reprFast(x_146);
x_171 = lean_string_append(x_169, x_170);
lean_dec_ref(x_170);
x_172 = lean_string_append(x_171, x_161);
x_173 = l_Nat_reprFast(x_145);
x_174 = lean_string_append(x_172, x_173);
lean_dec_ref(x_173);
x_175 = lean_string_append(x_174, x_165);
x_176 = lean_string_append(x_175, x_165);
x_177 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
x_178 = lean_string_append(x_176, x_177);
x_179 = lean_string_append(x_178, x_142);
lean_dec_ref(x_142);
x_180 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_181 = lean_string_append(x_179, x_180);
x_182 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
x_183 = lean_string_append(x_181, x_182);
x_184 = lean_string_append(x_183, x_155);
x_185 = lean_string_append(x_184, x_157);
x_186 = l_Nat_reprFast(x_148);
x_187 = lean_string_append(x_185, x_186);
lean_dec_ref(x_186);
x_188 = lean_string_append(x_187, x_161);
x_189 = l_Nat_reprFast(x_147);
x_190 = lean_string_append(x_188, x_189);
lean_dec_ref(x_189);
x_191 = lean_string_append(x_190, x_165);
x_192 = lean_string_append(x_191, x_167);
x_193 = lean_string_append(x_192, x_157);
x_194 = l_Nat_reprFast(x_150);
x_195 = lean_string_append(x_193, x_194);
lean_dec_ref(x_194);
x_196 = lean_string_append(x_195, x_161);
x_197 = l_Nat_reprFast(x_149);
x_198 = lean_string_append(x_196, x_197);
lean_dec_ref(x_197);
x_199 = lean_string_append(x_198, x_165);
x_200 = lean_string_append(x_199, x_165);
x_201 = lean_string_append(x_200, x_165);
x_117 = x_201;
goto block_133;
}
else
{
lean_dec(x_15);
x_117 = x_134;
goto block_133;
}
}
block_213:
{
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_204 = lean_ctor_get(x_14, 0);
lean_inc(x_204);
lean_dec_ref(x_14);
x_205 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4));
x_206 = lean_string_append(x_203, x_205);
x_207 = lean_unbox(x_204);
lean_dec(x_204);
x_208 = l_Lean_Lsp_CompletionItemKind_ctorIdx(x_207);
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_nat_add(x_208, x_209);
lean_dec(x_208);
x_211 = l_Nat_reprFast(x_210);
x_212 = lean_string_append(x_206, x_211);
lean_dec_ref(x_211);
x_134 = x_212;
goto block_202;
}
else
{
lean_dec(x_14);
x_134 = x_203;
goto block_202;
}
}
block_217:
{
lean_object* x_215; lean_object* x_216; 
x_215 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
x_216 = lean_string_append(x_214, x_215);
x_203 = x_216;
goto block_213;
}
block_238:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_221 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
x_222 = lean_string_append(x_219, x_221);
x_223 = lean_string_append(x_222, x_220);
lean_dec_ref(x_220);
x_224 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
x_225 = lean_string_append(x_223, x_224);
x_226 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_227 = lean_string_append(x_225, x_226);
x_228 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_218);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_string_append(x_227, x_218);
lean_dec_ref(x_218);
x_230 = lean_string_append(x_229, x_226);
x_214 = x_230;
goto block_217;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_231 = lean_unsigned_to_nat(0u);
x_232 = lean_string_utf8_byte_size(x_218);
lean_inc_ref(x_218);
x_233 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed), 6, 2);
lean_closure_set(x_233, 0, x_232);
lean_closure_set(x_233, 1, x_218);
x_234 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_234, 0, x_218);
lean_ctor_set(x_234, 1, x_231);
lean_ctor_set(x_234, 2, x_232);
x_235 = l_String_Slice_positions(x_234);
lean_dec_ref(x_234);
x_236 = l_WellFounded_opaqueFix_u2083___redArg(x_233, x_235, x_227, lean_box(0));
x_237 = lean_string_append(x_236, x_226);
x_214 = x_237;
goto block_217;
}
}
block_247:
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_240 = lean_ctor_get(x_13, 0);
lean_inc(x_240);
lean_dec_ref(x_13);
x_241 = lean_ctor_get_uint8(x_240, sizeof(void*)*1);
x_242 = lean_ctor_get(x_240, 0);
lean_inc_ref(x_242);
lean_dec(x_240);
x_243 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5));
x_244 = lean_string_append(x_239, x_243);
if (x_241 == 0)
{
lean_object* x_245; 
x_245 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
x_218 = x_242;
x_219 = x_244;
x_220 = x_245;
goto block_238;
}
else
{
lean_object* x_246; 
x_246 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
x_218 = x_242;
x_219 = x_244;
x_220 = x_246;
goto block_238;
}
}
else
{
lean_dec(x_13);
x_203 = x_239;
goto block_213;
}
}
block_264:
{
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_249 = lean_ctor_get(x_12, 0);
lean_inc(x_249);
lean_dec_ref(x_12);
x_250 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6));
x_251 = lean_string_append(x_248, x_250);
x_252 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_253 = lean_string_append(x_251, x_252);
x_254 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_249);
if (x_254 == 0)
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_string_append(x_253, x_249);
lean_dec(x_249);
x_256 = lean_string_append(x_255, x_252);
x_239 = x_256;
goto block_247;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_257 = lean_unsigned_to_nat(0u);
x_258 = lean_string_utf8_byte_size(x_249);
lean_inc(x_249);
x_259 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed), 6, 2);
lean_closure_set(x_259, 0, x_258);
lean_closure_set(x_259, 1, x_249);
x_260 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_260, 0, x_249);
lean_ctor_set(x_260, 1, x_257);
lean_ctor_set(x_260, 2, x_258);
x_261 = l_String_Slice_positions(x_260);
lean_dec_ref(x_260);
x_262 = l_WellFounded_opaqueFix_u2083___redArg(x_259, x_261, x_253, lean_box(0));
x_263 = lean_string_append(x_262, x_252);
x_239 = x_263;
goto block_247;
}
}
else
{
lean_dec(x_12);
x_239 = x_248;
goto block_247;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; lean_object* x_11; 
x_9 = lean_string_utf8_next_fast(x_2, x_3);
x_10 = lean_string_utf8_get_fast(x_2, x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(x_4, x_10);
x_3 = x_9;
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_19; uint8_t x_23; 
x_9 = lean_array_get_size(x_2);
x_23 = lean_nat_dec_lt(x_3, x_9);
if (x_23 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_39; lean_object* x_43; lean_object* x_47; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_97; lean_object* x_120; lean_object* x_137; lean_object* x_207; lean_object* x_219; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_243; lean_object* x_253; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_24 = lean_array_fget_borrowed(x_2, x_3);
x_270 = lean_ctor_get(x_24, 0);
x_271 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7));
x_272 = lean_string_append(x_1, x_271);
x_273 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_274 = lean_string_append(x_272, x_273);
x_275 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_270);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_string_append(x_274, x_270);
x_277 = lean_string_append(x_276, x_273);
x_253 = x_277;
goto block_269;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_278 = lean_unsigned_to_nat(0u);
x_279 = lean_string_utf8_byte_size(x_270);
lean_inc_ref(x_270);
x_280 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_280, 0, x_270);
lean_ctor_set(x_280, 1, x_278);
lean_ctor_set(x_280, 2, x_279);
x_281 = l_String_Slice_positions(x_280);
x_282 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(x_280, x_270, x_281, x_274);
lean_dec_ref(x_280);
x_283 = lean_string_append(x_282, x_273);
x_253 = x_283;
goto block_269;
}
block_38:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 7);
if (lean_obj_tag(x_26) == 1)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_26, 0);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get_size(x_27);
x_30 = lean_nat_dec_lt(x_28, x_29);
if (x_30 == 0)
{
x_10 = x_25;
goto block_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0));
x_32 = lean_string_append(x_25, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_dec_eq(x_29, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(x_32, x_27, x_28);
x_19 = x_35;
goto block_22;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0;
x_37 = lean_string_append(x_32, x_36);
x_19 = x_37;
goto block_22;
}
}
}
else
{
x_10 = x_25;
goto block_18;
}
}
block_42:
{
lean_object* x_40; lean_object* x_41; 
x_40 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
x_41 = lean_string_append(x_39, x_40);
x_25 = x_41;
goto block_38;
}
block_46:
{
lean_object* x_44; lean_object* x_45; 
x_44 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_45 = lean_string_append(x_43, x_44);
x_39 = x_45;
goto block_42;
}
block_50:
{
lean_object* x_48; lean_object* x_49; 
x_48 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_49 = lean_string_append(x_47, x_48);
x_39 = x_49;
goto block_42;
}
block_78:
{
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_string_append(x_53, x_51);
lean_dec_ref(x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2));
x_58 = lean_string_append(x_55, x_57);
x_59 = l_Lean_Name_toString(x_56, x_23);
x_60 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_string_append(x_58, x_59);
lean_dec_ref(x_59);
x_43 = x_61;
goto block_46;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_string_utf8_byte_size(x_59);
lean_inc_ref(x_59);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_63);
x_65 = l_String_Slice_positions(x_64);
x_66 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(x_64, x_59, x_65, x_58);
lean_dec_ref(x_59);
lean_dec_ref(x_64);
x_43 = x_66;
goto block_46;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_54, 0);
lean_inc(x_67);
lean_dec_ref(x_54);
x_68 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
x_69 = lean_string_append(x_55, x_68);
x_70 = l_Lean_Name_toString(x_67, x_23);
x_71 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_string_append(x_69, x_70);
lean_dec_ref(x_70);
x_47 = x_72;
goto block_50;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_string_utf8_byte_size(x_70);
lean_inc_ref(x_70);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_73);
lean_ctor_set(x_75, 2, x_74);
x_76 = l_String_Slice_positions(x_75);
x_77 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(x_75, x_70, x_76, x_69);
lean_dec_ref(x_70);
lean_dec_ref(x_75);
x_47 = x_77;
goto block_50;
}
}
}
else
{
lean_dec(x_52);
lean_dec_ref(x_51);
x_39 = x_53;
goto block_42;
}
}
block_96:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_83 = lean_ctor_get(x_79, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
lean_dec_ref(x_79);
x_85 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
x_86 = lean_string_append(x_82, x_85);
x_87 = l_Nat_reprFast(x_83);
x_88 = lean_string_append(x_86, x_87);
lean_dec_ref(x_87);
x_89 = lean_string_append(x_88, x_85);
x_90 = l_Nat_reprFast(x_84);
x_91 = lean_string_append(x_89, x_90);
lean_dec_ref(x_90);
if (lean_obj_tag(x_80) == 1)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_80, 0);
lean_inc(x_92);
lean_dec_ref(x_80);
x_93 = lean_string_append(x_91, x_85);
x_94 = l_Nat_reprFast(x_92);
x_95 = lean_string_append(x_93, x_94);
lean_dec_ref(x_94);
x_51 = x_85;
x_52 = x_81;
x_53 = x_95;
goto block_78;
}
else
{
lean_dec(x_80);
x_51 = x_85;
x_52 = x_81;
x_53 = x_91;
goto block_78;
}
}
block_119:
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_24, 6);
if (lean_obj_tag(x_98) == 1)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_99 = lean_ctor_get(x_98, 0);
x_100 = lean_ctor_get(x_99, 0);
x_101 = lean_ctor_get(x_99, 1);
x_102 = lean_ctor_get(x_99, 2);
x_103 = lean_ctor_get(x_99, 3);
x_104 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1));
x_105 = lean_string_append(x_97, x_104);
x_106 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
x_107 = lean_string_append(x_105, x_106);
x_108 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_109 = lean_string_append(x_107, x_108);
x_110 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_100);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_string_append(x_109, x_100);
x_112 = lean_string_append(x_111, x_108);
lean_inc(x_103);
lean_inc(x_102);
lean_inc_ref(x_101);
x_79 = x_101;
x_80 = x_102;
x_81 = x_103;
x_82 = x_112;
goto block_96;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_113 = lean_unsigned_to_nat(0u);
x_114 = lean_string_utf8_byte_size(x_100);
lean_inc_ref(x_100);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_113);
lean_ctor_set(x_115, 2, x_114);
x_116 = l_String_Slice_positions(x_115);
x_117 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(x_115, x_100, x_116, x_109);
lean_dec_ref(x_115);
x_118 = lean_string_append(x_117, x_108);
lean_inc(x_103);
lean_inc(x_102);
lean_inc_ref(x_101);
x_79 = x_101;
x_80 = x_102;
x_81 = x_103;
x_82 = x_118;
goto block_96;
}
}
else
{
x_25 = x_97;
goto block_38;
}
}
block_136:
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_24, 5);
if (lean_obj_tag(x_121) == 1)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_121, 0);
x_123 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2));
x_124 = lean_string_append(x_120, x_123);
x_125 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_126 = lean_string_append(x_124, x_125);
x_127 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_122);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_string_append(x_126, x_122);
x_129 = lean_string_append(x_128, x_125);
x_97 = x_129;
goto block_119;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_string_utf8_byte_size(x_122);
lean_inc(x_122);
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_122);
lean_ctor_set(x_132, 1, x_130);
lean_ctor_set(x_132, 2, x_131);
x_133 = l_String_Slice_positions(x_132);
x_134 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(x_132, x_122, x_133, x_126);
lean_dec_ref(x_132);
x_135 = lean_string_append(x_134, x_125);
x_97 = x_135;
goto block_119;
}
}
else
{
x_97 = x_120;
goto block_119;
}
}
block_206:
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_24, 4);
if (lean_obj_tag(x_138) == 1)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_139 = lean_ctor_get(x_138, 0);
x_140 = lean_ctor_get(x_139, 1);
x_141 = lean_ctor_get(x_140, 1);
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_ctor_get(x_139, 2);
x_144 = lean_ctor_get(x_143, 1);
x_145 = lean_ctor_get(x_143, 0);
x_146 = lean_ctor_get(x_139, 0);
x_147 = lean_ctor_get(x_141, 0);
x_148 = lean_ctor_get(x_141, 1);
x_149 = lean_ctor_get(x_142, 0);
x_150 = lean_ctor_get(x_142, 1);
x_151 = lean_ctor_get(x_144, 0);
x_152 = lean_ctor_get(x_144, 1);
x_153 = lean_ctor_get(x_145, 0);
x_154 = lean_ctor_get(x_145, 1);
x_155 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3));
x_156 = lean_string_append(x_137, x_155);
x_157 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
x_158 = lean_string_append(x_156, x_157);
x_159 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
x_160 = lean_string_append(x_158, x_159);
x_161 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
x_162 = lean_string_append(x_160, x_161);
lean_inc(x_148);
x_163 = l_Nat_reprFast(x_148);
x_164 = lean_string_append(x_162, x_163);
lean_dec_ref(x_163);
x_165 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
x_166 = lean_string_append(x_164, x_165);
lean_inc(x_147);
x_167 = l_Nat_reprFast(x_147);
x_168 = lean_string_append(x_166, x_167);
lean_dec_ref(x_167);
x_169 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
x_170 = lean_string_append(x_168, x_169);
x_171 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
x_172 = lean_string_append(x_170, x_171);
x_173 = lean_string_append(x_172, x_161);
lean_inc(x_150);
x_174 = l_Nat_reprFast(x_150);
x_175 = lean_string_append(x_173, x_174);
lean_dec_ref(x_174);
x_176 = lean_string_append(x_175, x_165);
lean_inc(x_149);
x_177 = l_Nat_reprFast(x_149);
x_178 = lean_string_append(x_176, x_177);
lean_dec_ref(x_177);
x_179 = lean_string_append(x_178, x_169);
x_180 = lean_string_append(x_179, x_169);
x_181 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
x_182 = lean_string_append(x_180, x_181);
x_183 = lean_string_append(x_182, x_146);
x_184 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_185 = lean_string_append(x_183, x_184);
x_186 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
x_187 = lean_string_append(x_185, x_186);
x_188 = lean_string_append(x_187, x_159);
x_189 = lean_string_append(x_188, x_161);
lean_inc(x_152);
x_190 = l_Nat_reprFast(x_152);
x_191 = lean_string_append(x_189, x_190);
lean_dec_ref(x_190);
x_192 = lean_string_append(x_191, x_165);
lean_inc(x_151);
x_193 = l_Nat_reprFast(x_151);
x_194 = lean_string_append(x_192, x_193);
lean_dec_ref(x_193);
x_195 = lean_string_append(x_194, x_169);
x_196 = lean_string_append(x_195, x_171);
x_197 = lean_string_append(x_196, x_161);
lean_inc(x_154);
x_198 = l_Nat_reprFast(x_154);
x_199 = lean_string_append(x_197, x_198);
lean_dec_ref(x_198);
x_200 = lean_string_append(x_199, x_165);
lean_inc(x_153);
x_201 = l_Nat_reprFast(x_153);
x_202 = lean_string_append(x_200, x_201);
lean_dec_ref(x_201);
x_203 = lean_string_append(x_202, x_169);
x_204 = lean_string_append(x_203, x_169);
x_205 = lean_string_append(x_204, x_169);
x_120 = x_205;
goto block_136;
}
else
{
x_120 = x_137;
goto block_136;
}
}
block_218:
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_24, 3);
if (lean_obj_tag(x_208) == 1)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_209 = lean_ctor_get(x_208, 0);
x_210 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4));
x_211 = lean_string_append(x_207, x_210);
x_212 = lean_unbox(x_209);
x_213 = l_Lean_Lsp_CompletionItemKind_ctorIdx(x_212);
x_214 = lean_unsigned_to_nat(1u);
x_215 = lean_nat_add(x_213, x_214);
lean_dec(x_213);
x_216 = l_Nat_reprFast(x_215);
x_217 = lean_string_append(x_211, x_216);
lean_dec_ref(x_216);
x_137 = x_217;
goto block_206;
}
else
{
x_137 = x_207;
goto block_206;
}
}
block_222:
{
lean_object* x_220; lean_object* x_221; 
x_220 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
x_221 = lean_string_append(x_219, x_220);
x_207 = x_221;
goto block_218;
}
block_242:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_226 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
x_227 = lean_string_append(x_223, x_226);
x_228 = lean_string_append(x_227, x_225);
lean_dec_ref(x_225);
x_229 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
x_230 = lean_string_append(x_228, x_229);
x_231 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_232 = lean_string_append(x_230, x_231);
x_233 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_224);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_string_append(x_232, x_224);
lean_dec_ref(x_224);
x_235 = lean_string_append(x_234, x_231);
x_219 = x_235;
goto block_222;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_unsigned_to_nat(0u);
x_237 = lean_string_utf8_byte_size(x_224);
lean_inc_ref(x_224);
x_238 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_238, 0, x_224);
lean_ctor_set(x_238, 1, x_236);
lean_ctor_set(x_238, 2, x_237);
x_239 = l_String_Slice_positions(x_238);
x_240 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(x_238, x_224, x_239, x_232);
lean_dec_ref(x_224);
lean_dec_ref(x_238);
x_241 = lean_string_append(x_240, x_231);
x_219 = x_241;
goto block_222;
}
}
block_252:
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_24, 2);
if (lean_obj_tag(x_244) == 1)
{
lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_245 = lean_ctor_get(x_244, 0);
x_246 = lean_ctor_get_uint8(x_245, sizeof(void*)*1);
x_247 = lean_ctor_get(x_245, 0);
x_248 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5));
x_249 = lean_string_append(x_243, x_248);
if (x_246 == 0)
{
lean_object* x_250; 
x_250 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
lean_inc_ref(x_247);
x_223 = x_249;
x_224 = x_247;
x_225 = x_250;
goto block_242;
}
else
{
lean_object* x_251; 
x_251 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
lean_inc_ref(x_247);
x_223 = x_249;
x_224 = x_247;
x_225 = x_251;
goto block_242;
}
}
else
{
x_207 = x_243;
goto block_218;
}
}
block_269:
{
lean_object* x_254; 
x_254 = lean_ctor_get(x_24, 1);
if (lean_obj_tag(x_254) == 1)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_255 = lean_ctor_get(x_254, 0);
x_256 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6));
x_257 = lean_string_append(x_253, x_256);
x_258 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
x_259 = lean_string_append(x_257, x_258);
x_260 = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(x_255);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_string_append(x_259, x_255);
x_262 = lean_string_append(x_261, x_258);
x_243 = x_262;
goto block_252;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_unsigned_to_nat(0u);
x_264 = lean_string_utf8_byte_size(x_255);
lean_inc(x_255);
x_265 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_265, 0, x_255);
lean_ctor_set(x_265, 1, x_263);
lean_ctor_set(x_265, 2, x_264);
x_266 = l_String_Slice_positions(x_265);
x_267 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(x_265, x_255, x_266, x_259);
lean_dec_ref(x_265);
x_268 = lean_string_append(x_267, x_258);
x_243 = x_268;
goto block_252;
}
}
else
{
x_243 = x_253;
goto block_252;
}
}
}
block_8:
{
lean_object* x_6; 
x_6 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_1 = x_5;
x_3 = x_6;
goto _start;
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_9, x_13);
x_15 = lean_nat_dec_lt(x_3, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
x_4 = x_13;
x_5 = x_12;
goto block_8;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
x_17 = lean_string_append(x_12, x_16);
x_4 = x_13;
x_5 = x_17;
goto block_8;
}
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
x_21 = lean_string_append(x_19, x_20);
x_10 = x_21;
goto block_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_3 = lean_ctor_get(x_1, 0);
x_4 = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0));
if (x_2 == 0)
{
lean_object* x_14; 
x_14 = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3));
x_5 = x_14;
goto block_13;
}
else
{
lean_object* x_15; 
x_15 = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4));
x_5 = x_15;
goto block_13;
}
block_13:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_string_append(x_4, x_5);
lean_dec_ref(x_5);
x_7 = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1));
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(x_8, x_3, x_9);
x_11 = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2));
x_12 = lean_string_append(x_10, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Lsp_ResolvableCompletionList_compressFast(x_1);
lean_dec_ref(x_1);
return x_2;
}
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
l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0 = _init_l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

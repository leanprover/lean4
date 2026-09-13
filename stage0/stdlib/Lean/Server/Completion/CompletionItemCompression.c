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
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
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
static const lean_string_object l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0 = (const lean_object*)&l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0_value;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v_decide_7_; 
v_decide_7_ = lean_nat_dec_eq(v_it_3_, v___x_1_);
if (v_decide_7_ == 0)
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
uint8_t v_decide_25_; 
v_decide_25_ = lean_nat_dec_eq(v_it_21_, v___x_19_);
if (v_decide_25_ == 0)
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
lean_object* v_acc_46_; lean_object* v___y_50_; lean_object* v___y_54_; lean_object* v_uri_57_; lean_object* v_pos_58_; lean_object* v_cPos_x3f_59_; lean_object* v_id_x3f_60_; lean_object* v___y_62_; lean_object* v_acc_63_; lean_object* v___y_89_; lean_object* v___x_103_; lean_object* v_acc_104_; lean_object* v___x_105_; lean_object* v_acc_106_; uint8_t v___x_107_; 
v_uri_57_ = lean_ctor_get(v_data_44_, 0);
lean_inc_ref(v_uri_57_);
v_pos_58_ = lean_ctor_get(v_data_44_, 1);
lean_inc_ref(v_pos_58_);
v_cPos_x3f_59_ = lean_ctor_get(v_data_44_, 2);
lean_inc(v_cPos_x3f_59_);
v_id_x3f_60_ = lean_ctor_get(v_data_44_, 3);
lean_inc(v_id_x3f_60_);
lean_dec_ref(v_data_44_);
v___x_103_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
v_acc_104_ = lean_string_append(v_acc_43_, v___x_103_);
v___x_105_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_106_ = lean_string_append(v_acc_104_, v___x_105_);
v___x_107_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_57_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_string_append(v_acc_106_, v_uri_57_);
lean_dec_ref(v_uri_57_);
v___x_109_ = lean_string_append(v___x_108_, v___x_105_);
v___y_89_ = v___x_109_;
goto v___jp_88_;
}
else
{
lean_object* v___x_110_; lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_110_ = lean_string_utf8_byte_size(v_uri_57_);
v___f_111_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed), 6, 2);
lean_closure_set(v___f_111_, 0, v___x_110_);
lean_closure_set(v___f_111_, 1, v_uri_57_);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_111_, v___x_112_, v_acc_106_, lean_box(0));
v___x_114_ = lean_string_append(v___x_113_, v___x_105_);
v___y_89_ = v___x_114_;
goto v___jp_88_;
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
lean_dec_ref_known(v_id_x3f_60_, 1);
v_acc_65_ = lean_string_append(v_acc_63_, v___y_62_);
if (lean_obj_tag(v_val_64_) == 0)
{
lean_object* v_declName_66_; lean_object* v___x_67_; lean_object* v_acc_68_; uint8_t v___x_69_; lean_object* v___x_70_; uint8_t v___x_71_; 
v_declName_66_ = lean_ctor_get(v_val_64_, 0);
lean_inc(v_declName_66_);
lean_dec_ref_known(v_val_64_, 1);
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
lean_object* v___x_73_; lean_object* v___f_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_string_utf8_byte_size(v___x_70_);
v___f_74_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_74_, 0, v___x_73_);
lean_closure_set(v___f_74_, 1, v___x_70_);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_74_, v___x_75_, v_acc_68_, lean_box(0));
v___y_50_ = v___x_76_;
goto v___jp_49_;
}
}
else
{
lean_object* v_id_77_; lean_object* v___x_78_; lean_object* v_acc_79_; uint8_t v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v_id_77_ = lean_ctor_get(v_val_64_, 0);
lean_inc(v_id_77_);
lean_dec_ref_known(v_val_64_, 1);
v___x_78_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
v_acc_79_ = lean_string_append(v_acc_65_, v___x_78_);
v___x_80_ = 1;
v___x_81_ = l_Lean_Name_toString(v_id_77_, v___x_80_);
v___x_82_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_string_append(v_acc_79_, v___x_81_);
lean_dec_ref(v___x_81_);
v___y_54_ = v___x_83_;
goto v___jp_53_;
}
else
{
lean_object* v___x_84_; lean_object* v___f_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_84_ = lean_string_utf8_byte_size(v___x_81_);
v___f_85_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_85_, 0, v___x_84_);
lean_closure_set(v___f_85_, 1, v___x_81_);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_85_, v___x_86_, v_acc_79_, lean_box(0));
v___y_54_ = v___x_87_;
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
v___jp_88_:
{
lean_object* v_line_90_; lean_object* v_character_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v_acc_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_acc_98_; 
v_line_90_ = lean_ctor_get(v_pos_58_, 0);
lean_inc(v_line_90_);
v_character_91_ = lean_ctor_get(v_pos_58_, 1);
lean_inc(v_character_91_);
lean_dec_ref(v_pos_58_);
v___x_92_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_93_ = lean_string_append(v___y_89_, v___x_92_);
v___x_94_ = l_Nat_reprFast(v_line_90_);
v_acc_95_ = lean_string_append(v___x_93_, v___x_94_);
lean_dec_ref(v___x_94_);
v___x_96_ = lean_string_append(v_acc_95_, v___x_92_);
v___x_97_ = l_Nat_reprFast(v_character_91_);
v_acc_98_ = lean_string_append(v___x_96_, v___x_97_);
lean_dec_ref(v___x_97_);
if (lean_obj_tag(v_cPos_x3f_59_) == 1)
{
lean_object* v_val_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v_acc_102_; 
v_val_99_ = lean_ctor_get(v_cPos_x3f_59_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v_cPos_x3f_59_, 1);
v___x_100_ = lean_string_append(v_acc_98_, v___x_92_);
v___x_101_ = l_Nat_reprFast(v_val_99_);
v_acc_102_ = lean_string_append(v___x_100_, v___x_101_);
lean_dec_ref(v___x_101_);
v___y_62_ = v___x_92_;
v_acc_63_ = v_acc_102_;
goto v___jp_61_;
}
else
{
lean_dec(v_cPos_x3f_59_);
v___y_62_ = v___x_92_;
v_acc_63_ = v_acc_98_;
goto v___jp_61_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0(lean_object* v___x_115_, lean_object* v_value_116_, lean_object* v_it_117_, lean_object* v_acc_118_, lean_object* v_hP_119_, lean_object* v_recur_120_){
_start:
{
uint8_t v_decide_121_; 
v_decide_121_ = lean_nat_dec_eq(v_it_117_, v___x_115_);
if (v_decide_121_ == 0)
{
uint32_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_122_ = lean_string_utf8_get_fast(v_value_116_, v_it_117_);
v___x_123_ = lean_string_utf8_next_fast(v_value_116_, v_it_117_);
v___x_124_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_118_, v___x_122_);
v___x_125_ = lean_apply_4(v_recur_120_, v___x_123_, v___x_124_, lean_box(0), lean_box(0));
return v___x_125_;
}
else
{
lean_dec_ref(v_recur_120_);
return v_acc_118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed(lean_object* v___x_126_, lean_object* v_value_127_, lean_object* v_it_128_, lean_object* v_acc_129_, lean_object* v_hP_130_, lean_object* v_recur_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0(v___x_126_, v_value_127_, v_it_128_, v_acc_129_, v_hP_130_, v_recur_131_);
lean_dec(v_it_128_);
lean_dec_ref(v_value_127_);
lean_dec(v___x_126_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast(lean_object* v_acc_138_, lean_object* v_c_139_){
_start:
{
lean_object* v___y_141_; uint8_t v_kind_144_; lean_object* v_value_145_; lean_object* v___y_147_; 
v_kind_144_ = lean_ctor_get_uint8(v_c_139_, sizeof(void*)*1);
v_value_145_ = lean_ctor_get(v_c_139_, 0);
lean_inc_ref(v_value_145_);
lean_dec_ref(v_c_139_);
if (v_kind_144_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
v___y_147_ = v___x_163_;
goto v___jp_146_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
v___y_147_ = v___x_164_;
goto v___jp_146_;
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_143_ = lean_string_append(v___y_141_, v___x_142_);
return v___x_143_;
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v_acc_152_; lean_object* v___x_153_; lean_object* v_acc_154_; uint8_t v___x_155_; 
v___x_148_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
v___x_149_ = lean_string_append(v_acc_138_, v___x_148_);
v___x_150_ = lean_string_append(v___x_149_, v___y_147_);
v___x_151_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
v_acc_152_ = lean_string_append(v___x_150_, v___x_151_);
v___x_153_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_154_ = lean_string_append(v_acc_152_, v___x_153_);
v___x_155_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_145_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_string_append(v_acc_154_, v_value_145_);
lean_dec_ref(v_value_145_);
v___x_157_ = lean_string_append(v___x_156_, v___x_153_);
v___y_141_ = v___x_157_;
goto v___jp_140_;
}
else
{
lean_object* v___x_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_158_ = lean_string_utf8_byte_size(v_value_145_);
v___f_159_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_159_, 0, v___x_158_);
lean_closure_set(v___f_159_, 1, v_value_145_);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_159_, v___x_160_, v_acc_154_, lean_box(0));
v___x_162_ = lean_string_append(v___x_161_, v___x_153_);
v___y_141_ = v___x_162_;
goto v___jp_140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast(lean_object* v_acc_167_, lean_object* v_p_168_){
_start:
{
lean_object* v_line_169_; lean_object* v_character_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_line_169_ = lean_ctor_get(v_p_168_, 0);
lean_inc(v_line_169_);
v_character_170_ = lean_ctor_get(v_p_168_, 1);
lean_inc(v_character_170_);
lean_dec_ref(v_p_168_);
v___x_171_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_172_ = lean_string_append(v_acc_167_, v___x_171_);
v___x_173_ = l_Nat_reprFast(v_character_170_);
v___x_174_ = lean_string_append(v___x_172_, v___x_173_);
lean_dec_ref(v___x_173_);
v___x_175_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_176_ = lean_string_append(v___x_174_, v___x_175_);
v___x_177_ = l_Nat_reprFast(v_line_169_);
v___x_178_ = lean_string_append(v___x_176_, v___x_177_);
lean_dec_ref(v___x_177_);
v___x_179_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_180_ = lean_string_append(v___x_178_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast(lean_object* v_acc_183_, lean_object* v_range_184_){
_start:
{
lean_object* v_end_185_; lean_object* v_start_186_; lean_object* v_line_187_; lean_object* v_character_188_; lean_object* v_line_189_; lean_object* v_character_190_; lean_object* v___x_191_; lean_object* v_acc_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_acc_202_; lean_object* v___x_203_; lean_object* v_acc_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_acc_211_; lean_object* v___x_212_; 
v_end_185_ = lean_ctor_get(v_range_184_, 1);
lean_inc_ref(v_end_185_);
v_start_186_ = lean_ctor_get(v_range_184_, 0);
lean_inc_ref(v_start_186_);
lean_dec_ref(v_range_184_);
v_line_187_ = lean_ctor_get(v_end_185_, 0);
lean_inc(v_line_187_);
v_character_188_ = lean_ctor_get(v_end_185_, 1);
lean_inc(v_character_188_);
lean_dec_ref(v_end_185_);
v_line_189_ = lean_ctor_get(v_start_186_, 0);
lean_inc(v_line_189_);
v_character_190_ = lean_ctor_get(v_start_186_, 1);
lean_inc(v_character_190_);
lean_dec_ref(v_start_186_);
v___x_191_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
v_acc_192_ = lean_string_append(v_acc_183_, v___x_191_);
v___x_193_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_194_ = lean_string_append(v_acc_192_, v___x_193_);
v___x_195_ = l_Nat_reprFast(v_character_188_);
v___x_196_ = lean_string_append(v___x_194_, v___x_195_);
lean_dec_ref(v___x_195_);
v___x_197_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_198_ = lean_string_append(v___x_196_, v___x_197_);
v___x_199_ = l_Nat_reprFast(v_line_187_);
v___x_200_ = lean_string_append(v___x_198_, v___x_199_);
lean_dec_ref(v___x_199_);
v___x_201_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v_acc_202_ = lean_string_append(v___x_200_, v___x_201_);
v___x_203_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
v_acc_204_ = lean_string_append(v_acc_202_, v___x_203_);
v___x_205_ = lean_string_append(v_acc_204_, v___x_193_);
v___x_206_ = l_Nat_reprFast(v_character_190_);
v___x_207_ = lean_string_append(v___x_205_, v___x_206_);
lean_dec_ref(v___x_206_);
v___x_208_ = lean_string_append(v___x_207_, v___x_197_);
v___x_209_ = l_Nat_reprFast(v_line_189_);
v___x_210_ = lean_string_append(v___x_208_, v___x_209_);
lean_dec_ref(v___x_209_);
v_acc_211_ = lean_string_append(v___x_210_, v___x_201_);
v___x_212_ = lean_string_append(v_acc_211_, v___x_201_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast(lean_object* v_acc_216_, lean_object* v_edit_217_){
_start:
{
lean_object* v_insert_218_; lean_object* v_end_219_; lean_object* v_start_220_; lean_object* v_replace_221_; lean_object* v_end_222_; lean_object* v_start_223_; lean_object* v_newText_224_; lean_object* v_line_225_; lean_object* v_character_226_; lean_object* v_line_227_; lean_object* v_character_228_; lean_object* v_line_229_; lean_object* v_character_230_; lean_object* v_line_231_; lean_object* v_character_232_; lean_object* v___x_233_; lean_object* v_acc_234_; lean_object* v___x_235_; lean_object* v_acc_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_acc_246_; lean_object* v___x_247_; lean_object* v_acc_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_acc_255_; lean_object* v_acc_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_acc_261_; lean_object* v___x_262_; lean_object* v_acc_263_; lean_object* v_acc_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_acc_271_; lean_object* v_acc_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_acc_279_; lean_object* v_acc_280_; lean_object* v___x_281_; 
v_insert_218_ = lean_ctor_get(v_edit_217_, 1);
v_end_219_ = lean_ctor_get(v_insert_218_, 1);
lean_inc_ref(v_end_219_);
v_start_220_ = lean_ctor_get(v_insert_218_, 0);
lean_inc_ref(v_start_220_);
v_replace_221_ = lean_ctor_get(v_edit_217_, 2);
v_end_222_ = lean_ctor_get(v_replace_221_, 1);
lean_inc_ref(v_end_222_);
v_start_223_ = lean_ctor_get(v_replace_221_, 0);
lean_inc_ref(v_start_223_);
v_newText_224_ = lean_ctor_get(v_edit_217_, 0);
lean_inc_ref(v_newText_224_);
lean_dec_ref(v_edit_217_);
v_line_225_ = lean_ctor_get(v_end_219_, 0);
lean_inc(v_line_225_);
v_character_226_ = lean_ctor_get(v_end_219_, 1);
lean_inc(v_character_226_);
lean_dec_ref(v_end_219_);
v_line_227_ = lean_ctor_get(v_start_220_, 0);
lean_inc(v_line_227_);
v_character_228_ = lean_ctor_get(v_start_220_, 1);
lean_inc(v_character_228_);
lean_dec_ref(v_start_220_);
v_line_229_ = lean_ctor_get(v_end_222_, 0);
lean_inc(v_line_229_);
v_character_230_ = lean_ctor_get(v_end_222_, 1);
lean_inc(v_character_230_);
lean_dec_ref(v_end_222_);
v_line_231_ = lean_ctor_get(v_start_223_, 0);
lean_inc(v_line_231_);
v_character_232_ = lean_ctor_get(v_start_223_, 1);
lean_inc(v_character_232_);
lean_dec_ref(v_start_223_);
v___x_233_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
v_acc_234_ = lean_string_append(v_acc_216_, v___x_233_);
v___x_235_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
v_acc_236_ = lean_string_append(v_acc_234_, v___x_235_);
v___x_237_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_238_ = lean_string_append(v_acc_236_, v___x_237_);
v___x_239_ = l_Nat_reprFast(v_character_226_);
v___x_240_ = lean_string_append(v___x_238_, v___x_239_);
lean_dec_ref(v___x_239_);
v___x_241_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_242_ = lean_string_append(v___x_240_, v___x_241_);
v___x_243_ = l_Nat_reprFast(v_line_225_);
v___x_244_ = lean_string_append(v___x_242_, v___x_243_);
lean_dec_ref(v___x_243_);
v___x_245_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v_acc_246_ = lean_string_append(v___x_244_, v___x_245_);
v___x_247_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
v_acc_248_ = lean_string_append(v_acc_246_, v___x_247_);
v___x_249_ = lean_string_append(v_acc_248_, v___x_237_);
v___x_250_ = l_Nat_reprFast(v_character_228_);
v___x_251_ = lean_string_append(v___x_249_, v___x_250_);
lean_dec_ref(v___x_250_);
v___x_252_ = lean_string_append(v___x_251_, v___x_241_);
v___x_253_ = l_Nat_reprFast(v_line_227_);
v___x_254_ = lean_string_append(v___x_252_, v___x_253_);
lean_dec_ref(v___x_253_);
v_acc_255_ = lean_string_append(v___x_254_, v___x_245_);
v_acc_256_ = lean_string_append(v_acc_255_, v___x_245_);
v___x_257_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
v___x_258_ = lean_string_append(v_acc_256_, v___x_257_);
v___x_259_ = lean_string_append(v___x_258_, v_newText_224_);
lean_dec_ref(v_newText_224_);
v___x_260_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_261_ = lean_string_append(v___x_259_, v___x_260_);
v___x_262_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
v_acc_263_ = lean_string_append(v_acc_261_, v___x_262_);
v_acc_264_ = lean_string_append(v_acc_263_, v___x_235_);
v___x_265_ = lean_string_append(v_acc_264_, v___x_237_);
v___x_266_ = l_Nat_reprFast(v_character_230_);
v___x_267_ = lean_string_append(v___x_265_, v___x_266_);
lean_dec_ref(v___x_266_);
v___x_268_ = lean_string_append(v___x_267_, v___x_241_);
v___x_269_ = l_Nat_reprFast(v_line_229_);
v___x_270_ = lean_string_append(v___x_268_, v___x_269_);
lean_dec_ref(v___x_269_);
v_acc_271_ = lean_string_append(v___x_270_, v___x_245_);
v_acc_272_ = lean_string_append(v_acc_271_, v___x_247_);
v___x_273_ = lean_string_append(v_acc_272_, v___x_237_);
v___x_274_ = l_Nat_reprFast(v_character_232_);
v___x_275_ = lean_string_append(v___x_273_, v___x_274_);
lean_dec_ref(v___x_274_);
v___x_276_ = lean_string_append(v___x_275_, v___x_241_);
v___x_277_ = l_Nat_reprFast(v_line_231_);
v___x_278_ = lean_string_append(v___x_276_, v___x_277_);
lean_dec_ref(v___x_277_);
v_acc_279_ = lean_string_append(v___x_278_, v___x_245_);
v_acc_280_ = lean_string_append(v_acc_279_, v___x_245_);
v___x_281_ = lean_string_append(v_acc_280_, v___x_245_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(lean_object* v_acc_283_, lean_object* v_tags_284_, lean_object* v_i_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_array_get_size(v_tags_284_);
v___x_287_ = lean_nat_dec_lt(v_i_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_dec(v_i_285_);
return v_acc_283_;
}
else
{
lean_object* v___x_288_; lean_object* v___y_290_; lean_object* v___x_293_; lean_object* v_acc_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_293_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0));
v_acc_294_ = lean_string_append(v_acc_283_, v___x_293_);
v___x_295_ = lean_nat_sub(v___x_286_, v___x_288_);
v___x_296_ = lean_nat_dec_lt(v_i_285_, v___x_295_);
lean_dec(v___x_295_);
if (v___x_296_ == 0)
{
v___y_290_ = v_acc_294_;
goto v___jp_289_;
}
else
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_298_ = lean_string_append(v_acc_294_, v___x_297_);
v___y_290_ = v___x_298_;
goto v___jp_289_;
}
v___jp_289_:
{
lean_object* v___x_291_; 
v___x_291_ = lean_nat_add(v_i_285_, v___x_288_);
lean_dec(v_i_285_);
v_acc_283_ = v___y_290_;
v_i_285_ = v___x_291_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___boxed(lean_object* v_acc_299_, lean_object* v_tags_300_, lean_object* v_i_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_299_, v_tags_300_, v_i_301_);
lean_dec_ref(v_tags_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(lean_object* v___x_303_, lean_object* v_val_304_, lean_object* v_it_305_, lean_object* v_acc_306_, lean_object* v_hP_307_, lean_object* v_recur_308_){
_start:
{
uint8_t v_decide_309_; 
v_decide_309_ = lean_nat_dec_eq(v_it_305_, v___x_303_);
if (v_decide_309_ == 0)
{
uint32_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_310_ = lean_string_utf8_get_fast(v_val_304_, v_it_305_);
v___x_311_ = lean_string_utf8_next_fast(v_val_304_, v_it_305_);
v___x_312_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_306_, v___x_310_);
v___x_313_ = lean_apply_4(v_recur_308_, v___x_311_, v___x_312_, lean_box(0), lean_box(0));
return v___x_313_;
}
else
{
lean_dec_ref(v_recur_308_);
return v_acc_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed(lean_object* v___x_314_, lean_object* v_val_315_, lean_object* v_it_316_, lean_object* v_acc_317_, lean_object* v_hP_318_, lean_object* v_recur_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(v___x_314_, v_val_315_, v_it_316_, v_acc_317_, v_hP_318_, v_recur_319_);
lean_dec(v_it_316_);
lean_dec_ref(v_val_315_);
lean_dec(v___x_314_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(lean_object* v___x_321_, lean_object* v_label_322_, lean_object* v_it_323_, lean_object* v_acc_324_, lean_object* v_hP_325_, lean_object* v_recur_326_){
_start:
{
uint8_t v_decide_327_; 
v_decide_327_ = lean_nat_dec_eq(v_it_323_, v___x_321_);
if (v_decide_327_ == 0)
{
uint32_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_328_ = lean_string_utf8_get_fast(v_label_322_, v_it_323_);
v___x_329_ = lean_string_utf8_next_fast(v_label_322_, v_it_323_);
v___x_330_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_324_, v___x_328_);
v___x_331_ = lean_apply_4(v_recur_326_, v___x_329_, v___x_330_, lean_box(0), lean_box(0));
return v___x_331_;
}
else
{
lean_dec_ref(v_recur_326_);
return v_acc_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed(lean_object* v___x_332_, lean_object* v_label_333_, lean_object* v_it_334_, lean_object* v_acc_335_, lean_object* v_hP_336_, lean_object* v_recur_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(v___x_332_, v_label_333_, v_it_334_, v_acc_335_, v_hP_336_, v_recur_337_);
lean_dec(v_it_334_);
lean_dec_ref(v_label_333_);
lean_dec(v___x_332_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast(lean_object* v_acc_347_, lean_object* v_item_348_){
_start:
{
lean_object* v_acc_350_; lean_object* v_acc_354_; lean_object* v_label_357_; lean_object* v_detail_x3f_358_; lean_object* v_documentation_x3f_359_; lean_object* v_kind_x3f_360_; lean_object* v_textEdit_x3f_361_; lean_object* v_sortText_x3f_362_; lean_object* v_data_x3f_363_; lean_object* v_tags_x3f_364_; lean_object* v_acc_366_; lean_object* v_acc_379_; lean_object* v___y_383_; lean_object* v___y_387_; lean_object* v___y_391_; lean_object* v_id_x3f_392_; lean_object* v_acc_393_; lean_object* v_pos_419_; lean_object* v_cPos_x3f_420_; lean_object* v_id_x3f_421_; lean_object* v___y_422_; lean_object* v_acc_437_; lean_object* v_acc_458_; lean_object* v_acc_473_; lean_object* v_acc_542_; lean_object* v___y_553_; lean_object* v_value_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v_acc_576_; lean_object* v___y_585_; lean_object* v___x_599_; lean_object* v_acc_600_; lean_object* v___x_601_; lean_object* v_acc_602_; uint8_t v___x_603_; 
v_label_357_ = lean_ctor_get(v_item_348_, 0);
lean_inc_ref(v_label_357_);
v_detail_x3f_358_ = lean_ctor_get(v_item_348_, 1);
lean_inc(v_detail_x3f_358_);
v_documentation_x3f_359_ = lean_ctor_get(v_item_348_, 2);
lean_inc(v_documentation_x3f_359_);
v_kind_x3f_360_ = lean_ctor_get(v_item_348_, 3);
lean_inc(v_kind_x3f_360_);
v_textEdit_x3f_361_ = lean_ctor_get(v_item_348_, 4);
lean_inc(v_textEdit_x3f_361_);
v_sortText_x3f_362_ = lean_ctor_get(v_item_348_, 5);
lean_inc(v_sortText_x3f_362_);
v_data_x3f_363_ = lean_ctor_get(v_item_348_, 6);
lean_inc(v_data_x3f_363_);
v_tags_x3f_364_ = lean_ctor_get(v_item_348_, 7);
lean_inc(v_tags_x3f_364_);
lean_dec_ref(v_item_348_);
v___x_599_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7));
v_acc_600_ = lean_string_append(v_acc_347_, v___x_599_);
v___x_601_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_602_ = lean_string_append(v_acc_600_, v___x_601_);
v___x_603_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_label_357_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_string_append(v_acc_602_, v_label_357_);
lean_dec_ref(v_label_357_);
v___x_605_ = lean_string_append(v___x_604_, v___x_601_);
v___y_585_ = v___x_605_;
goto v___jp_584_;
}
else
{
lean_object* v___x_606_; lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_606_ = lean_string_utf8_byte_size(v_label_357_);
v___f_607_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed), 6, 2);
lean_closure_set(v___f_607_, 0, v___x_606_);
lean_closure_set(v___f_607_, 1, v_label_357_);
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_607_, v___x_608_, v_acc_602_, lean_box(0));
v___x_610_ = lean_string_append(v___x_609_, v___x_601_);
v___y_585_ = v___x_610_;
goto v___jp_584_;
}
v___jp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_352_ = lean_string_append(v_acc_350_, v___x_351_);
return v___x_352_;
}
v___jp_353_:
{
lean_object* v___x_355_; lean_object* v_acc_356_; 
v___x_355_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v_acc_356_ = lean_string_append(v_acc_354_, v___x_355_);
v_acc_350_ = v_acc_356_;
goto v___jp_349_;
}
v___jp_365_:
{
if (lean_obj_tag(v_tags_x3f_364_) == 1)
{
lean_object* v_val_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_val_367_ = lean_ctor_get(v_tags_x3f_364_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v_tags_x3f_364_, 1);
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = lean_array_get_size(v_val_367_);
v___x_370_ = lean_nat_dec_lt(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_dec(v_val_367_);
v_acc_350_ = v_acc_366_;
goto v___jp_349_;
}
else
{
lean_object* v___x_371_; lean_object* v_acc_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_371_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0));
v_acc_372_ = lean_string_append(v_acc_366_, v___x_371_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_dec_eq(v___x_369_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v_acc_375_; 
v_acc_375_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_372_, v_val_367_, v___x_368_);
lean_dec(v_val_367_);
v_acc_354_ = v_acc_375_;
goto v___jp_353_;
}
else
{
lean_object* v___x_376_; lean_object* v_acc_377_; 
lean_dec(v_val_367_);
v___x_376_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0));
v_acc_377_ = lean_string_append(v_acc_372_, v___x_376_);
v_acc_354_ = v_acc_377_;
goto v___jp_353_;
}
}
}
else
{
lean_dec(v_tags_x3f_364_);
v_acc_350_ = v_acc_366_;
goto v___jp_349_;
}
}
v___jp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v___x_381_ = lean_string_append(v_acc_379_, v___x_380_);
v_acc_366_ = v___x_381_;
goto v___jp_365_;
}
v___jp_382_:
{
lean_object* v___x_384_; lean_object* v_acc_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_385_ = lean_string_append(v___y_383_, v___x_384_);
v_acc_379_ = v_acc_385_;
goto v___jp_378_;
}
v___jp_386_:
{
lean_object* v___x_388_; lean_object* v_acc_389_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_389_ = lean_string_append(v___y_387_, v___x_388_);
v_acc_379_ = v_acc_389_;
goto v___jp_378_;
}
v___jp_390_:
{
if (lean_obj_tag(v_id_x3f_392_) == 1)
{
lean_object* v_val_394_; lean_object* v_acc_395_; 
v_val_394_ = lean_ctor_get(v_id_x3f_392_, 0);
lean_inc(v_val_394_);
lean_dec_ref_known(v_id_x3f_392_, 1);
v_acc_395_ = lean_string_append(v_acc_393_, v___y_391_);
if (lean_obj_tag(v_val_394_) == 0)
{
lean_object* v_declName_396_; lean_object* v___x_397_; lean_object* v_acc_398_; uint8_t v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_declName_396_ = lean_ctor_get(v_val_394_, 0);
lean_inc(v_declName_396_);
lean_dec_ref_known(v_val_394_, 1);
v___x_397_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2));
v_acc_398_ = lean_string_append(v_acc_395_, v___x_397_);
v___x_399_ = 1;
v___x_400_ = l_Lean_Name_toString(v_declName_396_, v___x_399_);
v___x_401_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; 
v___x_402_ = lean_string_append(v_acc_398_, v___x_400_);
lean_dec_ref(v___x_400_);
v___y_387_ = v___x_402_;
goto v___jp_386_;
}
else
{
lean_object* v___x_403_; lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_string_utf8_byte_size(v___x_400_);
v___f_404_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_404_, 0, v___x_403_);
lean_closure_set(v___f_404_, 1, v___x_400_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_404_, v___x_405_, v_acc_398_, lean_box(0));
v___y_387_ = v___x_406_;
goto v___jp_386_;
}
}
else
{
lean_object* v_id_407_; lean_object* v___x_408_; lean_object* v_acc_409_; uint8_t v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v_id_407_ = lean_ctor_get(v_val_394_, 0);
lean_inc(v_id_407_);
lean_dec_ref_known(v_val_394_, 1);
v___x_408_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
v_acc_409_ = lean_string_append(v_acc_395_, v___x_408_);
v___x_410_ = 1;
v___x_411_ = l_Lean_Name_toString(v_id_407_, v___x_410_);
v___x_412_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
v___x_413_ = lean_string_append(v_acc_409_, v___x_411_);
lean_dec_ref(v___x_411_);
v___y_383_ = v___x_413_;
goto v___jp_382_;
}
else
{
lean_object* v___x_414_; lean_object* v___f_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = lean_string_utf8_byte_size(v___x_411_);
v___f_415_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_415_, 0, v___x_414_);
lean_closure_set(v___f_415_, 1, v___x_411_);
v___x_416_ = lean_unsigned_to_nat(0u);
v___x_417_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_415_, v___x_416_, v_acc_409_, lean_box(0));
v___y_383_ = v___x_417_;
goto v___jp_382_;
}
}
}
else
{
lean_dec(v_id_x3f_392_);
v_acc_379_ = v_acc_393_;
goto v___jp_378_;
}
}
v___jp_418_:
{
lean_object* v_line_423_; lean_object* v_character_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v_acc_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v_acc_431_; 
v_line_423_ = lean_ctor_get(v_pos_419_, 0);
lean_inc(v_line_423_);
v_character_424_ = lean_ctor_get(v_pos_419_, 1);
lean_inc(v_character_424_);
lean_dec_ref(v_pos_419_);
v___x_425_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_426_ = lean_string_append(v___y_422_, v___x_425_);
v___x_427_ = l_Nat_reprFast(v_line_423_);
v_acc_428_ = lean_string_append(v___x_426_, v___x_427_);
lean_dec_ref(v___x_427_);
v___x_429_ = lean_string_append(v_acc_428_, v___x_425_);
v___x_430_ = l_Nat_reprFast(v_character_424_);
v_acc_431_ = lean_string_append(v___x_429_, v___x_430_);
lean_dec_ref(v___x_430_);
if (lean_obj_tag(v_cPos_x3f_420_) == 1)
{
lean_object* v_val_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_acc_435_; 
v_val_432_ = lean_ctor_get(v_cPos_x3f_420_, 0);
lean_inc(v_val_432_);
lean_dec_ref_known(v_cPos_x3f_420_, 1);
v___x_433_ = lean_string_append(v_acc_431_, v___x_425_);
v___x_434_ = l_Nat_reprFast(v_val_432_);
v_acc_435_ = lean_string_append(v___x_433_, v___x_434_);
lean_dec_ref(v___x_434_);
v___y_391_ = v___x_425_;
v_id_x3f_392_ = v_id_x3f_421_;
v_acc_393_ = v_acc_435_;
goto v___jp_390_;
}
else
{
lean_dec(v_cPos_x3f_420_);
v___y_391_ = v___x_425_;
v_id_x3f_392_ = v_id_x3f_421_;
v_acc_393_ = v_acc_431_;
goto v___jp_390_;
}
}
v___jp_436_:
{
if (lean_obj_tag(v_data_x3f_363_) == 1)
{
lean_object* v_val_438_; lean_object* v_uri_439_; lean_object* v_pos_440_; lean_object* v_cPos_x3f_441_; lean_object* v_id_x3f_442_; lean_object* v___x_443_; lean_object* v_acc_444_; lean_object* v___x_445_; lean_object* v_acc_446_; lean_object* v___x_447_; lean_object* v_acc_448_; uint8_t v___x_449_; 
v_val_438_ = lean_ctor_get(v_data_x3f_363_, 0);
lean_inc(v_val_438_);
lean_dec_ref_known(v_data_x3f_363_, 1);
v_uri_439_ = lean_ctor_get(v_val_438_, 0);
lean_inc_ref(v_uri_439_);
v_pos_440_ = lean_ctor_get(v_val_438_, 1);
lean_inc_ref(v_pos_440_);
v_cPos_x3f_441_ = lean_ctor_get(v_val_438_, 2);
lean_inc(v_cPos_x3f_441_);
v_id_x3f_442_ = lean_ctor_get(v_val_438_, 3);
lean_inc(v_id_x3f_442_);
lean_dec(v_val_438_);
v___x_443_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1));
v_acc_444_ = lean_string_append(v_acc_437_, v___x_443_);
v___x_445_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
v_acc_446_ = lean_string_append(v_acc_444_, v___x_445_);
v___x_447_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_448_ = lean_string_append(v_acc_446_, v___x_447_);
v___x_449_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_439_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_string_append(v_acc_448_, v_uri_439_);
lean_dec_ref(v_uri_439_);
v___x_451_ = lean_string_append(v___x_450_, v___x_447_);
v_pos_419_ = v_pos_440_;
v_cPos_x3f_420_ = v_cPos_x3f_441_;
v_id_x3f_421_ = v_id_x3f_442_;
v___y_422_ = v___x_451_;
goto v___jp_418_;
}
else
{
lean_object* v___x_452_; lean_object* v___f_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_452_ = lean_string_utf8_byte_size(v_uri_439_);
v___f_453_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed), 6, 2);
lean_closure_set(v___f_453_, 0, v___x_452_);
lean_closure_set(v___f_453_, 1, v_uri_439_);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_453_, v___x_454_, v_acc_448_, lean_box(0));
v___x_456_ = lean_string_append(v___x_455_, v___x_447_);
v_pos_419_ = v_pos_440_;
v_cPos_x3f_420_ = v_cPos_x3f_441_;
v_id_x3f_421_ = v_id_x3f_442_;
v___y_422_ = v___x_456_;
goto v___jp_418_;
}
}
else
{
lean_dec(v_data_x3f_363_);
v_acc_366_ = v_acc_437_;
goto v___jp_365_;
}
}
v___jp_457_:
{
if (lean_obj_tag(v_sortText_x3f_362_) == 1)
{
lean_object* v_val_459_; lean_object* v___x_460_; lean_object* v_acc_461_; lean_object* v___x_462_; lean_object* v_acc_463_; uint8_t v___x_464_; 
v_val_459_ = lean_ctor_get(v_sortText_x3f_362_, 0);
lean_inc(v_val_459_);
lean_dec_ref_known(v_sortText_x3f_362_, 1);
v___x_460_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2));
v_acc_461_ = lean_string_append(v_acc_458_, v___x_460_);
v___x_462_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_463_ = lean_string_append(v_acc_461_, v___x_462_);
v___x_464_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_459_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_string_append(v_acc_463_, v_val_459_);
lean_dec(v_val_459_);
v___x_466_ = lean_string_append(v___x_465_, v___x_462_);
v_acc_437_ = v___x_466_;
goto v___jp_436_;
}
else
{
lean_object* v___x_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_467_ = lean_string_utf8_byte_size(v_val_459_);
v___f_468_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed), 6, 2);
lean_closure_set(v___f_468_, 0, v___x_467_);
lean_closure_set(v___f_468_, 1, v_val_459_);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_468_, v___x_469_, v_acc_463_, lean_box(0));
v___x_471_ = lean_string_append(v___x_470_, v___x_462_);
v_acc_437_ = v___x_471_;
goto v___jp_436_;
}
}
else
{
lean_dec(v_sortText_x3f_362_);
v_acc_437_ = v_acc_458_;
goto v___jp_436_;
}
}
v___jp_472_:
{
if (lean_obj_tag(v_textEdit_x3f_361_) == 1)
{
lean_object* v_val_474_; lean_object* v_insert_475_; lean_object* v_end_476_; lean_object* v_start_477_; lean_object* v_replace_478_; lean_object* v_end_479_; lean_object* v_start_480_; lean_object* v_newText_481_; lean_object* v_line_482_; lean_object* v_character_483_; lean_object* v_line_484_; lean_object* v_character_485_; lean_object* v_line_486_; lean_object* v_character_487_; lean_object* v_line_488_; lean_object* v_character_489_; lean_object* v___x_490_; lean_object* v_acc_491_; lean_object* v___x_492_; lean_object* v_acc_493_; lean_object* v___x_494_; lean_object* v_acc_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_acc_505_; lean_object* v___x_506_; lean_object* v_acc_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_acc_514_; lean_object* v_acc_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v_acc_520_; lean_object* v___x_521_; lean_object* v_acc_522_; lean_object* v_acc_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_acc_530_; lean_object* v_acc_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_acc_538_; lean_object* v_acc_539_; lean_object* v_acc_540_; 
v_val_474_ = lean_ctor_get(v_textEdit_x3f_361_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v_textEdit_x3f_361_, 1);
v_insert_475_ = lean_ctor_get(v_val_474_, 1);
v_end_476_ = lean_ctor_get(v_insert_475_, 1);
lean_inc_ref(v_end_476_);
v_start_477_ = lean_ctor_get(v_insert_475_, 0);
lean_inc_ref(v_start_477_);
v_replace_478_ = lean_ctor_get(v_val_474_, 2);
v_end_479_ = lean_ctor_get(v_replace_478_, 1);
lean_inc_ref(v_end_479_);
v_start_480_ = lean_ctor_get(v_replace_478_, 0);
lean_inc_ref(v_start_480_);
v_newText_481_ = lean_ctor_get(v_val_474_, 0);
lean_inc_ref(v_newText_481_);
lean_dec(v_val_474_);
v_line_482_ = lean_ctor_get(v_end_476_, 0);
lean_inc(v_line_482_);
v_character_483_ = lean_ctor_get(v_end_476_, 1);
lean_inc(v_character_483_);
lean_dec_ref(v_end_476_);
v_line_484_ = lean_ctor_get(v_start_477_, 0);
lean_inc(v_line_484_);
v_character_485_ = lean_ctor_get(v_start_477_, 1);
lean_inc(v_character_485_);
lean_dec_ref(v_start_477_);
v_line_486_ = lean_ctor_get(v_end_479_, 0);
lean_inc(v_line_486_);
v_character_487_ = lean_ctor_get(v_end_479_, 1);
lean_inc(v_character_487_);
lean_dec_ref(v_end_479_);
v_line_488_ = lean_ctor_get(v_start_480_, 0);
lean_inc(v_line_488_);
v_character_489_ = lean_ctor_get(v_start_480_, 1);
lean_inc(v_character_489_);
lean_dec_ref(v_start_480_);
v___x_490_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3));
v_acc_491_ = lean_string_append(v_acc_473_, v___x_490_);
v___x_492_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
v_acc_493_ = lean_string_append(v_acc_491_, v___x_492_);
v___x_494_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
v_acc_495_ = lean_string_append(v_acc_493_, v___x_494_);
v___x_496_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_497_ = lean_string_append(v_acc_495_, v___x_496_);
v___x_498_ = l_Nat_reprFast(v_character_483_);
v___x_499_ = lean_string_append(v___x_497_, v___x_498_);
lean_dec_ref(v___x_498_);
v___x_500_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_501_ = lean_string_append(v___x_499_, v___x_500_);
v___x_502_ = l_Nat_reprFast(v_line_482_);
v___x_503_ = lean_string_append(v___x_501_, v___x_502_);
lean_dec_ref(v___x_502_);
v___x_504_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v_acc_505_ = lean_string_append(v___x_503_, v___x_504_);
v___x_506_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
v_acc_507_ = lean_string_append(v_acc_505_, v___x_506_);
v___x_508_ = lean_string_append(v_acc_507_, v___x_496_);
v___x_509_ = l_Nat_reprFast(v_character_485_);
v___x_510_ = lean_string_append(v___x_508_, v___x_509_);
lean_dec_ref(v___x_509_);
v___x_511_ = lean_string_append(v___x_510_, v___x_500_);
v___x_512_ = l_Nat_reprFast(v_line_484_);
v___x_513_ = lean_string_append(v___x_511_, v___x_512_);
lean_dec_ref(v___x_512_);
v_acc_514_ = lean_string_append(v___x_513_, v___x_504_);
v_acc_515_ = lean_string_append(v_acc_514_, v___x_504_);
v___x_516_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
v___x_517_ = lean_string_append(v_acc_515_, v___x_516_);
v___x_518_ = lean_string_append(v___x_517_, v_newText_481_);
lean_dec_ref(v_newText_481_);
v___x_519_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_520_ = lean_string_append(v___x_518_, v___x_519_);
v___x_521_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
v_acc_522_ = lean_string_append(v_acc_520_, v___x_521_);
v_acc_523_ = lean_string_append(v_acc_522_, v___x_494_);
v___x_524_ = lean_string_append(v_acc_523_, v___x_496_);
v___x_525_ = l_Nat_reprFast(v_character_487_);
v___x_526_ = lean_string_append(v___x_524_, v___x_525_);
lean_dec_ref(v___x_525_);
v___x_527_ = lean_string_append(v___x_526_, v___x_500_);
v___x_528_ = l_Nat_reprFast(v_line_486_);
v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
lean_dec_ref(v___x_528_);
v_acc_530_ = lean_string_append(v___x_529_, v___x_504_);
v_acc_531_ = lean_string_append(v_acc_530_, v___x_506_);
v___x_532_ = lean_string_append(v_acc_531_, v___x_496_);
v___x_533_ = l_Nat_reprFast(v_character_489_);
v___x_534_ = lean_string_append(v___x_532_, v___x_533_);
lean_dec_ref(v___x_533_);
v___x_535_ = lean_string_append(v___x_534_, v___x_500_);
v___x_536_ = l_Nat_reprFast(v_line_488_);
v___x_537_ = lean_string_append(v___x_535_, v___x_536_);
lean_dec_ref(v___x_536_);
v_acc_538_ = lean_string_append(v___x_537_, v___x_504_);
v_acc_539_ = lean_string_append(v_acc_538_, v___x_504_);
v_acc_540_ = lean_string_append(v_acc_539_, v___x_504_);
v_acc_458_ = v_acc_540_;
goto v___jp_457_;
}
else
{
lean_dec(v_textEdit_x3f_361_);
v_acc_458_ = v_acc_473_;
goto v___jp_457_;
}
}
v___jp_541_:
{
if (lean_obj_tag(v_kind_x3f_360_) == 1)
{
lean_object* v_val_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_acc_551_; 
v_val_543_ = lean_ctor_get(v_kind_x3f_360_, 0);
lean_inc(v_val_543_);
lean_dec_ref_known(v_kind_x3f_360_, 1);
v___x_544_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4));
v___x_545_ = lean_string_append(v_acc_542_, v___x_544_);
v___x_546_ = lean_unbox(v_val_543_);
lean_dec(v_val_543_);
v___x_547_ = l_Lean_Lsp_CompletionItemKind_ctorIdx(v___x_546_);
v___x_548_ = lean_unsigned_to_nat(1u);
v___x_549_ = lean_nat_add(v___x_547_, v___x_548_);
lean_dec(v___x_547_);
v___x_550_ = l_Nat_reprFast(v___x_549_);
v_acc_551_ = lean_string_append(v___x_545_, v___x_550_);
lean_dec_ref(v___x_550_);
v_acc_473_ = v_acc_551_;
goto v___jp_472_;
}
else
{
lean_dec(v_kind_x3f_360_);
v_acc_473_ = v_acc_542_;
goto v___jp_472_;
}
}
v___jp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_555_ = lean_string_append(v___y_553_, v___x_554_);
v_acc_542_ = v___x_555_;
goto v___jp_541_;
}
v___jp_556_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v_acc_564_; lean_object* v___x_565_; lean_object* v_acc_566_; uint8_t v___x_567_; 
v___x_560_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
v___x_561_ = lean_string_append(v___y_558_, v___x_560_);
v___x_562_ = lean_string_append(v___x_561_, v___y_559_);
v___x_563_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
v_acc_564_ = lean_string_append(v___x_562_, v___x_563_);
v___x_565_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_566_ = lean_string_append(v_acc_564_, v___x_565_);
v___x_567_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_557_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_string_append(v_acc_566_, v_value_557_);
lean_dec_ref(v_value_557_);
v___x_569_ = lean_string_append(v___x_568_, v___x_565_);
v___y_553_ = v___x_569_;
goto v___jp_552_;
}
else
{
lean_object* v___x_570_; lean_object* v___f_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_570_ = lean_string_utf8_byte_size(v_value_557_);
v___f_571_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_571_, 0, v___x_570_);
lean_closure_set(v___f_571_, 1, v_value_557_);
v___x_572_ = lean_unsigned_to_nat(0u);
v___x_573_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_571_, v___x_572_, v_acc_566_, lean_box(0));
v___x_574_ = lean_string_append(v___x_573_, v___x_565_);
v___y_553_ = v___x_574_;
goto v___jp_552_;
}
}
v___jp_575_:
{
if (lean_obj_tag(v_documentation_x3f_359_) == 1)
{
lean_object* v_val_577_; uint8_t v_kind_578_; lean_object* v_value_579_; lean_object* v___x_580_; lean_object* v_acc_581_; 
v_val_577_ = lean_ctor_get(v_documentation_x3f_359_, 0);
lean_inc(v_val_577_);
lean_dec_ref_known(v_documentation_x3f_359_, 1);
v_kind_578_ = lean_ctor_get_uint8(v_val_577_, sizeof(void*)*1);
v_value_579_ = lean_ctor_get(v_val_577_, 0);
lean_inc_ref(v_value_579_);
lean_dec(v_val_577_);
v___x_580_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5));
v_acc_581_ = lean_string_append(v_acc_576_, v___x_580_);
if (v_kind_578_ == 0)
{
lean_object* v___x_582_; 
v___x_582_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
v_value_557_ = v_value_579_;
v___y_558_ = v_acc_581_;
v___y_559_ = v___x_582_;
goto v___jp_556_;
}
else
{
lean_object* v___x_583_; 
v___x_583_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
v_value_557_ = v_value_579_;
v___y_558_ = v_acc_581_;
v___y_559_ = v___x_583_;
goto v___jp_556_;
}
}
else
{
lean_dec(v_documentation_x3f_359_);
v_acc_542_ = v_acc_576_;
goto v___jp_541_;
}
}
v___jp_584_:
{
if (lean_obj_tag(v_detail_x3f_358_) == 1)
{
lean_object* v_val_586_; lean_object* v___x_587_; lean_object* v_acc_588_; lean_object* v___x_589_; lean_object* v_acc_590_; uint8_t v___x_591_; 
v_val_586_ = lean_ctor_get(v_detail_x3f_358_, 0);
lean_inc(v_val_586_);
lean_dec_ref_known(v_detail_x3f_358_, 1);
v___x_587_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6));
v_acc_588_ = lean_string_append(v___y_585_, v___x_587_);
v___x_589_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_590_ = lean_string_append(v_acc_588_, v___x_589_);
v___x_591_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_586_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_string_append(v_acc_590_, v_val_586_);
lean_dec(v_val_586_);
v___x_593_ = lean_string_append(v___x_592_, v___x_589_);
v_acc_576_ = v___x_593_;
goto v___jp_575_;
}
else
{
lean_object* v___x_594_; lean_object* v___f_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_594_ = lean_string_utf8_byte_size(v_val_586_);
v___f_595_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed), 6, 2);
lean_closure_set(v___f_595_, 0, v___x_594_);
lean_closure_set(v___f_595_, 1, v_val_586_);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_595_, v___x_596_, v_acc_590_, lean_box(0));
v___x_598_ = lean_string_append(v___x_597_, v___x_589_);
v_acc_576_ = v___x_598_;
goto v___jp_575_;
}
}
else
{
lean_dec(v_detail_x3f_358_);
v_acc_576_ = v___y_585_;
goto v___jp_575_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_a_613_, lean_object* v_b_614_){
_start:
{
uint8_t v_decide_615_; 
v_decide_615_ = lean_nat_dec_eq(v_a_613_, v___x_611_);
if (v_decide_615_ == 0)
{
uint32_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = lean_string_utf8_get_fast(v___x_612_, v_a_613_);
v___x_617_ = lean_string_utf8_next_fast(v___x_612_, v_a_613_);
lean_dec(v_a_613_);
v___x_618_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_b_614_, v___x_616_);
v_a_613_ = v___x_617_;
v_b_614_ = v___x_618_;
goto _start;
}
else
{
lean_dec(v_a_613_);
return v_b_614_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg___boxed(lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v_a_622_, lean_object* v_b_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_620_, v___x_621_, v_a_622_, v_b_623_);
lean_dec_ref(v___x_621_);
lean_dec(v___x_620_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(lean_object* v_acc_625_, lean_object* v_items_626_, lean_object* v_i_627_){
_start:
{
lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___x_633_; lean_object* v_acc_635_; lean_object* v_acc_644_; uint8_t v___x_647_; 
v___x_633_ = lean_array_get_size(v_items_626_);
v___x_647_ = lean_nat_dec_lt(v_i_627_, v___x_633_);
if (v___x_647_ == 0)
{
lean_dec(v_i_627_);
return v_acc_625_;
}
else
{
lean_object* v___x_648_; lean_object* v_acc_650_; lean_object* v_acc_664_; lean_object* v___y_668_; lean_object* v___y_672_; lean_object* v___y_676_; lean_object* v_id_x3f_677_; lean_object* v_acc_678_; lean_object* v_pos_700_; lean_object* v_cPos_x3f_701_; lean_object* v_id_x3f_702_; lean_object* v___y_703_; lean_object* v_acc_718_; lean_object* v_acc_739_; lean_object* v_acc_754_; lean_object* v_acc_824_; lean_object* v___y_836_; lean_object* v_value_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v_acc_858_; lean_object* v___y_868_; lean_object* v_label_882_; lean_object* v___x_883_; lean_object* v_acc_884_; lean_object* v___x_885_; lean_object* v_acc_886_; uint8_t v___x_887_; 
v___x_648_ = lean_array_fget_borrowed(v_items_626_, v_i_627_);
v_label_882_ = lean_ctor_get(v___x_648_, 0);
v___x_883_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7));
v_acc_884_ = lean_string_append(v_acc_625_, v___x_883_);
v___x_885_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_886_ = lean_string_append(v_acc_884_, v___x_885_);
v___x_887_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_label_882_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_string_append(v_acc_886_, v_label_882_);
v___x_889_ = lean_string_append(v___x_888_, v___x_885_);
v___y_868_ = v___x_889_;
goto v___jp_867_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_890_ = lean_string_utf8_byte_size(v_label_882_);
v___x_891_ = lean_unsigned_to_nat(0u);
v___x_892_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_890_, v_label_882_, v___x_891_, v_acc_886_);
v___x_893_ = lean_string_append(v___x_892_, v___x_885_);
v___y_868_ = v___x_893_;
goto v___jp_867_;
}
v___jp_649_:
{
lean_object* v_tags_x3f_651_; 
v_tags_x3f_651_ = lean_ctor_get(v___x_648_, 7);
if (lean_obj_tag(v_tags_x3f_651_) == 1)
{
lean_object* v_val_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_val_652_ = lean_ctor_get(v_tags_x3f_651_, 0);
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = lean_array_get_size(v_val_652_);
v___x_655_ = lean_nat_dec_lt(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
v_acc_635_ = v_acc_650_;
goto v___jp_634_;
}
else
{
lean_object* v___x_656_; lean_object* v_acc_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_656_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0));
v_acc_657_ = lean_string_append(v_acc_650_, v___x_656_);
v___x_658_ = lean_unsigned_to_nat(1u);
v___x_659_ = lean_nat_dec_eq(v___x_654_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v_acc_660_; 
v_acc_660_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_657_, v_val_652_, v___x_653_);
v_acc_644_ = v_acc_660_;
goto v___jp_643_;
}
else
{
lean_object* v___x_661_; lean_object* v_acc_662_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0));
v_acc_662_ = lean_string_append(v_acc_657_, v___x_661_);
v_acc_644_ = v_acc_662_;
goto v___jp_643_;
}
}
}
else
{
v_acc_635_ = v_acc_650_;
goto v___jp_634_;
}
}
v___jp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v___x_666_ = lean_string_append(v_acc_664_, v___x_665_);
v_acc_650_ = v___x_666_;
goto v___jp_649_;
}
v___jp_667_:
{
lean_object* v___x_669_; lean_object* v_acc_670_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_670_ = lean_string_append(v___y_668_, v___x_669_);
v_acc_664_ = v_acc_670_;
goto v___jp_663_;
}
v___jp_671_:
{
lean_object* v___x_673_; lean_object* v_acc_674_; 
v___x_673_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_674_ = lean_string_append(v___y_672_, v___x_673_);
v_acc_664_ = v_acc_674_;
goto v___jp_663_;
}
v___jp_675_:
{
if (lean_obj_tag(v_id_x3f_677_) == 1)
{
lean_object* v_val_679_; lean_object* v_acc_680_; 
v_val_679_ = lean_ctor_get(v_id_x3f_677_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_id_x3f_677_, 1);
v_acc_680_ = lean_string_append(v_acc_678_, v___y_676_);
if (lean_obj_tag(v_val_679_) == 0)
{
lean_object* v_declName_681_; lean_object* v___x_682_; lean_object* v_acc_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_declName_681_ = lean_ctor_get(v_val_679_, 0);
lean_inc(v_declName_681_);
lean_dec_ref_known(v_val_679_, 1);
v___x_682_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2));
v_acc_683_ = lean_string_append(v_acc_680_, v___x_682_);
v___x_684_ = l_Lean_Name_toString(v_declName_681_, v___x_647_);
v___x_685_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; 
v___x_686_ = lean_string_append(v_acc_683_, v___x_684_);
lean_dec_ref(v___x_684_);
v___y_668_ = v___x_686_;
goto v___jp_667_;
}
else
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_string_utf8_byte_size(v___x_684_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_687_, v___x_684_, v___x_688_, v_acc_683_);
lean_dec_ref(v___x_684_);
v___y_668_ = v___x_689_;
goto v___jp_667_;
}
}
else
{
lean_object* v_id_690_; lean_object* v___x_691_; lean_object* v_acc_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_id_690_ = lean_ctor_get(v_val_679_, 0);
lean_inc(v_id_690_);
lean_dec_ref_known(v_val_679_, 1);
v___x_691_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
v_acc_692_ = lean_string_append(v_acc_680_, v___x_691_);
v___x_693_ = l_Lean_Name_toString(v_id_690_, v___x_647_);
v___x_694_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
v___x_695_ = lean_string_append(v_acc_692_, v___x_693_);
lean_dec_ref(v___x_693_);
v___y_672_ = v___x_695_;
goto v___jp_671_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_string_utf8_byte_size(v___x_693_);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_696_, v___x_693_, v___x_697_, v_acc_692_);
lean_dec_ref(v___x_693_);
v___y_672_ = v___x_698_;
goto v___jp_671_;
}
}
}
else
{
lean_dec(v_id_x3f_677_);
v_acc_664_ = v_acc_678_;
goto v___jp_663_;
}
}
v___jp_699_:
{
lean_object* v_line_704_; lean_object* v_character_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v_acc_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v_acc_712_; 
v_line_704_ = lean_ctor_get(v_pos_700_, 0);
lean_inc(v_line_704_);
v_character_705_ = lean_ctor_get(v_pos_700_, 1);
lean_inc(v_character_705_);
lean_dec_ref(v_pos_700_);
v___x_706_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_707_ = lean_string_append(v___y_703_, v___x_706_);
v___x_708_ = l_Nat_reprFast(v_line_704_);
v_acc_709_ = lean_string_append(v___x_707_, v___x_708_);
lean_dec_ref(v___x_708_);
v___x_710_ = lean_string_append(v_acc_709_, v___x_706_);
v___x_711_ = l_Nat_reprFast(v_character_705_);
v_acc_712_ = lean_string_append(v___x_710_, v___x_711_);
lean_dec_ref(v___x_711_);
if (lean_obj_tag(v_cPos_x3f_701_) == 1)
{
lean_object* v_val_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v_acc_716_; 
v_val_713_ = lean_ctor_get(v_cPos_x3f_701_, 0);
lean_inc(v_val_713_);
lean_dec_ref_known(v_cPos_x3f_701_, 1);
v___x_714_ = lean_string_append(v_acc_712_, v___x_706_);
v___x_715_ = l_Nat_reprFast(v_val_713_);
v_acc_716_ = lean_string_append(v___x_714_, v___x_715_);
lean_dec_ref(v___x_715_);
v___y_676_ = v___x_706_;
v_id_x3f_677_ = v_id_x3f_702_;
v_acc_678_ = v_acc_716_;
goto v___jp_675_;
}
else
{
lean_dec(v_cPos_x3f_701_);
v___y_676_ = v___x_706_;
v_id_x3f_677_ = v_id_x3f_702_;
v_acc_678_ = v_acc_712_;
goto v___jp_675_;
}
}
v___jp_717_:
{
lean_object* v_data_x3f_719_; 
v_data_x3f_719_ = lean_ctor_get(v___x_648_, 6);
if (lean_obj_tag(v_data_x3f_719_) == 1)
{
lean_object* v_val_720_; lean_object* v_uri_721_; lean_object* v_pos_722_; lean_object* v_cPos_x3f_723_; lean_object* v_id_x3f_724_; lean_object* v___x_725_; lean_object* v_acc_726_; lean_object* v___x_727_; lean_object* v_acc_728_; lean_object* v___x_729_; lean_object* v_acc_730_; uint8_t v___x_731_; 
v_val_720_ = lean_ctor_get(v_data_x3f_719_, 0);
v_uri_721_ = lean_ctor_get(v_val_720_, 0);
v_pos_722_ = lean_ctor_get(v_val_720_, 1);
v_cPos_x3f_723_ = lean_ctor_get(v_val_720_, 2);
v_id_x3f_724_ = lean_ctor_get(v_val_720_, 3);
v___x_725_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1));
v_acc_726_ = lean_string_append(v_acc_718_, v___x_725_);
v___x_727_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
v_acc_728_ = lean_string_append(v_acc_726_, v___x_727_);
v___x_729_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_730_ = lean_string_append(v_acc_728_, v___x_729_);
v___x_731_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_721_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_string_append(v_acc_730_, v_uri_721_);
v___x_733_ = lean_string_append(v___x_732_, v___x_729_);
lean_inc(v_id_x3f_724_);
lean_inc(v_cPos_x3f_723_);
lean_inc_ref(v_pos_722_);
v_pos_700_ = v_pos_722_;
v_cPos_x3f_701_ = v_cPos_x3f_723_;
v_id_x3f_702_ = v_id_x3f_724_;
v___y_703_ = v___x_733_;
goto v___jp_699_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_734_ = lean_string_utf8_byte_size(v_uri_721_);
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_734_, v_uri_721_, v___x_735_, v_acc_730_);
v___x_737_ = lean_string_append(v___x_736_, v___x_729_);
lean_inc(v_id_x3f_724_);
lean_inc(v_cPos_x3f_723_);
lean_inc_ref(v_pos_722_);
v_pos_700_ = v_pos_722_;
v_cPos_x3f_701_ = v_cPos_x3f_723_;
v_id_x3f_702_ = v_id_x3f_724_;
v___y_703_ = v___x_737_;
goto v___jp_699_;
}
}
else
{
v_acc_650_ = v_acc_718_;
goto v___jp_649_;
}
}
v___jp_738_:
{
lean_object* v_sortText_x3f_740_; 
v_sortText_x3f_740_ = lean_ctor_get(v___x_648_, 5);
if (lean_obj_tag(v_sortText_x3f_740_) == 1)
{
lean_object* v_val_741_; lean_object* v___x_742_; lean_object* v_acc_743_; lean_object* v___x_744_; lean_object* v_acc_745_; uint8_t v___x_746_; 
v_val_741_ = lean_ctor_get(v_sortText_x3f_740_, 0);
v___x_742_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2));
v_acc_743_ = lean_string_append(v_acc_739_, v___x_742_);
v___x_744_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_745_ = lean_string_append(v_acc_743_, v___x_744_);
v___x_746_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_741_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_string_append(v_acc_745_, v_val_741_);
v___x_748_ = lean_string_append(v___x_747_, v___x_744_);
v_acc_718_ = v___x_748_;
goto v___jp_717_;
}
else
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_749_ = lean_string_utf8_byte_size(v_val_741_);
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_749_, v_val_741_, v___x_750_, v_acc_745_);
v___x_752_ = lean_string_append(v___x_751_, v___x_744_);
v_acc_718_ = v___x_752_;
goto v___jp_717_;
}
}
else
{
v_acc_718_ = v_acc_739_;
goto v___jp_717_;
}
}
v___jp_753_:
{
lean_object* v_textEdit_x3f_755_; 
v_textEdit_x3f_755_ = lean_ctor_get(v___x_648_, 4);
if (lean_obj_tag(v_textEdit_x3f_755_) == 1)
{
lean_object* v_val_756_; lean_object* v_insert_757_; lean_object* v_end_758_; lean_object* v_start_759_; lean_object* v_replace_760_; lean_object* v_end_761_; lean_object* v_start_762_; lean_object* v_newText_763_; lean_object* v_line_764_; lean_object* v_character_765_; lean_object* v_line_766_; lean_object* v_character_767_; lean_object* v_line_768_; lean_object* v_character_769_; lean_object* v_line_770_; lean_object* v_character_771_; lean_object* v___x_772_; lean_object* v_acc_773_; lean_object* v___x_774_; lean_object* v_acc_775_; lean_object* v___x_776_; lean_object* v_acc_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v_acc_787_; lean_object* v___x_788_; lean_object* v_acc_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_acc_796_; lean_object* v_acc_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v_acc_802_; lean_object* v___x_803_; lean_object* v_acc_804_; lean_object* v_acc_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v_acc_812_; lean_object* v_acc_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_acc_820_; lean_object* v_acc_821_; lean_object* v_acc_822_; 
v_val_756_ = lean_ctor_get(v_textEdit_x3f_755_, 0);
v_insert_757_ = lean_ctor_get(v_val_756_, 1);
v_end_758_ = lean_ctor_get(v_insert_757_, 1);
v_start_759_ = lean_ctor_get(v_insert_757_, 0);
v_replace_760_ = lean_ctor_get(v_val_756_, 2);
v_end_761_ = lean_ctor_get(v_replace_760_, 1);
v_start_762_ = lean_ctor_get(v_replace_760_, 0);
v_newText_763_ = lean_ctor_get(v_val_756_, 0);
v_line_764_ = lean_ctor_get(v_end_758_, 0);
v_character_765_ = lean_ctor_get(v_end_758_, 1);
v_line_766_ = lean_ctor_get(v_start_759_, 0);
v_character_767_ = lean_ctor_get(v_start_759_, 1);
v_line_768_ = lean_ctor_get(v_end_761_, 0);
v_character_769_ = lean_ctor_get(v_end_761_, 1);
v_line_770_ = lean_ctor_get(v_start_762_, 0);
v_character_771_ = lean_ctor_get(v_start_762_, 1);
v___x_772_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3));
v_acc_773_ = lean_string_append(v_acc_754_, v___x_772_);
v___x_774_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
v_acc_775_ = lean_string_append(v_acc_773_, v___x_774_);
v___x_776_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
v_acc_777_ = lean_string_append(v_acc_775_, v___x_776_);
v___x_778_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_779_ = lean_string_append(v_acc_777_, v___x_778_);
lean_inc(v_character_765_);
v___x_780_ = l_Nat_reprFast(v_character_765_);
v___x_781_ = lean_string_append(v___x_779_, v___x_780_);
lean_dec_ref(v___x_780_);
v___x_782_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_783_ = lean_string_append(v___x_781_, v___x_782_);
lean_inc(v_line_764_);
v___x_784_ = l_Nat_reprFast(v_line_764_);
v___x_785_ = lean_string_append(v___x_783_, v___x_784_);
lean_dec_ref(v___x_784_);
v___x_786_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v_acc_787_ = lean_string_append(v___x_785_, v___x_786_);
v___x_788_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
v_acc_789_ = lean_string_append(v_acc_787_, v___x_788_);
v___x_790_ = lean_string_append(v_acc_789_, v___x_778_);
lean_inc(v_character_767_);
v___x_791_ = l_Nat_reprFast(v_character_767_);
v___x_792_ = lean_string_append(v___x_790_, v___x_791_);
lean_dec_ref(v___x_791_);
v___x_793_ = lean_string_append(v___x_792_, v___x_782_);
lean_inc(v_line_766_);
v___x_794_ = l_Nat_reprFast(v_line_766_);
v___x_795_ = lean_string_append(v___x_793_, v___x_794_);
lean_dec_ref(v___x_794_);
v_acc_796_ = lean_string_append(v___x_795_, v___x_786_);
v_acc_797_ = lean_string_append(v_acc_796_, v___x_786_);
v___x_798_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
v___x_799_ = lean_string_append(v_acc_797_, v___x_798_);
v___x_800_ = lean_string_append(v___x_799_, v_newText_763_);
v___x_801_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_802_ = lean_string_append(v___x_800_, v___x_801_);
v___x_803_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
v_acc_804_ = lean_string_append(v_acc_802_, v___x_803_);
v_acc_805_ = lean_string_append(v_acc_804_, v___x_776_);
v___x_806_ = lean_string_append(v_acc_805_, v___x_778_);
lean_inc(v_character_769_);
v___x_807_ = l_Nat_reprFast(v_character_769_);
v___x_808_ = lean_string_append(v___x_806_, v___x_807_);
lean_dec_ref(v___x_807_);
v___x_809_ = lean_string_append(v___x_808_, v___x_782_);
lean_inc(v_line_768_);
v___x_810_ = l_Nat_reprFast(v_line_768_);
v___x_811_ = lean_string_append(v___x_809_, v___x_810_);
lean_dec_ref(v___x_810_);
v_acc_812_ = lean_string_append(v___x_811_, v___x_786_);
v_acc_813_ = lean_string_append(v_acc_812_, v___x_788_);
v___x_814_ = lean_string_append(v_acc_813_, v___x_778_);
lean_inc(v_character_771_);
v___x_815_ = l_Nat_reprFast(v_character_771_);
v___x_816_ = lean_string_append(v___x_814_, v___x_815_);
lean_dec_ref(v___x_815_);
v___x_817_ = lean_string_append(v___x_816_, v___x_782_);
lean_inc(v_line_770_);
v___x_818_ = l_Nat_reprFast(v_line_770_);
v___x_819_ = lean_string_append(v___x_817_, v___x_818_);
lean_dec_ref(v___x_818_);
v_acc_820_ = lean_string_append(v___x_819_, v___x_786_);
v_acc_821_ = lean_string_append(v_acc_820_, v___x_786_);
v_acc_822_ = lean_string_append(v_acc_821_, v___x_786_);
v_acc_739_ = v_acc_822_;
goto v___jp_738_;
}
else
{
v_acc_739_ = v_acc_754_;
goto v___jp_738_;
}
}
v___jp_823_:
{
lean_object* v_kind_x3f_825_; 
v_kind_x3f_825_ = lean_ctor_get(v___x_648_, 3);
if (lean_obj_tag(v_kind_x3f_825_) == 1)
{
lean_object* v_val_826_; lean_object* v___x_827_; lean_object* v___x_828_; uint8_t v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_acc_834_; 
v_val_826_ = lean_ctor_get(v_kind_x3f_825_, 0);
v___x_827_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4));
v___x_828_ = lean_string_append(v_acc_824_, v___x_827_);
v___x_829_ = lean_unbox(v_val_826_);
v___x_830_ = l_Lean_Lsp_CompletionItemKind_ctorIdx(v___x_829_);
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_add(v___x_830_, v___x_831_);
lean_dec(v___x_830_);
v___x_833_ = l_Nat_reprFast(v___x_832_);
v_acc_834_ = lean_string_append(v___x_828_, v___x_833_);
lean_dec_ref(v___x_833_);
v_acc_754_ = v_acc_834_;
goto v___jp_753_;
}
else
{
v_acc_754_ = v_acc_824_;
goto v___jp_753_;
}
}
v___jp_835_:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_838_ = lean_string_append(v___y_836_, v___x_837_);
v_acc_824_ = v___x_838_;
goto v___jp_823_;
}
v___jp_839_:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v_acc_847_; lean_object* v___x_848_; lean_object* v_acc_849_; uint8_t v___x_850_; 
v___x_843_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
v___x_844_ = lean_string_append(v___y_841_, v___x_843_);
v___x_845_ = lean_string_append(v___x_844_, v___y_842_);
v___x_846_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
v_acc_847_ = lean_string_append(v___x_845_, v___x_846_);
v___x_848_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_849_ = lean_string_append(v_acc_847_, v___x_848_);
v___x_850_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_840_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_string_append(v_acc_849_, v_value_840_);
lean_dec_ref(v_value_840_);
v___x_852_ = lean_string_append(v___x_851_, v___x_848_);
v___y_836_ = v___x_852_;
goto v___jp_835_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = lean_string_utf8_byte_size(v_value_840_);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_853_, v_value_840_, v___x_854_, v_acc_849_);
lean_dec_ref(v_value_840_);
v___x_856_ = lean_string_append(v___x_855_, v___x_848_);
v___y_836_ = v___x_856_;
goto v___jp_835_;
}
}
v___jp_857_:
{
lean_object* v_documentation_x3f_859_; 
v_documentation_x3f_859_ = lean_ctor_get(v___x_648_, 2);
if (lean_obj_tag(v_documentation_x3f_859_) == 1)
{
lean_object* v_val_860_; uint8_t v_kind_861_; lean_object* v_value_862_; lean_object* v___x_863_; lean_object* v_acc_864_; 
v_val_860_ = lean_ctor_get(v_documentation_x3f_859_, 0);
v_kind_861_ = lean_ctor_get_uint8(v_val_860_, sizeof(void*)*1);
v_value_862_ = lean_ctor_get(v_val_860_, 0);
v___x_863_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5));
v_acc_864_ = lean_string_append(v_acc_858_, v___x_863_);
if (v_kind_861_ == 0)
{
lean_object* v___x_865_; 
v___x_865_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
lean_inc_ref(v_value_862_);
v_value_840_ = v_value_862_;
v___y_841_ = v_acc_864_;
v___y_842_ = v___x_865_;
goto v___jp_839_;
}
else
{
lean_object* v___x_866_; 
v___x_866_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
lean_inc_ref(v_value_862_);
v_value_840_ = v_value_862_;
v___y_841_ = v_acc_864_;
v___y_842_ = v___x_866_;
goto v___jp_839_;
}
}
else
{
v_acc_824_ = v_acc_858_;
goto v___jp_823_;
}
}
v___jp_867_:
{
lean_object* v_detail_x3f_869_; 
v_detail_x3f_869_ = lean_ctor_get(v___x_648_, 1);
if (lean_obj_tag(v_detail_x3f_869_) == 1)
{
lean_object* v_val_870_; lean_object* v___x_871_; lean_object* v_acc_872_; lean_object* v___x_873_; lean_object* v_acc_874_; uint8_t v___x_875_; 
v_val_870_ = lean_ctor_get(v_detail_x3f_869_, 0);
v___x_871_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6));
v_acc_872_ = lean_string_append(v___y_868_, v___x_871_);
v___x_873_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_874_ = lean_string_append(v_acc_872_, v___x_873_);
v___x_875_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_870_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_string_append(v_acc_874_, v_val_870_);
v___x_877_ = lean_string_append(v___x_876_, v___x_873_);
v_acc_858_ = v___x_877_;
goto v___jp_857_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_878_ = lean_string_utf8_byte_size(v_val_870_);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_878_, v_val_870_, v___x_879_, v_acc_874_);
v___x_881_ = lean_string_append(v___x_880_, v___x_873_);
v_acc_858_ = v___x_881_;
goto v___jp_857_;
}
}
else
{
v_acc_858_ = v___y_868_;
goto v___jp_857_;
}
}
}
v___jp_628_:
{
lean_object* v___x_631_; 
v___x_631_ = lean_nat_add(v_i_627_, v___y_629_);
lean_dec(v_i_627_);
v_acc_625_ = v___y_630_;
v_i_627_ = v___x_631_;
goto _start;
}
v___jp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_636_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_637_ = lean_string_append(v_acc_635_, v___x_636_);
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = lean_nat_sub(v___x_633_, v___x_638_);
v___x_640_ = lean_nat_dec_lt(v_i_627_, v___x_639_);
lean_dec(v___x_639_);
if (v___x_640_ == 0)
{
v___y_629_ = v___x_638_;
v___y_630_ = v___x_637_;
goto v___jp_628_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_642_ = lean_string_append(v___x_637_, v___x_641_);
v___y_629_ = v___x_638_;
v___y_630_ = v___x_642_;
goto v___jp_628_;
}
}
v___jp_643_:
{
lean_object* v___x_645_; lean_object* v_acc_646_; 
v___x_645_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v_acc_646_ = lean_string_append(v_acc_644_, v___x_645_);
v_acc_635_ = v_acc_646_;
goto v___jp_634_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast___boxed(lean_object* v_acc_894_, lean_object* v_items_895_, lean_object* v_i_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(v_acc_894_, v_items_895_, v_i_896_);
lean_dec_ref(v_items_895_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(lean_object* v___x_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v_inst_901_, lean_object* v_R_902_, lean_object* v_a_903_, lean_object* v_b_904_, lean_object* v_c_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_899_, v___x_900_, v_a_903_, v_b_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___boxed(lean_object* v___x_907_, lean_object* v___x_908_, lean_object* v___x_909_, lean_object* v_inst_910_, lean_object* v_R_911_, lean_object* v_a_912_, lean_object* v_b_913_, lean_object* v_c_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(v___x_907_, v___x_908_, v___x_909_, v_inst_910_, v_R_911_, v_a_912_, v_b_913_, v_c_914_);
lean_dec_ref(v___x_909_);
lean_dec(v___x_908_);
lean_dec_ref(v___x_907_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast(lean_object* v_l_921_){
_start:
{
uint8_t v_isIncomplete_922_; lean_object* v_items_923_; lean_object* v___x_924_; lean_object* v___y_926_; 
v_isIncomplete_922_ = lean_ctor_get_uint8(v_l_921_, sizeof(void*)*1);
v_items_923_ = lean_ctor_get(v_l_921_, 0);
v___x_924_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0));
if (v_isIncomplete_922_ == 0)
{
lean_object* v___x_934_; 
v___x_934_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3));
v___y_926_ = v___x_934_;
goto v___jp_925_;
}
else
{
lean_object* v___x_935_; 
v___x_935_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4));
v___y_926_ = v___x_935_;
goto v___jp_925_;
}
v___jp_925_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v_acc_929_; lean_object* v___x_930_; lean_object* v_acc_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_927_ = lean_string_append(v___x_924_, v___y_926_);
v___x_928_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1));
v_acc_929_ = lean_string_append(v___x_927_, v___x_928_);
v___x_930_ = lean_unsigned_to_nat(0u);
v_acc_931_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(v_acc_929_, v_items_923_, v___x_930_);
v___x_932_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2));
v___x_933_ = lean_string_append(v_acc_931_, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___boxed(lean_object* v_l_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Lsp_ResolvableCompletionList_compressFast(v_l_936_);
lean_dec_ref(v_l_936_);
return v_res_937_;
}
}
lean_object* runtime_initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Completion_CompletionItemCompression(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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

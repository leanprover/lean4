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
lean_dec_ref_known(v___x_117_, 3);
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
lean_dec_ref_known(v___x_76_, 3);
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
lean_dec_ref_known(v_val_64_, 1);
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
lean_dec_ref_known(v___x_89_, 3);
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
lean_dec_ref_known(v_cPos_x3f_59_, 1);
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
lean_dec_ref_known(v___x_167_, 3);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(lean_object* v_acc_291_, lean_object* v_tags_292_, lean_object* v_i_293_){
_start:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_array_get_size(v_tags_292_);
v___x_295_ = lean_nat_dec_lt(v_i_293_, v___x_294_);
if (v___x_295_ == 0)
{
lean_dec(v_i_293_);
return v_acc_291_;
}
else
{
lean_object* v___x_296_; lean_object* v___y_298_; lean_object* v___x_301_; lean_object* v_acc_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_301_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0));
v_acc_302_ = lean_string_append(v_acc_291_, v___x_301_);
v___x_303_ = lean_nat_sub(v___x_294_, v___x_296_);
v___x_304_ = lean_nat_dec_lt(v_i_293_, v___x_303_);
lean_dec(v___x_303_);
if (v___x_304_ == 0)
{
v___y_298_ = v_acc_302_;
goto v___jp_297_;
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_306_ = lean_string_append(v_acc_302_, v___x_305_);
v___y_298_ = v___x_306_;
goto v___jp_297_;
}
v___jp_297_:
{
lean_object* v___x_299_; 
v___x_299_ = lean_nat_add(v_i_293_, v___x_296_);
lean_dec(v_i_293_);
v_acc_291_ = v___y_298_;
v_i_293_ = v___x_299_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___boxed(lean_object* v_acc_307_, lean_object* v_tags_308_, lean_object* v_i_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_307_, v_tags_308_, v_i_309_);
lean_dec_ref(v_tags_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(lean_object* v___x_311_, lean_object* v_val_312_, lean_object* v_it_313_, lean_object* v_acc_314_, lean_object* v_hP_315_, lean_object* v_recur_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = lean_nat_dec_eq(v_it_313_, v___x_311_);
if (v___x_317_ == 0)
{
uint32_t v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_318_ = lean_string_utf8_get_fast(v_val_312_, v_it_313_);
v___x_319_ = lean_string_utf8_next_fast(v_val_312_, v_it_313_);
v___x_320_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_314_, v___x_318_);
v___x_321_ = lean_apply_4(v_recur_316_, v___x_319_, v___x_320_, lean_box(0), lean_box(0));
return v___x_321_;
}
else
{
lean_dec_ref(v_recur_316_);
return v_acc_314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed(lean_object* v___x_322_, lean_object* v_val_323_, lean_object* v_it_324_, lean_object* v_acc_325_, lean_object* v_hP_326_, lean_object* v_recur_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3(v___x_322_, v_val_323_, v_it_324_, v_acc_325_, v_hP_326_, v_recur_327_);
lean_dec(v_it_324_);
lean_dec_ref(v_val_323_);
lean_dec(v___x_322_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(lean_object* v___x_329_, lean_object* v_label_330_, lean_object* v_it_331_, lean_object* v_acc_332_, lean_object* v_hP_333_, lean_object* v_recur_334_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = lean_nat_dec_eq(v_it_331_, v___x_329_);
if (v___x_335_ == 0)
{
uint32_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_336_ = lean_string_utf8_get_fast(v_label_330_, v_it_331_);
v___x_337_ = lean_string_utf8_next_fast(v_label_330_, v_it_331_);
v___x_338_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_acc_332_, v___x_336_);
v___x_339_ = lean_apply_4(v_recur_334_, v___x_337_, v___x_338_, lean_box(0), lean_box(0));
return v___x_339_;
}
else
{
lean_dec_ref(v_recur_334_);
return v_acc_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed(lean_object* v___x_340_, lean_object* v_label_341_, lean_object* v_it_342_, lean_object* v_acc_343_, lean_object* v_hP_344_, lean_object* v_recur_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2(v___x_340_, v_label_341_, v_it_342_, v_acc_343_, v_hP_344_, v_recur_345_);
lean_dec(v_it_342_);
lean_dec_ref(v_label_341_);
lean_dec(v___x_340_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast(lean_object* v_acc_355_, lean_object* v_item_356_){
_start:
{
lean_object* v_acc_358_; lean_object* v_acc_362_; lean_object* v_label_365_; lean_object* v_detail_x3f_366_; lean_object* v_documentation_x3f_367_; lean_object* v_kind_x3f_368_; lean_object* v_textEdit_x3f_369_; lean_object* v_sortText_x3f_370_; lean_object* v_data_x3f_371_; lean_object* v_tags_x3f_372_; lean_object* v_acc_374_; lean_object* v_acc_387_; lean_object* v___y_391_; lean_object* v___y_395_; lean_object* v___y_399_; lean_object* v_id_x3f_400_; lean_object* v_acc_401_; lean_object* v_pos_431_; lean_object* v_cPos_x3f_432_; lean_object* v_id_x3f_433_; lean_object* v___y_434_; lean_object* v_acc_449_; lean_object* v_acc_472_; lean_object* v_acc_489_; lean_object* v_acc_558_; lean_object* v___y_569_; lean_object* v_value_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v_acc_594_; lean_object* v___y_603_; lean_object* v___x_619_; lean_object* v_acc_620_; lean_object* v___x_621_; lean_object* v_acc_622_; uint8_t v___x_623_; 
v_label_365_ = lean_ctor_get(v_item_356_, 0);
lean_inc_ref(v_label_365_);
v_detail_x3f_366_ = lean_ctor_get(v_item_356_, 1);
lean_inc(v_detail_x3f_366_);
v_documentation_x3f_367_ = lean_ctor_get(v_item_356_, 2);
lean_inc(v_documentation_x3f_367_);
v_kind_x3f_368_ = lean_ctor_get(v_item_356_, 3);
lean_inc(v_kind_x3f_368_);
v_textEdit_x3f_369_ = lean_ctor_get(v_item_356_, 4);
lean_inc(v_textEdit_x3f_369_);
v_sortText_x3f_370_ = lean_ctor_get(v_item_356_, 5);
lean_inc(v_sortText_x3f_370_);
v_data_x3f_371_ = lean_ctor_get(v_item_356_, 6);
lean_inc(v_data_x3f_371_);
v_tags_x3f_372_ = lean_ctor_get(v_item_356_, 7);
lean_inc(v_tags_x3f_372_);
lean_dec_ref(v_item_356_);
v___x_619_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7));
v_acc_620_ = lean_string_append(v_acc_355_, v___x_619_);
v___x_621_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_622_ = lean_string_append(v_acc_620_, v___x_621_);
v___x_623_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_label_365_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_string_append(v_acc_622_, v_label_365_);
lean_dec_ref(v_label_365_);
v___x_625_ = lean_string_append(v___x_624_, v___x_621_);
v___y_603_ = v___x_625_;
goto v___jp_602_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___f_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_string_utf8_byte_size(v_label_365_);
lean_inc_ref(v_label_365_);
v___f_628_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__2___boxed), 6, 2);
lean_closure_set(v___f_628_, 0, v___x_627_);
lean_closure_set(v___f_628_, 1, v_label_365_);
v___x_629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_629_, 0, v_label_365_);
lean_ctor_set(v___x_629_, 1, v___x_626_);
lean_ctor_set(v___x_629_, 2, v___x_627_);
v___x_630_ = l_String_Slice_positions(v___x_629_);
lean_dec_ref_known(v___x_629_, 3);
v___x_631_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_628_, v___x_630_, v_acc_622_, lean_box(0));
v___x_632_ = lean_string_append(v___x_631_, v___x_621_);
v___y_603_ = v___x_632_;
goto v___jp_602_;
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_360_ = lean_string_append(v_acc_358_, v___x_359_);
return v___x_360_;
}
v___jp_361_:
{
lean_object* v___x_363_; lean_object* v_acc_364_; 
v___x_363_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v_acc_364_ = lean_string_append(v_acc_362_, v___x_363_);
v_acc_358_ = v_acc_364_;
goto v___jp_357_;
}
v___jp_373_:
{
if (lean_obj_tag(v_tags_x3f_372_) == 1)
{
lean_object* v_val_375_; lean_object* v___x_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_val_375_ = lean_ctor_get(v_tags_x3f_372_, 0);
lean_inc(v_val_375_);
lean_dec_ref_known(v_tags_x3f_372_, 1);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_array_get_size(v_val_375_);
v___x_378_ = lean_nat_dec_lt(v___x_376_, v___x_377_);
if (v___x_378_ == 0)
{
lean_dec(v_val_375_);
v_acc_358_ = v_acc_374_;
goto v___jp_357_;
}
else
{
lean_object* v___x_379_; lean_object* v_acc_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0));
v_acc_380_ = lean_string_append(v_acc_374_, v___x_379_);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_dec_eq(v___x_377_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v_acc_383_; 
v_acc_383_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_380_, v_val_375_, v___x_376_);
lean_dec(v_val_375_);
v_acc_362_ = v_acc_383_;
goto v___jp_361_;
}
else
{
lean_object* v___x_384_; lean_object* v_acc_385_; 
lean_dec(v_val_375_);
v___x_384_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0));
v_acc_385_ = lean_string_append(v_acc_380_, v___x_384_);
v_acc_362_ = v_acc_385_;
goto v___jp_361_;
}
}
}
else
{
lean_dec(v_tags_x3f_372_);
v_acc_358_ = v_acc_374_;
goto v___jp_357_;
}
}
v___jp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v___x_389_ = lean_string_append(v_acc_387_, v___x_388_);
v_acc_374_ = v___x_389_;
goto v___jp_373_;
}
v___jp_390_:
{
lean_object* v___x_392_; lean_object* v_acc_393_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_393_ = lean_string_append(v___y_391_, v___x_392_);
v_acc_387_ = v_acc_393_;
goto v___jp_386_;
}
v___jp_394_:
{
lean_object* v___x_396_; lean_object* v_acc_397_; 
v___x_396_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_397_ = lean_string_append(v___y_395_, v___x_396_);
v_acc_387_ = v_acc_397_;
goto v___jp_386_;
}
v___jp_398_:
{
if (lean_obj_tag(v_id_x3f_400_) == 1)
{
lean_object* v_val_402_; lean_object* v_acc_403_; 
v_val_402_ = lean_ctor_get(v_id_x3f_400_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v_id_x3f_400_, 1);
v_acc_403_ = lean_string_append(v_acc_401_, v___y_399_);
if (lean_obj_tag(v_val_402_) == 0)
{
lean_object* v_declName_404_; lean_object* v___x_405_; lean_object* v_acc_406_; uint8_t v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_declName_404_ = lean_ctor_get(v_val_402_, 0);
lean_inc(v_declName_404_);
lean_dec_ref_known(v_val_402_, 1);
v___x_405_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2));
v_acc_406_ = lean_string_append(v_acc_403_, v___x_405_);
v___x_407_ = 1;
v___x_408_ = l_Lean_Name_toString(v_declName_404_, v___x_407_);
v___x_409_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_string_append(v_acc_406_, v___x_408_);
lean_dec_ref(v___x_408_);
v___y_395_ = v___x_410_;
goto v___jp_394_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_string_utf8_byte_size(v___x_408_);
lean_inc_ref(v___x_408_);
v___f_413_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_413_, 0, v___x_412_);
lean_closure_set(v___f_413_, 1, v___x_408_);
v___x_414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_414_, 0, v___x_408_);
lean_ctor_set(v___x_414_, 1, v___x_411_);
lean_ctor_set(v___x_414_, 2, v___x_412_);
v___x_415_ = l_String_Slice_positions(v___x_414_);
lean_dec_ref_known(v___x_414_, 3);
v___x_416_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_413_, v___x_415_, v_acc_406_, lean_box(0));
v___y_395_ = v___x_416_;
goto v___jp_394_;
}
}
else
{
lean_object* v_id_417_; lean_object* v___x_418_; lean_object* v_acc_419_; uint8_t v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_id_417_ = lean_ctor_get(v_val_402_, 0);
lean_inc(v_id_417_);
lean_dec_ref_known(v_val_402_, 1);
v___x_418_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
v_acc_419_ = lean_string_append(v_acc_403_, v___x_418_);
v___x_420_ = 1;
v___x_421_ = l_Lean_Name_toString(v_id_417_, v___x_420_);
v___x_422_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_string_append(v_acc_419_, v___x_421_);
lean_dec_ref(v___x_421_);
v___y_391_ = v___x_423_;
goto v___jp_390_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___f_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = lean_string_utf8_byte_size(v___x_421_);
lean_inc_ref(v___x_421_);
v___f_426_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_426_, 0, v___x_425_);
lean_closure_set(v___f_426_, 1, v___x_421_);
v___x_427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_427_, 0, v___x_421_);
lean_ctor_set(v___x_427_, 1, v___x_424_);
lean_ctor_set(v___x_427_, 2, v___x_425_);
v___x_428_ = l_String_Slice_positions(v___x_427_);
lean_dec_ref_known(v___x_427_, 3);
v___x_429_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_426_, v___x_428_, v_acc_419_, lean_box(0));
v___y_391_ = v___x_429_;
goto v___jp_390_;
}
}
}
else
{
lean_dec(v_id_x3f_400_);
v_acc_387_ = v_acc_401_;
goto v___jp_386_;
}
}
v___jp_430_:
{
lean_object* v_line_435_; lean_object* v_character_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v_acc_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_acc_443_; 
v_line_435_ = lean_ctor_get(v_pos_431_, 0);
lean_inc(v_line_435_);
v_character_436_ = lean_ctor_get(v_pos_431_, 1);
lean_inc(v_character_436_);
lean_dec_ref(v_pos_431_);
v___x_437_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_438_ = lean_string_append(v___y_434_, v___x_437_);
v___x_439_ = l_Nat_reprFast(v_line_435_);
v_acc_440_ = lean_string_append(v___x_438_, v___x_439_);
lean_dec_ref(v___x_439_);
v___x_441_ = lean_string_append(v_acc_440_, v___x_437_);
v___x_442_ = l_Nat_reprFast(v_character_436_);
v_acc_443_ = lean_string_append(v___x_441_, v___x_442_);
lean_dec_ref(v___x_442_);
if (lean_obj_tag(v_cPos_x3f_432_) == 1)
{
lean_object* v_val_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v_acc_447_; 
v_val_444_ = lean_ctor_get(v_cPos_x3f_432_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v_cPos_x3f_432_, 1);
v___x_445_ = lean_string_append(v_acc_443_, v___x_437_);
v___x_446_ = l_Nat_reprFast(v_val_444_);
v_acc_447_ = lean_string_append(v___x_445_, v___x_446_);
lean_dec_ref(v___x_446_);
v___y_399_ = v___x_437_;
v_id_x3f_400_ = v_id_x3f_433_;
v_acc_401_ = v_acc_447_;
goto v___jp_398_;
}
else
{
lean_dec(v_cPos_x3f_432_);
v___y_399_ = v___x_437_;
v_id_x3f_400_ = v_id_x3f_433_;
v_acc_401_ = v_acc_443_;
goto v___jp_398_;
}
}
v___jp_448_:
{
if (lean_obj_tag(v_data_x3f_371_) == 1)
{
lean_object* v_val_450_; lean_object* v_uri_451_; lean_object* v_pos_452_; lean_object* v_cPos_x3f_453_; lean_object* v_id_x3f_454_; lean_object* v___x_455_; lean_object* v_acc_456_; lean_object* v___x_457_; lean_object* v_acc_458_; lean_object* v___x_459_; lean_object* v_acc_460_; uint8_t v___x_461_; 
v_val_450_ = lean_ctor_get(v_data_x3f_371_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v_data_x3f_371_, 1);
v_uri_451_ = lean_ctor_get(v_val_450_, 0);
lean_inc_ref(v_uri_451_);
v_pos_452_ = lean_ctor_get(v_val_450_, 1);
lean_inc_ref(v_pos_452_);
v_cPos_x3f_453_ = lean_ctor_get(v_val_450_, 2);
lean_inc(v_cPos_x3f_453_);
v_id_x3f_454_ = lean_ctor_get(v_val_450_, 3);
lean_inc(v_id_x3f_454_);
lean_dec(v_val_450_);
v___x_455_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1));
v_acc_456_ = lean_string_append(v_acc_449_, v___x_455_);
v___x_457_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
v_acc_458_ = lean_string_append(v_acc_456_, v___x_457_);
v___x_459_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_460_ = lean_string_append(v_acc_458_, v___x_459_);
v___x_461_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_451_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = lean_string_append(v_acc_460_, v_uri_451_);
lean_dec_ref(v_uri_451_);
v___x_463_ = lean_string_append(v___x_462_, v___x_459_);
v_pos_431_ = v_pos_452_;
v_cPos_x3f_432_ = v_cPos_x3f_453_;
v_id_x3f_433_ = v_id_x3f_454_;
v___y_434_ = v___x_463_;
goto v___jp_430_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___f_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_string_utf8_byte_size(v_uri_451_);
lean_inc_ref(v_uri_451_);
v___f_466_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___lam__2___boxed), 6, 2);
lean_closure_set(v___f_466_, 0, v___x_465_);
lean_closure_set(v___f_466_, 1, v_uri_451_);
v___x_467_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_467_, 0, v_uri_451_);
lean_ctor_set(v___x_467_, 1, v___x_464_);
lean_ctor_set(v___x_467_, 2, v___x_465_);
v___x_468_ = l_String_Slice_positions(v___x_467_);
lean_dec_ref_known(v___x_467_, 3);
v___x_469_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_466_, v___x_468_, v_acc_460_, lean_box(0));
v___x_470_ = lean_string_append(v___x_469_, v___x_459_);
v_pos_431_ = v_pos_452_;
v_cPos_x3f_432_ = v_cPos_x3f_453_;
v_id_x3f_433_ = v_id_x3f_454_;
v___y_434_ = v___x_470_;
goto v___jp_430_;
}
}
else
{
lean_dec(v_data_x3f_371_);
v_acc_374_ = v_acc_449_;
goto v___jp_373_;
}
}
v___jp_471_:
{
if (lean_obj_tag(v_sortText_x3f_370_) == 1)
{
lean_object* v_val_473_; lean_object* v___x_474_; lean_object* v_acc_475_; lean_object* v___x_476_; lean_object* v_acc_477_; uint8_t v___x_478_; 
v_val_473_ = lean_ctor_get(v_sortText_x3f_370_, 0);
lean_inc(v_val_473_);
lean_dec_ref_known(v_sortText_x3f_370_, 1);
v___x_474_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2));
v_acc_475_ = lean_string_append(v_acc_472_, v___x_474_);
v___x_476_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_477_ = lean_string_append(v_acc_475_, v___x_476_);
v___x_478_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_473_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_string_append(v_acc_477_, v_val_473_);
lean_dec(v_val_473_);
v___x_480_ = lean_string_append(v___x_479_, v___x_476_);
v_acc_449_ = v___x_480_;
goto v___jp_448_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = lean_string_utf8_byte_size(v_val_473_);
lean_inc(v_val_473_);
v___f_483_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed), 6, 2);
lean_closure_set(v___f_483_, 0, v___x_482_);
lean_closure_set(v___f_483_, 1, v_val_473_);
v___x_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_484_, 0, v_val_473_);
lean_ctor_set(v___x_484_, 1, v___x_481_);
lean_ctor_set(v___x_484_, 2, v___x_482_);
v___x_485_ = l_String_Slice_positions(v___x_484_);
lean_dec_ref_known(v___x_484_, 3);
v___x_486_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_483_, v___x_485_, v_acc_477_, lean_box(0));
v___x_487_ = lean_string_append(v___x_486_, v___x_476_);
v_acc_449_ = v___x_487_;
goto v___jp_448_;
}
}
else
{
lean_dec(v_sortText_x3f_370_);
v_acc_449_ = v_acc_472_;
goto v___jp_448_;
}
}
v___jp_488_:
{
if (lean_obj_tag(v_textEdit_x3f_369_) == 1)
{
lean_object* v_val_490_; lean_object* v_insert_491_; lean_object* v_end_492_; lean_object* v_start_493_; lean_object* v_replace_494_; lean_object* v_end_495_; lean_object* v_start_496_; lean_object* v_newText_497_; lean_object* v_line_498_; lean_object* v_character_499_; lean_object* v_line_500_; lean_object* v_character_501_; lean_object* v_line_502_; lean_object* v_character_503_; lean_object* v_line_504_; lean_object* v_character_505_; lean_object* v___x_506_; lean_object* v_acc_507_; lean_object* v___x_508_; lean_object* v_acc_509_; lean_object* v___x_510_; lean_object* v_acc_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v_acc_521_; lean_object* v___x_522_; lean_object* v_acc_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_acc_530_; lean_object* v_acc_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v_acc_536_; lean_object* v___x_537_; lean_object* v_acc_538_; lean_object* v_acc_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v_acc_546_; lean_object* v_acc_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v_acc_554_; lean_object* v_acc_555_; lean_object* v_acc_556_; 
v_val_490_ = lean_ctor_get(v_textEdit_x3f_369_, 0);
lean_inc(v_val_490_);
lean_dec_ref_known(v_textEdit_x3f_369_, 1);
v_insert_491_ = lean_ctor_get(v_val_490_, 1);
v_end_492_ = lean_ctor_get(v_insert_491_, 1);
lean_inc_ref(v_end_492_);
v_start_493_ = lean_ctor_get(v_insert_491_, 0);
lean_inc_ref(v_start_493_);
v_replace_494_ = lean_ctor_get(v_val_490_, 2);
v_end_495_ = lean_ctor_get(v_replace_494_, 1);
lean_inc_ref(v_end_495_);
v_start_496_ = lean_ctor_get(v_replace_494_, 0);
lean_inc_ref(v_start_496_);
v_newText_497_ = lean_ctor_get(v_val_490_, 0);
lean_inc_ref(v_newText_497_);
lean_dec(v_val_490_);
v_line_498_ = lean_ctor_get(v_end_492_, 0);
lean_inc(v_line_498_);
v_character_499_ = lean_ctor_get(v_end_492_, 1);
lean_inc(v_character_499_);
lean_dec_ref(v_end_492_);
v_line_500_ = lean_ctor_get(v_start_493_, 0);
lean_inc(v_line_500_);
v_character_501_ = lean_ctor_get(v_start_493_, 1);
lean_inc(v_character_501_);
lean_dec_ref(v_start_493_);
v_line_502_ = lean_ctor_get(v_end_495_, 0);
lean_inc(v_line_502_);
v_character_503_ = lean_ctor_get(v_end_495_, 1);
lean_inc(v_character_503_);
lean_dec_ref(v_end_495_);
v_line_504_ = lean_ctor_get(v_start_496_, 0);
lean_inc(v_line_504_);
v_character_505_ = lean_ctor_get(v_start_496_, 1);
lean_inc(v_character_505_);
lean_dec_ref(v_start_496_);
v___x_506_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3));
v_acc_507_ = lean_string_append(v_acc_489_, v___x_506_);
v___x_508_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
v_acc_509_ = lean_string_append(v_acc_507_, v___x_508_);
v___x_510_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
v_acc_511_ = lean_string_append(v_acc_509_, v___x_510_);
v___x_512_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_513_ = lean_string_append(v_acc_511_, v___x_512_);
v___x_514_ = l_Nat_reprFast(v_character_499_);
v___x_515_ = lean_string_append(v___x_513_, v___x_514_);
lean_dec_ref(v___x_514_);
v___x_516_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_517_ = lean_string_append(v___x_515_, v___x_516_);
v___x_518_ = l_Nat_reprFast(v_line_498_);
v___x_519_ = lean_string_append(v___x_517_, v___x_518_);
lean_dec_ref(v___x_518_);
v___x_520_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v_acc_521_ = lean_string_append(v___x_519_, v___x_520_);
v___x_522_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
v_acc_523_ = lean_string_append(v_acc_521_, v___x_522_);
v___x_524_ = lean_string_append(v_acc_523_, v___x_512_);
v___x_525_ = l_Nat_reprFast(v_character_501_);
v___x_526_ = lean_string_append(v___x_524_, v___x_525_);
lean_dec_ref(v___x_525_);
v___x_527_ = lean_string_append(v___x_526_, v___x_516_);
v___x_528_ = l_Nat_reprFast(v_line_500_);
v___x_529_ = lean_string_append(v___x_527_, v___x_528_);
lean_dec_ref(v___x_528_);
v_acc_530_ = lean_string_append(v___x_529_, v___x_520_);
v_acc_531_ = lean_string_append(v_acc_530_, v___x_520_);
v___x_532_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
v___x_533_ = lean_string_append(v_acc_531_, v___x_532_);
v___x_534_ = lean_string_append(v___x_533_, v_newText_497_);
lean_dec_ref(v_newText_497_);
v___x_535_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_536_ = lean_string_append(v___x_534_, v___x_535_);
v___x_537_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
v_acc_538_ = lean_string_append(v_acc_536_, v___x_537_);
v_acc_539_ = lean_string_append(v_acc_538_, v___x_510_);
v___x_540_ = lean_string_append(v_acc_539_, v___x_512_);
v___x_541_ = l_Nat_reprFast(v_character_503_);
v___x_542_ = lean_string_append(v___x_540_, v___x_541_);
lean_dec_ref(v___x_541_);
v___x_543_ = lean_string_append(v___x_542_, v___x_516_);
v___x_544_ = l_Nat_reprFast(v_line_502_);
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
lean_dec_ref(v___x_544_);
v_acc_546_ = lean_string_append(v___x_545_, v___x_520_);
v_acc_547_ = lean_string_append(v_acc_546_, v___x_522_);
v___x_548_ = lean_string_append(v_acc_547_, v___x_512_);
v___x_549_ = l_Nat_reprFast(v_character_505_);
v___x_550_ = lean_string_append(v___x_548_, v___x_549_);
lean_dec_ref(v___x_549_);
v___x_551_ = lean_string_append(v___x_550_, v___x_516_);
v___x_552_ = l_Nat_reprFast(v_line_504_);
v___x_553_ = lean_string_append(v___x_551_, v___x_552_);
lean_dec_ref(v___x_552_);
v_acc_554_ = lean_string_append(v___x_553_, v___x_520_);
v_acc_555_ = lean_string_append(v_acc_554_, v___x_520_);
v_acc_556_ = lean_string_append(v_acc_555_, v___x_520_);
v_acc_472_ = v_acc_556_;
goto v___jp_471_;
}
else
{
lean_dec(v_textEdit_x3f_369_);
v_acc_472_ = v_acc_489_;
goto v___jp_471_;
}
}
v___jp_557_:
{
if (lean_obj_tag(v_kind_x3f_368_) == 1)
{
lean_object* v_val_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_acc_567_; 
v_val_559_ = lean_ctor_get(v_kind_x3f_368_, 0);
lean_inc(v_val_559_);
lean_dec_ref_known(v_kind_x3f_368_, 1);
v___x_560_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4));
v___x_561_ = lean_string_append(v_acc_558_, v___x_560_);
v___x_562_ = lean_unbox(v_val_559_);
lean_dec(v_val_559_);
v___x_563_ = l_Lean_Lsp_CompletionItemKind_ctorIdx(v___x_562_);
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = lean_nat_add(v___x_563_, v___x_564_);
lean_dec(v___x_563_);
v___x_566_ = l_Nat_reprFast(v___x_565_);
v_acc_567_ = lean_string_append(v___x_561_, v___x_566_);
lean_dec_ref(v___x_566_);
v_acc_489_ = v_acc_567_;
goto v___jp_488_;
}
else
{
lean_dec(v_kind_x3f_368_);
v_acc_489_ = v_acc_558_;
goto v___jp_488_;
}
}
v___jp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_571_ = lean_string_append(v___y_569_, v___x_570_);
v_acc_558_ = v___x_571_;
goto v___jp_557_;
}
v___jp_572_:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_acc_580_; lean_object* v___x_581_; lean_object* v_acc_582_; uint8_t v___x_583_; 
v___x_576_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
v___x_577_ = lean_string_append(v___y_574_, v___x_576_);
v___x_578_ = lean_string_append(v___x_577_, v___y_575_);
v___x_579_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
v_acc_580_ = lean_string_append(v___x_578_, v___x_579_);
v___x_581_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_582_ = lean_string_append(v_acc_580_, v___x_581_);
v___x_583_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_573_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_string_append(v_acc_582_, v_value_573_);
lean_dec_ref(v_value_573_);
v___x_585_ = lean_string_append(v___x_584_, v___x_581_);
v___y_569_ = v___x_585_;
goto v___jp_568_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_string_utf8_byte_size(v_value_573_);
lean_inc_ref(v_value_573_);
v___f_588_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___lam__0___boxed), 6, 2);
lean_closure_set(v___f_588_, 0, v___x_587_);
lean_closure_set(v___f_588_, 1, v_value_573_);
v___x_589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_589_, 0, v_value_573_);
lean_ctor_set(v___x_589_, 1, v___x_586_);
lean_ctor_set(v___x_589_, 2, v___x_587_);
v___x_590_ = l_String_Slice_positions(v___x_589_);
lean_dec_ref_known(v___x_589_, 3);
v___x_591_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_588_, v___x_590_, v_acc_582_, lean_box(0));
v___x_592_ = lean_string_append(v___x_591_, v___x_581_);
v___y_569_ = v___x_592_;
goto v___jp_568_;
}
}
v___jp_593_:
{
if (lean_obj_tag(v_documentation_x3f_367_) == 1)
{
lean_object* v_val_595_; uint8_t v_kind_596_; lean_object* v_value_597_; lean_object* v___x_598_; lean_object* v_acc_599_; 
v_val_595_ = lean_ctor_get(v_documentation_x3f_367_, 0);
lean_inc(v_val_595_);
lean_dec_ref_known(v_documentation_x3f_367_, 1);
v_kind_596_ = lean_ctor_get_uint8(v_val_595_, sizeof(void*)*1);
v_value_597_ = lean_ctor_get(v_val_595_, 0);
lean_inc_ref(v_value_597_);
lean_dec(v_val_595_);
v___x_598_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5));
v_acc_599_ = lean_string_append(v_acc_594_, v___x_598_);
if (v_kind_596_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
v_value_573_ = v_value_597_;
v___y_574_ = v_acc_599_;
v___y_575_ = v___x_600_;
goto v___jp_572_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
v_value_573_ = v_value_597_;
v___y_574_ = v_acc_599_;
v___y_575_ = v___x_601_;
goto v___jp_572_;
}
}
else
{
lean_dec(v_documentation_x3f_367_);
v_acc_558_ = v_acc_594_;
goto v___jp_557_;
}
}
v___jp_602_:
{
if (lean_obj_tag(v_detail_x3f_366_) == 1)
{
lean_object* v_val_604_; lean_object* v___x_605_; lean_object* v_acc_606_; lean_object* v___x_607_; lean_object* v_acc_608_; uint8_t v___x_609_; 
v_val_604_ = lean_ctor_get(v_detail_x3f_366_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_detail_x3f_366_, 1);
v___x_605_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6));
v_acc_606_ = lean_string_append(v___y_603_, v___x_605_);
v___x_607_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_608_ = lean_string_append(v_acc_606_, v___x_607_);
v___x_609_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_604_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_string_append(v_acc_608_, v_val_604_);
lean_dec(v_val_604_);
v___x_611_ = lean_string_append(v___x_610_, v___x_607_);
v_acc_594_ = v___x_611_;
goto v___jp_593_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___f_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_string_utf8_byte_size(v_val_604_);
lean_inc(v_val_604_);
v___f_614_ = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___lam__3___boxed), 6, 2);
lean_closure_set(v___f_614_, 0, v___x_613_);
lean_closure_set(v___f_614_, 1, v_val_604_);
v___x_615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_615_, 0, v_val_604_);
lean_ctor_set(v___x_615_, 1, v___x_612_);
lean_ctor_set(v___x_615_, 2, v___x_613_);
v___x_616_ = l_String_Slice_positions(v___x_615_);
lean_dec_ref_known(v___x_615_, 3);
v___x_617_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_614_, v___x_616_, v_acc_608_, lean_box(0));
v___x_618_ = lean_string_append(v___x_617_, v___x_607_);
v_acc_594_ = v___x_618_;
goto v___jp_593_;
}
}
else
{
lean_dec(v_detail_x3f_366_);
v_acc_594_ = v___y_603_;
goto v___jp_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v_a_635_, lean_object* v_b_636_){
_start:
{
lean_object* v_startInclusive_637_; lean_object* v_endExclusive_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v_startInclusive_637_ = lean_ctor_get(v___x_633_, 1);
v_endExclusive_638_ = lean_ctor_get(v___x_633_, 2);
v___x_639_ = lean_nat_sub(v_endExclusive_638_, v_startInclusive_637_);
v___x_640_ = lean_nat_dec_eq(v_a_635_, v___x_639_);
lean_dec(v___x_639_);
if (v___x_640_ == 0)
{
uint32_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_string_utf8_get_fast(v___x_634_, v_a_635_);
v___x_642_ = lean_string_utf8_next_fast(v___x_634_, v_a_635_);
lean_dec(v_a_635_);
v___x_643_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_escapeAux(v_b_636_, v___x_641_);
v_a_635_ = v___x_642_;
v_b_636_ = v___x_643_;
goto _start;
}
else
{
lean_dec(v_a_635_);
return v_b_636_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg___boxed(lean_object* v___x_645_, lean_object* v___x_646_, lean_object* v_a_647_, lean_object* v_b_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_645_, v___x_646_, v_a_647_, v_b_648_);
lean_dec_ref(v___x_646_);
lean_dec_ref(v___x_645_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(lean_object* v_acc_650_, lean_object* v_items_651_, lean_object* v_i_652_){
_start:
{
lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___x_658_; lean_object* v_acc_660_; lean_object* v_acc_669_; uint8_t v___x_672_; 
v___x_658_ = lean_array_get_size(v_items_651_);
v___x_672_ = lean_nat_dec_lt(v_i_652_, v___x_658_);
if (v___x_672_ == 0)
{
lean_dec(v_i_652_);
return v_acc_650_;
}
else
{
lean_object* v___x_673_; lean_object* v_acc_675_; lean_object* v_acc_689_; lean_object* v___y_693_; lean_object* v___y_697_; lean_object* v___y_701_; lean_object* v_id_x3f_702_; lean_object* v_acc_703_; lean_object* v_pos_729_; lean_object* v_cPos_x3f_730_; lean_object* v_id_x3f_731_; lean_object* v___y_732_; lean_object* v_acc_747_; lean_object* v_acc_770_; lean_object* v_acc_787_; lean_object* v_acc_857_; lean_object* v___y_869_; lean_object* v___y_873_; lean_object* v_value_874_; lean_object* v___y_875_; lean_object* v_acc_893_; lean_object* v___y_903_; lean_object* v_label_919_; lean_object* v___x_920_; lean_object* v_acc_921_; lean_object* v___x_922_; lean_object* v_acc_923_; uint8_t v___x_924_; 
v___x_673_ = lean_array_fget_borrowed(v_items_651_, v_i_652_);
v_label_919_ = lean_ctor_get(v___x_673_, 0);
v___x_920_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__7));
v_acc_921_ = lean_string_append(v_acc_650_, v___x_920_);
v___x_922_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_923_ = lean_string_append(v_acc_921_, v___x_922_);
v___x_924_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_label_919_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_string_append(v_acc_923_, v_label_919_);
v___x_926_ = lean_string_append(v___x_925_, v___x_922_);
v___y_903_ = v___x_926_;
goto v___jp_902_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_string_utf8_byte_size(v_label_919_);
lean_inc_ref(v_label_919_);
v___x_929_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_929_, 0, v_label_919_);
lean_ctor_set(v___x_929_, 1, v___x_927_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
v___x_930_ = l_String_Slice_positions(v___x_929_);
v___x_931_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_929_, v_label_919_, v___x_930_, v_acc_923_);
lean_dec_ref_known(v___x_929_, 3);
v___x_932_ = lean_string_append(v___x_931_, v___x_922_);
v___y_903_ = v___x_932_;
goto v___jp_902_;
}
v___jp_674_:
{
lean_object* v_tags_x3f_676_; 
v_tags_x3f_676_ = lean_ctor_get(v___x_673_, 7);
if (lean_obj_tag(v_tags_x3f_676_) == 1)
{
lean_object* v_val_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_val_677_ = lean_ctor_get(v_tags_x3f_676_, 0);
v___x_678_ = lean_unsigned_to_nat(0u);
v___x_679_ = lean_array_get_size(v_val_677_);
v___x_680_ = lean_nat_dec_lt(v___x_678_, v___x_679_);
if (v___x_680_ == 0)
{
v_acc_660_ = v_acc_675_;
goto v___jp_659_;
}
else
{
lean_object* v___x_681_; lean_object* v_acc_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_681_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__0));
v_acc_682_ = lean_string_append(v_acc_675_, v___x_681_);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_dec_eq(v___x_679_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v_acc_685_; 
v_acc_685_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast(v_acc_682_, v_val_677_, v___x_678_);
v_acc_669_ = v_acc_685_;
goto v___jp_668_;
}
else
{
lean_object* v___x_686_; lean_object* v_acc_687_; 
v___x_686_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressCompletionTagsFast___closed__0));
v_acc_687_ = lean_string_append(v_acc_682_, v___x_686_);
v_acc_669_ = v_acc_687_;
goto v___jp_668_;
}
}
}
else
{
v_acc_660_ = v_acc_675_;
goto v___jp_659_;
}
}
v___jp_688_:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v___x_691_ = lean_string_append(v_acc_689_, v___x_690_);
v_acc_675_ = v___x_691_;
goto v___jp_674_;
}
v___jp_692_:
{
lean_object* v___x_694_; lean_object* v_acc_695_; 
v___x_694_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_695_ = lean_string_append(v___y_693_, v___x_694_);
v_acc_689_ = v_acc_695_;
goto v___jp_688_;
}
v___jp_696_:
{
lean_object* v___x_698_; lean_object* v_acc_699_; 
v___x_698_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_699_ = lean_string_append(v___y_697_, v___x_698_);
v_acc_689_ = v_acc_699_;
goto v___jp_688_;
}
v___jp_700_:
{
if (lean_obj_tag(v_id_x3f_702_) == 1)
{
lean_object* v_val_704_; lean_object* v_acc_705_; 
v_val_704_ = lean_ctor_get(v_id_x3f_702_, 0);
lean_inc(v_val_704_);
lean_dec_ref_known(v_id_x3f_702_, 1);
v_acc_705_ = lean_string_append(v_acc_703_, v___y_701_);
if (lean_obj_tag(v_val_704_) == 0)
{
lean_object* v_declName_706_; lean_object* v___x_707_; lean_object* v_acc_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_declName_706_ = lean_ctor_get(v_val_704_, 0);
lean_inc(v_declName_706_);
lean_dec_ref_known(v_val_704_, 1);
v___x_707_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__2));
v_acc_708_ = lean_string_append(v_acc_705_, v___x_707_);
v___x_709_ = l_Lean_Name_toString(v_declName_706_, v___x_672_);
v___x_710_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
v___x_711_ = lean_string_append(v_acc_708_, v___x_709_);
lean_dec_ref(v___x_709_);
v___y_693_ = v___x_711_;
goto v___jp_692_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = lean_string_utf8_byte_size(v___x_709_);
lean_inc_ref(v___x_709_);
v___x_714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_714_, 0, v___x_709_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
lean_ctor_set(v___x_714_, 2, v___x_713_);
v___x_715_ = l_String_Slice_positions(v___x_714_);
v___x_716_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_714_, v___x_709_, v___x_715_, v_acc_708_);
lean_dec_ref(v___x_709_);
lean_dec_ref_known(v___x_714_, 3);
v___y_693_ = v___x_716_;
goto v___jp_692_;
}
}
else
{
lean_object* v_id_717_; lean_object* v___x_718_; lean_object* v_acc_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_id_717_ = lean_ctor_get(v_val_704_, 0);
lean_inc(v_id_717_);
lean_dec_ref_known(v_val_704_, 1);
v___x_718_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__3));
v_acc_719_ = lean_string_append(v_acc_705_, v___x_718_);
v___x_720_ = l_Lean_Name_toString(v_id_717_, v___x_672_);
v___x_721_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
v___x_722_ = lean_string_append(v_acc_719_, v___x_720_);
lean_dec_ref(v___x_720_);
v___y_697_ = v___x_722_;
goto v___jp_696_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_string_utf8_byte_size(v___x_720_);
lean_inc_ref(v___x_720_);
v___x_725_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_725_, 0, v___x_720_);
lean_ctor_set(v___x_725_, 1, v___x_723_);
lean_ctor_set(v___x_725_, 2, v___x_724_);
v___x_726_ = l_String_Slice_positions(v___x_725_);
v___x_727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_725_, v___x_720_, v___x_726_, v_acc_719_);
lean_dec_ref(v___x_720_);
lean_dec_ref_known(v___x_725_, 3);
v___y_697_ = v___x_727_;
goto v___jp_696_;
}
}
}
else
{
lean_dec(v_id_x3f_702_);
v_acc_689_ = v_acc_703_;
goto v___jp_688_;
}
}
v___jp_728_:
{
lean_object* v_line_733_; lean_object* v_character_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v_acc_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v_acc_741_; 
v_line_733_ = lean_ctor_get(v_pos_729_, 0);
lean_inc(v_line_733_);
v_character_734_ = lean_ctor_get(v_pos_729_, 1);
lean_inc(v_character_734_);
lean_dec_ref(v_pos_729_);
v___x_735_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_736_ = lean_string_append(v___y_732_, v___x_735_);
v___x_737_ = l_Nat_reprFast(v_line_733_);
v_acc_738_ = lean_string_append(v___x_736_, v___x_737_);
lean_dec_ref(v___x_737_);
v___x_739_ = lean_string_append(v_acc_738_, v___x_735_);
v___x_740_ = l_Nat_reprFast(v_character_734_);
v_acc_741_ = lean_string_append(v___x_739_, v___x_740_);
lean_dec_ref(v___x_740_);
if (lean_obj_tag(v_cPos_x3f_730_) == 1)
{
lean_object* v_val_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v_acc_745_; 
v_val_742_ = lean_ctor_get(v_cPos_x3f_730_, 0);
lean_inc(v_val_742_);
lean_dec_ref_known(v_cPos_x3f_730_, 1);
v___x_743_ = lean_string_append(v_acc_741_, v___x_735_);
v___x_744_ = l_Nat_reprFast(v_val_742_);
v_acc_745_ = lean_string_append(v___x_743_, v___x_744_);
lean_dec_ref(v___x_744_);
v___y_701_ = v___x_735_;
v_id_x3f_702_ = v_id_x3f_731_;
v_acc_703_ = v_acc_745_;
goto v___jp_700_;
}
else
{
lean_dec(v_cPos_x3f_730_);
v___y_701_ = v___x_735_;
v_id_x3f_702_ = v_id_x3f_731_;
v_acc_703_ = v_acc_741_;
goto v___jp_700_;
}
}
v___jp_746_:
{
lean_object* v_data_x3f_748_; 
v_data_x3f_748_ = lean_ctor_get(v___x_673_, 6);
if (lean_obj_tag(v_data_x3f_748_) == 1)
{
lean_object* v_val_749_; lean_object* v_uri_750_; lean_object* v_pos_751_; lean_object* v_cPos_x3f_752_; lean_object* v_id_x3f_753_; lean_object* v___x_754_; lean_object* v_acc_755_; lean_object* v___x_756_; lean_object* v_acc_757_; lean_object* v___x_758_; lean_object* v_acc_759_; uint8_t v___x_760_; 
v_val_749_ = lean_ctor_get(v_data_x3f_748_, 0);
v_uri_750_ = lean_ctor_get(v_val_749_, 0);
v_pos_751_ = lean_ctor_get(v_val_749_, 1);
v_cPos_x3f_752_ = lean_ctor_get(v_val_749_, 2);
v_id_x3f_753_ = lean_ctor_get(v_val_749_, 3);
v___x_754_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__1));
v_acc_755_ = lean_string_append(v_acc_747_, v___x_754_);
v___x_756_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__5));
v_acc_757_ = lean_string_append(v_acc_755_, v___x_756_);
v___x_758_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_759_ = lean_string_append(v_acc_757_, v___x_758_);
v___x_760_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_uri_750_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_string_append(v_acc_759_, v_uri_750_);
v___x_762_ = lean_string_append(v___x_761_, v___x_758_);
lean_inc(v_id_x3f_753_);
lean_inc(v_cPos_x3f_752_);
lean_inc_ref(v_pos_751_);
v_pos_729_ = v_pos_751_;
v_cPos_x3f_730_ = v_cPos_x3f_752_;
v_id_x3f_731_ = v_id_x3f_753_;
v___y_732_ = v___x_762_;
goto v___jp_728_;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_string_utf8_byte_size(v_uri_750_);
lean_inc_ref(v_uri_750_);
v___x_765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_765_, 0, v_uri_750_);
lean_ctor_set(v___x_765_, 1, v___x_763_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
v___x_766_ = l_String_Slice_positions(v___x_765_);
v___x_767_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_765_, v_uri_750_, v___x_766_, v_acc_759_);
lean_dec_ref_known(v___x_765_, 3);
v___x_768_ = lean_string_append(v___x_767_, v___x_758_);
lean_inc(v_id_x3f_753_);
lean_inc(v_cPos_x3f_752_);
lean_inc_ref(v_pos_751_);
v_pos_729_ = v_pos_751_;
v_cPos_x3f_730_ = v_cPos_x3f_752_;
v_id_x3f_731_ = v_id_x3f_753_;
v___y_732_ = v___x_768_;
goto v___jp_728_;
}
}
else
{
v_acc_675_ = v_acc_747_;
goto v___jp_674_;
}
}
v___jp_769_:
{
lean_object* v_sortText_x3f_771_; 
v_sortText_x3f_771_ = lean_ctor_get(v___x_673_, 5);
if (lean_obj_tag(v_sortText_x3f_771_) == 1)
{
lean_object* v_val_772_; lean_object* v___x_773_; lean_object* v_acc_774_; lean_object* v___x_775_; lean_object* v_acc_776_; uint8_t v___x_777_; 
v_val_772_ = lean_ctor_get(v_sortText_x3f_771_, 0);
v___x_773_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__2));
v_acc_774_ = lean_string_append(v_acc_770_, v___x_773_);
v___x_775_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_776_ = lean_string_append(v_acc_774_, v___x_775_);
v___x_777_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_772_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_string_append(v_acc_776_, v_val_772_);
v___x_779_ = lean_string_append(v___x_778_, v___x_775_);
v_acc_747_ = v___x_779_;
goto v___jp_746_;
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_string_utf8_byte_size(v_val_772_);
lean_inc(v_val_772_);
v___x_782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_782_, 0, v_val_772_);
lean_ctor_set(v___x_782_, 1, v___x_780_);
lean_ctor_set(v___x_782_, 2, v___x_781_);
v___x_783_ = l_String_Slice_positions(v___x_782_);
v___x_784_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_782_, v_val_772_, v___x_783_, v_acc_776_);
lean_dec_ref_known(v___x_782_, 3);
v___x_785_ = lean_string_append(v___x_784_, v___x_775_);
v_acc_747_ = v___x_785_;
goto v___jp_746_;
}
}
else
{
v_acc_747_ = v_acc_770_;
goto v___jp_746_;
}
}
v___jp_786_:
{
lean_object* v_textEdit_x3f_788_; 
v_textEdit_x3f_788_ = lean_ctor_get(v___x_673_, 4);
if (lean_obj_tag(v_textEdit_x3f_788_) == 1)
{
lean_object* v_val_789_; lean_object* v_insert_790_; lean_object* v_end_791_; lean_object* v_start_792_; lean_object* v_replace_793_; lean_object* v_end_794_; lean_object* v_start_795_; lean_object* v_newText_796_; lean_object* v_line_797_; lean_object* v_character_798_; lean_object* v_line_799_; lean_object* v_character_800_; lean_object* v_line_801_; lean_object* v_character_802_; lean_object* v_line_803_; lean_object* v_character_804_; lean_object* v___x_805_; lean_object* v_acc_806_; lean_object* v___x_807_; lean_object* v_acc_808_; lean_object* v___x_809_; lean_object* v_acc_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_acc_820_; lean_object* v___x_821_; lean_object* v_acc_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v_acc_829_; lean_object* v_acc_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v_acc_835_; lean_object* v___x_836_; lean_object* v_acc_837_; lean_object* v_acc_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v_acc_845_; lean_object* v_acc_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v_acc_853_; lean_object* v_acc_854_; lean_object* v_acc_855_; 
v_val_789_ = lean_ctor_get(v_textEdit_x3f_788_, 0);
v_insert_790_ = lean_ctor_get(v_val_789_, 1);
v_end_791_ = lean_ctor_get(v_insert_790_, 1);
v_start_792_ = lean_ctor_get(v_insert_790_, 0);
v_replace_793_ = lean_ctor_get(v_val_789_, 2);
v_end_794_ = lean_ctor_get(v_replace_793_, 1);
v_start_795_ = lean_ctor_get(v_replace_793_, 0);
v_newText_796_ = lean_ctor_get(v_val_789_, 0);
v_line_797_ = lean_ctor_get(v_end_791_, 0);
v_character_798_ = lean_ctor_get(v_end_791_, 1);
v_line_799_ = lean_ctor_get(v_start_792_, 0);
v_character_800_ = lean_ctor_get(v_start_792_, 1);
v_line_801_ = lean_ctor_get(v_end_794_, 0);
v_character_802_ = lean_ctor_get(v_end_794_, 1);
v_line_803_ = lean_ctor_get(v_start_795_, 0);
v_character_804_ = lean_ctor_get(v_start_795_, 1);
v___x_805_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__3));
v_acc_806_ = lean_string_append(v_acc_787_, v___x_805_);
v___x_807_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__0));
v_acc_808_ = lean_string_append(v_acc_806_, v___x_807_);
v___x_809_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__0));
v_acc_810_ = lean_string_append(v_acc_808_, v___x_809_);
v___x_811_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__0));
v___x_812_ = lean_string_append(v_acc_810_, v___x_811_);
lean_inc(v_character_798_);
v___x_813_ = l_Nat_reprFast(v_character_798_);
v___x_814_ = lean_string_append(v___x_812_, v___x_813_);
lean_dec_ref(v___x_813_);
v___x_815_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressPositionFast___closed__1));
v___x_816_ = lean_string_append(v___x_814_, v___x_815_);
lean_inc(v_line_797_);
v___x_817_ = l_Nat_reprFast(v_line_797_);
v___x_818_ = lean_string_append(v___x_816_, v___x_817_);
lean_dec_ref(v___x_817_);
v___x_819_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v_acc_820_ = lean_string_append(v___x_818_, v___x_819_);
v___x_821_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressRangeFast___closed__1));
v_acc_822_ = lean_string_append(v_acc_820_, v___x_821_);
v___x_823_ = lean_string_append(v_acc_822_, v___x_811_);
lean_inc(v_character_800_);
v___x_824_ = l_Nat_reprFast(v_character_800_);
v___x_825_ = lean_string_append(v___x_823_, v___x_824_);
lean_dec_ref(v___x_824_);
v___x_826_ = lean_string_append(v___x_825_, v___x_815_);
lean_inc(v_line_799_);
v___x_827_ = l_Nat_reprFast(v_line_799_);
v___x_828_ = lean_string_append(v___x_826_, v___x_827_);
lean_dec_ref(v___x_827_);
v_acc_829_ = lean_string_append(v___x_828_, v___x_819_);
v_acc_830_ = lean_string_append(v_acc_829_, v___x_819_);
v___x_831_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__1));
v___x_832_ = lean_string_append(v_acc_830_, v___x_831_);
v___x_833_ = lean_string_append(v___x_832_, v_newText_796_);
v___x_834_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_835_ = lean_string_append(v___x_833_, v___x_834_);
v___x_836_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressEditFast___closed__2));
v_acc_837_ = lean_string_append(v_acc_835_, v___x_836_);
v_acc_838_ = lean_string_append(v_acc_837_, v___x_809_);
v___x_839_ = lean_string_append(v_acc_838_, v___x_811_);
lean_inc(v_character_802_);
v___x_840_ = l_Nat_reprFast(v_character_802_);
v___x_841_ = lean_string_append(v___x_839_, v___x_840_);
lean_dec_ref(v___x_840_);
v___x_842_ = lean_string_append(v___x_841_, v___x_815_);
lean_inc(v_line_801_);
v___x_843_ = l_Nat_reprFast(v_line_801_);
v___x_844_ = lean_string_append(v___x_842_, v___x_843_);
lean_dec_ref(v___x_843_);
v_acc_845_ = lean_string_append(v___x_844_, v___x_819_);
v_acc_846_ = lean_string_append(v_acc_845_, v___x_821_);
v___x_847_ = lean_string_append(v_acc_846_, v___x_811_);
lean_inc(v_character_804_);
v___x_848_ = l_Nat_reprFast(v_character_804_);
v___x_849_ = lean_string_append(v___x_847_, v___x_848_);
lean_dec_ref(v___x_848_);
v___x_850_ = lean_string_append(v___x_849_, v___x_815_);
lean_inc(v_line_803_);
v___x_851_ = l_Nat_reprFast(v_line_803_);
v___x_852_ = lean_string_append(v___x_850_, v___x_851_);
lean_dec_ref(v___x_851_);
v_acc_853_ = lean_string_append(v___x_852_, v___x_819_);
v_acc_854_ = lean_string_append(v_acc_853_, v___x_819_);
v_acc_855_ = lean_string_append(v_acc_854_, v___x_819_);
v_acc_770_ = v_acc_855_;
goto v___jp_769_;
}
else
{
v_acc_770_ = v_acc_787_;
goto v___jp_769_;
}
}
v___jp_856_:
{
lean_object* v_kind_x3f_858_; 
v_kind_x3f_858_ = lean_ctor_get(v___x_673_, 3);
if (lean_obj_tag(v_kind_x3f_858_) == 1)
{
lean_object* v_val_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v_acc_867_; 
v_val_859_ = lean_ctor_get(v_kind_x3f_858_, 0);
v___x_860_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__4));
v___x_861_ = lean_string_append(v_acc_857_, v___x_860_);
v___x_862_ = lean_unbox(v_val_859_);
v___x_863_ = l_Lean_Lsp_CompletionItemKind_ctorIdx(v___x_862_);
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = lean_nat_add(v___x_863_, v___x_864_);
lean_dec(v___x_863_);
v___x_866_ = l_Nat_reprFast(v___x_865_);
v_acc_867_ = lean_string_append(v___x_861_, v___x_866_);
lean_dec_ref(v___x_866_);
v_acc_787_ = v_acc_867_;
goto v___jp_786_;
}
else
{
v_acc_787_ = v_acc_857_;
goto v___jp_786_;
}
}
v___jp_868_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_871_ = lean_string_append(v___y_869_, v___x_870_);
v_acc_857_ = v___x_871_;
goto v___jp_856_;
}
v___jp_872_:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v_acc_880_; lean_object* v___x_881_; lean_object* v_acc_882_; uint8_t v___x_883_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__1));
v___x_877_ = lean_string_append(v___y_873_, v___x_876_);
v___x_878_ = lean_string_append(v___x_877_, v___y_875_);
v___x_879_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__2));
v_acc_880_ = lean_string_append(v___x_878_, v___x_879_);
v___x_881_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_882_ = lean_string_append(v_acc_880_, v___x_881_);
v___x_883_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_value_874_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = lean_string_append(v_acc_882_, v_value_874_);
lean_dec_ref(v_value_874_);
v___x_885_ = lean_string_append(v___x_884_, v___x_881_);
v___y_869_ = v___x_885_;
goto v___jp_868_;
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_886_ = lean_unsigned_to_nat(0u);
v___x_887_ = lean_string_utf8_byte_size(v_value_874_);
lean_inc_ref(v_value_874_);
v___x_888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_888_, 0, v_value_874_);
lean_ctor_set(v___x_888_, 1, v___x_886_);
lean_ctor_set(v___x_888_, 2, v___x_887_);
v___x_889_ = l_String_Slice_positions(v___x_888_);
v___x_890_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_888_, v_value_874_, v___x_889_, v_acc_882_);
lean_dec_ref(v_value_874_);
lean_dec_ref_known(v___x_888_, 3);
v___x_891_ = lean_string_append(v___x_890_, v___x_881_);
v___y_869_ = v___x_891_;
goto v___jp_868_;
}
}
v___jp_892_:
{
lean_object* v_documentation_x3f_894_; 
v_documentation_x3f_894_ = lean_ctor_get(v___x_673_, 2);
if (lean_obj_tag(v_documentation_x3f_894_) == 1)
{
lean_object* v_val_895_; uint8_t v_kind_896_; lean_object* v_value_897_; lean_object* v___x_898_; lean_object* v_acc_899_; 
v_val_895_ = lean_ctor_get(v_documentation_x3f_894_, 0);
v_kind_896_ = lean_ctor_get_uint8(v_val_895_, sizeof(void*)*1);
v_value_897_ = lean_ctor_get(v_val_895_, 0);
v___x_898_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__5));
v_acc_899_ = lean_string_append(v_acc_893_, v___x_898_);
if (v_kind_896_ == 0)
{
lean_object* v___x_900_; 
v___x_900_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__3));
lean_inc_ref(v_value_897_);
v___y_873_ = v_acc_899_;
v_value_874_ = v_value_897_;
v___y_875_ = v___x_900_;
goto v___jp_872_;
}
else
{
lean_object* v___x_901_; 
v___x_901_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__4));
lean_inc_ref(v_value_897_);
v___y_873_ = v_acc_899_;
v_value_874_ = v_value_897_;
v___y_875_ = v___x_901_;
goto v___jp_872_;
}
}
else
{
v_acc_857_ = v_acc_893_;
goto v___jp_856_;
}
}
v___jp_902_:
{
lean_object* v_detail_x3f_904_; 
v_detail_x3f_904_ = lean_ctor_get(v___x_673_, 1);
if (lean_obj_tag(v_detail_x3f_904_) == 1)
{
lean_object* v_val_905_; lean_object* v___x_906_; lean_object* v_acc_907_; lean_object* v___x_908_; lean_object* v_acc_909_; uint8_t v___x_910_; 
v_val_905_ = lean_ctor_get(v_detail_x3f_904_, 0);
v___x_906_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemFast___closed__6));
v_acc_907_ = lean_string_append(v___y_903_, v___x_906_);
v___x_908_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__1));
v_acc_909_ = lean_string_append(v_acc_907_, v___x_908_);
v___x_910_ = l___private_Lean_Data_Json_Printer_0__Lean_Json_needEscape(v_val_905_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_string_append(v_acc_909_, v_val_905_);
v___x_912_ = lean_string_append(v___x_911_, v___x_908_);
v_acc_893_ = v___x_912_;
goto v___jp_892_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_string_utf8_byte_size(v_val_905_);
lean_inc(v_val_905_);
v___x_915_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_915_, 0, v_val_905_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
lean_ctor_set(v___x_915_, 2, v___x_914_);
v___x_916_ = l_String_Slice_positions(v___x_915_);
v___x_917_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_915_, v_val_905_, v___x_916_, v_acc_909_);
lean_dec_ref_known(v___x_915_, 3);
v___x_918_ = lean_string_append(v___x_917_, v___x_908_);
v_acc_893_ = v___x_918_;
goto v___jp_892_;
}
}
else
{
v_acc_893_ = v___y_903_;
goto v___jp_892_;
}
}
}
v___jp_653_:
{
lean_object* v___x_656_; 
v___x_656_ = lean_nat_add(v_i_652_, v___y_654_);
lean_dec(v_i_652_);
v_acc_650_ = v___y_655_;
v_i_652_ = v___x_656_;
goto _start;
}
v___jp_659_:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_661_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressMarkupContentFast___closed__0));
v___x_662_ = lean_string_append(v_acc_660_, v___x_661_);
v___x_663_ = lean_unsigned_to_nat(1u);
v___x_664_ = lean_nat_sub(v___x_658_, v___x_663_);
v___x_665_ = lean_nat_dec_lt(v_i_652_, v___x_664_);
lean_dec(v___x_664_);
if (v___x_665_ == 0)
{
v___y_654_ = v___x_663_;
v___y_655_ = v___x_662_;
goto v___jp_653_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__4));
v___x_667_ = lean_string_append(v___x_662_, v___x_666_);
v___y_654_ = v___x_663_;
v___y_655_ = v___x_667_;
goto v___jp_653_;
}
}
v___jp_668_:
{
lean_object* v___x_670_; lean_object* v_acc_671_; 
v___x_670_ = ((lean_object*)(l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemDataFast___closed__0));
v_acc_671_ = lean_string_append(v_acc_669_, v___x_670_);
v_acc_660_ = v_acc_671_;
goto v___jp_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast___boxed(lean_object* v_acc_933_, lean_object* v_items_934_, lean_object* v_i_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(v_acc_933_, v_items_934_, v_i_935_);
lean_dec_ref(v_items_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(lean_object* v___x_937_, lean_object* v___x_938_, lean_object* v_inst_939_, lean_object* v_R_940_, lean_object* v_a_941_, lean_object* v_b_942_, lean_object* v_c_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___redArg(v___x_937_, v___x_938_, v_a_941_, v_b_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0___boxed(lean_object* v___x_945_, lean_object* v___x_946_, lean_object* v_inst_947_, lean_object* v_R_948_, lean_object* v_a_949_, lean_object* v_b_950_, lean_object* v_c_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast_spec__0(v___x_945_, v___x_946_, v_inst_947_, v_R_948_, v_a_949_, v_b_950_, v_c_951_);
lean_dec_ref(v___x_946_);
lean_dec_ref(v___x_945_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast(lean_object* v_l_958_){
_start:
{
uint8_t v_isIncomplete_959_; lean_object* v_items_960_; lean_object* v___x_961_; lean_object* v___y_963_; 
v_isIncomplete_959_ = lean_ctor_get_uint8(v_l_958_, sizeof(void*)*1);
v_items_960_ = lean_ctor_get(v_l_958_, 0);
v___x_961_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__0));
if (v_isIncomplete_959_ == 0)
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__3));
v___y_963_ = v___x_971_;
goto v___jp_962_;
}
else
{
lean_object* v___x_972_; 
v___x_972_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__4));
v___y_963_ = v___x_972_;
goto v___jp_962_;
}
v___jp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_acc_966_; lean_object* v___x_967_; lean_object* v_acc_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_964_ = lean_string_append(v___x_961_, v___y_963_);
v___x_965_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__1));
v_acc_966_ = lean_string_append(v___x_964_, v___x_965_);
v___x_967_ = lean_unsigned_to_nat(0u);
v_acc_968_ = l___private_Lean_Server_Completion_CompletionItemCompression_0__Lean_Lsp_ResolvableCompletionList_compressItemsFast(v_acc_966_, v_items_960_, v___x_967_);
v___x_969_ = ((lean_object*)(l_Lean_Lsp_ResolvableCompletionList_compressFast___closed__2));
v___x_970_ = lean_string_append(v_acc_968_, v___x_969_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ResolvableCompletionList_compressFast___boxed(lean_object* v_l_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Lsp_ResolvableCompletionList_compressFast(v_l_973_);
lean_dec_ref(v_l_973_);
return v_res_974_;
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

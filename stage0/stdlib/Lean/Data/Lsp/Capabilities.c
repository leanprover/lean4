// Lean compiler output
// Module: Lean.Data.Lsp.Capabilities
// Imports: public import Lean.Data.JsonRpc public import Lean.Data.Lsp.LanguageFeatures public import Lean.Data.Lsp.CodeActions public import Lean.Data.Lsp.Extra
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
lean_object* l_Lean_Lsp_instToJsonRpcOptions_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSemanticTokensOptions_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCompletionOptions_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRenameOptions_toJson(uint8_t);
lean_object* l_Lean_Lsp_instToJsonSemanticTokensOptions_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCodeActionOptions_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonInlayHintOptions_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonSignatureHelpOptions_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonDocumentColorOptions_toJson(uint8_t);
lean_object* l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
lean_object* l_Lean_Lsp_instFromJsonRpcOptions_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonInlayHintOptions_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonInlayHintClientCapabilities_fromJson(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonRpcWireFormat_toJson(uint8_t);
lean_object* l_Lean_Lsp_instFromJsonCompletionOptions_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRenameOptions_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonDocumentColorOptions_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonInlayHintClientCapabilities_toJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonSignatureHelpOptions_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "insertReplaceSupport"};
static const lean_object* l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__0_value;
static const lean_array_object l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonCompletionItemCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonCompletionItemCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonCompletionItemCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonCompletionItemCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonCompletionItemCapabilities___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "CompletionItemCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(168, 162, 232, 103, 213, 167, 93, 242)}};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6;
static const lean_string_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "insertReplaceSupport\?"};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__7_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__7_value),LEAN_SCALAR_PTR_LITERAL(124, 17, 86, 160, 119, 199, 142, 57)}};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10;
static const lean_string_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonCompletionItemCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "completionItem"};
static const lean_object* l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonCompletionClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonCompletionClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonCompletionClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonCompletionClientCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonCompletionClientCapabilities___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "CompletionClientCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 114, 84, 111, 206, 242, 23, 210)}};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "completionItem\?"};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(148, 88, 72, 80, 247, 45, 226, 68)}};
static const lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonCompletionClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonCompletionClientCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "completion"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "codeAction"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inlayHint"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonTextDocumentClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextDocumentClientCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentClientCapabilities___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "TextDocumentClientCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 8, 128, 198, 36, 63, 158, 219)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "completion\?"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(211, 102, 236, 80, 129, 50, 133, 33)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "codeAction\?"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(32, 9, 147, 242, 55, 207, 156, 149)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13;
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "inlayHint\?"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(64, 110, 171, 197, 31, 169, 250, 121)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "support"};
static const lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonShowDocumentClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonShowDocumentClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonShowDocumentClientCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ShowDocumentClientCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 227, 102, 228, 63, 67, 171, 158)}};
static const lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 49, 93, 70, 185, 187, 252, 212)}};
static const lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "showDocument"};
static const lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWindowClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWindowClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonWindowClientCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "WindowClientCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 16, 77, 211, 20, 177, 36, 236)}};
static const lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "showDocument\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(100, 183, 142, 163, 171, 83, 242, 42)}};
static const lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWindowClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWindowClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonWindowClientCapabilities___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "groupsOnLabel"};
static const lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonChangeAnnotationSupport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonChangeAnnotationSupport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport = (const lean_object*)&l_Lean_Lsp_instToJsonChangeAnnotationSupport___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ChangeAnnotationSupport"};
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(77, 205, 129, 68, 169, 88, 116, 77)}};
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "groupsOnLabel\?"};
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(82, 95, 251, 98, 216, 224, 97, 227)}};
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonChangeAnnotationSupport___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotationSupport___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport = (const lean_object*)&l_Lean_Lsp_instFromJsonChangeAnnotationSupport___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "documentChanges"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "changeAnnotationSupport"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "resourceOperations"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "WorkspaceEditClientCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 114, 2, 101, 88, 119, 192, 111)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "documentChanges\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(98, 237, 212, 122, 169, 183, 78, 106)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "changeAnnotationSupport\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(102, 156, 73, 199, 112, 229, 110, 9)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "resourceOperations\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(130, 35, 108, 92, 58, 215, 10, 58)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "applyEdit"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "workspaceEdit"};
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonWorkspaceClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonWorkspaceClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonWorkspaceClientCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonWorkspaceClientCapabilities___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "WorkspaceClientCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 74, 183, 61, 37, 225, 182, 245)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "applyEdit\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(121, 129, 200, 120, 123, 107, 28, 164)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "workspaceEdit\?"};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(9, 88, 0, 64, 220, 57, 86, 230)}};
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "incrementalDiagnosticSupport"};
static const lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "silentDiagnosticSupport"};
static const lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "rpcWireFormat"};
static const lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonLeanClientCapabilities___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "LeanClientCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 254, 182, 222, 136, 163, 126, 10)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "incrementalDiagnosticSupport\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(197, 194, 208, 52, 121, 207, 90, 171)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "silentDiagnosticSupport\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(109, 58, 227, 208, 126, 204, 178, 31)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "rpcWireFormat\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(102, 166, 72, 226, 0, 98, 21, 166)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanClientCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "textDocument"};
static const lean_object* l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "window"};
static const lean_object* l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "workspace"};
static const lean_object* l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonClientCapabilities_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonClientCapabilities_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonClientCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonClientCapabilities___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ClientCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 225, 118, 144, 36, 222, 122, 79)}};
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "textDocument\?"};
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(66, 233, 112, 24, 125, 205, 254, 24)}};
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "window\?"};
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(95, 45, 82, 31, 231, 205, 122, 91)}};
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13;
static const lean_string_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "workspace\?"};
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__14_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__14_value),LEAN_SCALAR_PTR_LITERAL(3, 114, 21, 18, 79, 3, 28, 205)}};
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__15_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18;
static const lean_string_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lean\?"};
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__19 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__19_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__19_value),LEAN_SCALAR_PTR_LITERAL(113, 97, 121, 84, 79, 57, 27, 198)}};
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__20 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__20_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22;
static lean_once_cell_t l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonClientCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonClientCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonClientCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonClientCapabilities___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Lsp_ClientCapabilities_rpcWireFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_rpcWireFormat___boxed(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "moduleHierarchyProvider"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "LeanServerCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(184, 251, 61, 158, 232, 172, 150, 12)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "moduleHierarchyProvider\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__5_value),LEAN_SCALAR_PTR_LITERAL(90, 222, 123, 123, 145, 81, 54, 103)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rpcProvider"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10_value;
static const lean_string_object l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "rpcProvider\?"};
static const lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__11_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__11_value),LEAN_SCALAR_PTR_LITERAL(236, 165, 216, 88, 94, 154, 224, 77)}};
static const lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonLeanServerCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonLeanServerCapabilities___closed__0_value;
static lean_once_cell_t l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonLeanServerCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonLeanServerCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonLeanServerCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonLeanServerCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonLeanServerCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__8(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "textDocumentSync"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "completionProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "hoverProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "documentHighlightProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "documentSymbolProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "definitionProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "declarationProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "typeDefinitionProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "referencesProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "callHierarchyProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "renameProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "workspaceSymbolProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "foldingRangeProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "semanticTokensProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "codeActionProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "inlayHintProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "signatureHelpProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "colorProvider"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17_value;
static const lean_string_object l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "experimental"};
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonServerCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonServerCapabilities_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonServerCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonServerCapabilities = (const lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7_spec__14(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ServerCapabilities"};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 191, 235, 206, 233, 176, 101, 87)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3;
static const lean_string_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "textDocumentSync\?"};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__4_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(241, 190, 21, 208, 74, 247, 24, 209)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8;
static const lean_string_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "completionProvider\?"};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__9 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__9_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(76, 106, 184, 243, 136, 68, 189, 54)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 116, 162, 118, 12, 180, 32, 251)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__14 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__14_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(227, 162, 97, 82, 134, 176, 214, 16)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__18 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__18_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 176, 178, 113, 20, 18, 128, 223)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__22 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__22_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5_value),LEAN_SCALAR_PTR_LITERAL(38, 38, 131, 11, 63, 211, 60, 55)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__26 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__26_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(82, 237, 5, 103, 95, 207, 170, 187)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__30 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__30_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7_value),LEAN_SCALAR_PTR_LITERAL(157, 141, 45, 168, 21, 140, 9, 158)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__34 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__34_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8_value),LEAN_SCALAR_PTR_LITERAL(90, 96, 212, 155, 169, 220, 22, 175)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__38 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__38_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9_value),LEAN_SCALAR_PTR_LITERAL(252, 184, 155, 207, 133, 165, 237, 217)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__42 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__42_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45;
static const lean_string_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "renameProvider\?"};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__46 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__46_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__46_value),LEAN_SCALAR_PTR_LITERAL(163, 183, 148, 169, 44, 156, 33, 113)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__47 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__47_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11_value),LEAN_SCALAR_PTR_LITERAL(141, 55, 171, 62, 182, 165, 37, 21)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__51 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__51_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12_value),LEAN_SCALAR_PTR_LITERAL(140, 106, 30, 254, 164, 67, 13, 4)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__55 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__55_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58;
static const lean_string_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "semanticTokensProvider\?"};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__59 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__59_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__59_value),LEAN_SCALAR_PTR_LITERAL(111, 91, 196, 13, 189, 147, 87, 200)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__60 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__60_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63;
static const lean_string_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "codeActionProvider\?"};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__64 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__64_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__64_value),LEAN_SCALAR_PTR_LITERAL(58, 117, 200, 140, 213, 200, 118, 98)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__65 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__65_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68;
static const lean_string_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "inlayHintProvider\?"};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__69 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__69_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__69_value),LEAN_SCALAR_PTR_LITERAL(157, 78, 18, 190, 89, 32, 129, 179)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__70 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__70_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73;
static const lean_string_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "signatureHelpProvider\?"};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__74 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__74_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__74_value),LEAN_SCALAR_PTR_LITERAL(1, 207, 74, 244, 176, 203, 217, 6)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__75 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__75_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78;
static const lean_string_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "colorProvider\?"};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__79 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__79_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__79_value),LEAN_SCALAR_PTR_LITERAL(118, 33, 223, 81, 109, 180, 161, 194)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__80 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__80_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83;
static const lean_string_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "experimental\?"};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__84 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__84_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__84_value),LEAN_SCALAR_PTR_LITERAL(97, 31, 210, 10, 133, 196, 228, 90)}};
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__85 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__85_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87;
static lean_once_cell_t l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonServerCapabilities___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonServerCapabilities_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonServerCapabilities = (const lean_object*)&l_Lean_Lsp_instFromJsonServerCapabilities___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(lean_object* v_k_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
lean_dec_ref(v_k_1_);
v___x_3_ = lean_box(0);
return v___x_3_;
}
else
{
lean_object* v_val_4_; lean_object* v___x_5_; uint8_t v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_val_4_ = lean_ctor_get(v_x_2_, 0);
v___x_5_ = lean_alloc_ctor(1, 0, 1);
v___x_6_ = lean_unbox(v_val_4_);
lean_ctor_set_uint8(v___x_5_, 0, v___x_6_);
v___x_7_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_7_, 0, v_k_1_);
lean_ctor_set(v___x_7_, 1, v___x_5_);
v___x_8_ = lean_box(0);
v___x_9_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_9_, 0, v___x_7_);
lean_ctor_set(v___x_9_, 1, v___x_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0___boxed(lean_object* v_k_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v_k_10_, v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
if (lean_obj_tag(v_a_13_) == 0)
{
lean_object* v___x_15_; 
v___x_15_ = lean_array_to_list(v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_head_16_; lean_object* v_tail_17_; lean_object* v___x_18_; 
v_head_16_ = lean_ctor_get(v_a_13_, 0);
lean_inc(v_head_16_);
v_tail_17_ = lean_ctor_get(v_a_13_, 1);
lean_inc(v_tail_17_);
lean_dec_ref_known(v_a_13_, 2);
v___x_18_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_14_, v_head_16_);
v_a_13_ = v_tail_17_;
v_a_14_ = v___x_18_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson(lean_object* v_x_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_24_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__0));
v___x_25_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_24_, v_x_23_);
v___x_26_ = lean_box(0);
v___x_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_25_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
v___x_28_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_29_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_27_, v___x_28_);
v___x_30_ = l_Lean_Json_mkObj(v___x_29_);
lean_dec(v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___boxed(lean_object* v_x_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson(v_x_31_);
lean_dec(v_x_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_37_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_38_; 
v___x_38_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_38_;
}
else
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Json_getBool_x3f(v_x_37_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_39_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_39_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
else
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_56_; 
v_a_48_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_56_ == 0)
{
v___x_50_ = v___x_39_;
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_39_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_56_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v_a_48_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 0, v___x_52_);
v___x_54_ = v___x_50_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___boxed(lean_object* v_x_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0(v_x_57_);
lean_dec(v_x_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(lean_object* v_j_59_, lean_object* v_k_60_){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = l_Lean_Json_getObjValD(v_j_59_, v_k_60_);
v___x_62_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0(v___x_61_);
lean_dec(v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0___boxed(lean_object* v_j_63_, lean_object* v_k_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_j_63_, v_k_64_);
lean_dec_ref(v_k_64_);
return v_res_65_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4(void){
_start:
{
uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = 1;
v___x_74_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__3));
v___x_75_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_78_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4, &l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__4);
v___x_79_ = lean_string_append(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9(void){
_start:
{
uint8_t v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = 1;
v___x_84_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__8));
v___x_85_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_84_, v___x_83_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9, &l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__9);
v___x_87_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__6);
v___x_88_ = lean_string_append(v___x_87_, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_91_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10, &l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__10);
v___x_92_ = lean_string_append(v___x_91_, v___x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson(lean_object* v_json_93_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__0));
v___x_95_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_93_, v___x_94_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_105_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_105_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_100_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__12);
v___x_101_ = lean_string_append(v___x_100_, v_a_96_);
lean_dec(v_a_96_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_101_);
v___x_103_ = v___x_98_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_a_106_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_95_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_95_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0(lean_object* v_k_116_, lean_object* v_x_117_){
_start:
{
if (lean_obj_tag(v_x_117_) == 0)
{
lean_object* v___x_118_; 
lean_dec_ref(v_k_116_);
v___x_118_ = lean_box(0);
return v___x_118_;
}
else
{
lean_object* v_val_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_val_119_ = lean_ctor_get(v_x_117_, 0);
v___x_120_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson(v_val_119_);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_k_116_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_box(0);
v___x_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0(v_k_124_, v_x_125_);
lean_dec(v_x_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson(lean_object* v_x_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_129_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0));
v___x_130_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0(v___x_129_, v_x_128_);
v___x_131_ = lean_box(0);
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_134_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_132_, v___x_133_);
v___x_135_ = l_Lean_Json_mkObj(v___x_134_);
lean_dec(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___boxed(lean_object* v_x_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson(v_x_136_);
lean_dec(v_x_136_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v___x_143_; 
v___x_143_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson(v_x_142_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_161_; 
v_a_153_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_161_ == 0)
{
v___x_155_ = v___x_144_;
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_144_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v_a_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_157_);
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0(lean_object* v_j_162_, lean_object* v_k_163_){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = l_Lean_Json_getObjValD(v_j_162_, v_k_163_);
v___x_165_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_166_, lean_object* v_k_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0(v_j_166_, v_k_167_);
lean_dec_ref(v_k_167_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = 1;
v___x_175_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1));
v___x_176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_175_, v___x_174_);
return v___x_176_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_178_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2);
v___x_179_ = lean_string_append(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = 1;
v___x_184_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__5));
v___x_185_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6);
v___x_187_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3);
v___x_188_ = lean_string_append(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_190_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7);
v___x_191_ = lean_string_append(v___x_190_, v___x_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson(lean_object* v_json_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0));
v___x_194_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0(v_json_192_, v___x_193_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_204_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_204_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_199_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8);
v___x_200_ = lean_string_append(v___x_199_, v_a_195_);
lean_dec(v_a_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_200_);
v___x_202_ = v___x_197_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_a_205_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_194_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_194_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0(lean_object* v_k_215_, lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v___x_217_; 
lean_dec_ref(v_k_215_);
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v_val_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v_val_218_ = lean_ctor_get(v_x_216_, 0);
v___x_219_ = l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson(v_val_218_);
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v_k_215_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = lean_box(0);
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0(v_k_223_, v_x_224_);
lean_dec(v_x_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__1(lean_object* v_k_226_, lean_object* v_x_227_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_object* v___x_228_; 
lean_dec_ref(v_k_226_);
v___x_228_ = lean_box(0);
return v___x_228_;
}
else
{
lean_object* v_val_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_val_229_ = lean_ctor_get(v_x_227_, 0);
lean_inc(v_val_229_);
lean_dec_ref_known(v_x_227_, 1);
v___x_230_ = l_Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson(v_val_229_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_k_226_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
return v___x_233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__2(lean_object* v_k_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_235_) == 0)
{
lean_object* v___x_236_; 
lean_dec_ref(v_k_234_);
v___x_236_ = lean_box(0);
return v___x_236_;
}
else
{
lean_object* v_val_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v_val_237_ = lean_ctor_get(v_x_235_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v_x_235_, 1);
v___x_238_ = l_Lean_Lsp_instToJsonInlayHintClientCapabilities_toJson(v_val_237_);
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v_k_234_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson(lean_object* v_x_245_){
_start:
{
lean_object* v_completion_x3f_246_; lean_object* v_codeAction_x3f_247_; lean_object* v_inlayHint_x3f_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_completion_x3f_246_ = lean_ctor_get(v_x_245_, 0);
lean_inc(v_completion_x3f_246_);
v_codeAction_x3f_247_ = lean_ctor_get(v_x_245_, 1);
lean_inc(v_codeAction_x3f_247_);
v_inlayHint_x3f_248_ = lean_ctor_get(v_x_245_, 2);
lean_inc(v_inlayHint_x3f_248_);
lean_dec_ref(v_x_245_);
v___x_249_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0));
v___x_250_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0(v___x_249_, v_completion_x3f_246_);
lean_dec(v_completion_x3f_246_);
v___x_251_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1));
v___x_252_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__1(v___x_251_, v_codeAction_x3f_247_);
v___x_253_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2));
v___x_254_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__2(v___x_253_, v_inlayHint_x3f_248_);
v___x_255_ = lean_box(0);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_252_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_250_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_260_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_258_, v___x_259_);
v___x_261_ = l_Lean_Json_mkObj(v___x_260_);
lean_dec(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_267_;
}
else
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson(v_x_266_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
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
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_285_; 
v_a_277_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_285_ == 0)
{
v___x_279_ = v___x_268_;
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_268_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_a_277_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_283_ = v___x_279_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1(lean_object* v_j_286_, lean_object* v_k_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = l_Lean_Json_getObjValD(v_j_286_, v_k_287_);
v___x_289_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1___boxed(lean_object* v_j_290_, lean_object* v_k_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1(v_j_290_, v_k_291_);
lean_dec_ref(v_k_291_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_object* v___x_296_; 
v___x_296_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_296_;
}
else
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson(v_x_295_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
else
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
v_a_306_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_314_ == 0)
{
v___x_308_ = v___x_297_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_297_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v_a_306_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0(lean_object* v_j_315_, lean_object* v_k_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l_Lean_Json_getObjValD(v_j_315_, v_k_316_);
v___x_318_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_319_, lean_object* v_k_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0(v_j_319_, v_k_320_);
lean_dec_ref(v_k_320_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4(lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v___x_325_; 
v___x_325_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4___closed__0));
return v___x_325_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Lsp_instFromJsonInlayHintClientCapabilities_fromJson(v_x_324_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
v_a_335_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_343_ == 0)
{
v___x_337_ = v___x_326_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_326_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v_a_335_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v___x_339_);
v___x_341_ = v___x_337_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2(lean_object* v_j_344_, lean_object* v_k_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = l_Lean_Json_getObjValD(v_j_344_, v_k_345_);
v___x_347_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4(v___x_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2___boxed(lean_object* v_j_348_, lean_object* v_k_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2(v_j_348_, v_k_349_);
lean_dec_ref(v_k_349_);
return v_res_350_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = 1;
v___x_357_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1));
v___x_358_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_357_, v___x_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_360_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2);
v___x_361_ = lean_string_append(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = 1;
v___x_366_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__5));
v___x_367_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_366_, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_368_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6);
v___x_369_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3);
v___x_370_ = lean_string_append(v___x_369_, v___x_368_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_372_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7);
v___x_373_ = lean_string_append(v___x_372_, v___x_371_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_377_ = 1;
v___x_378_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__10));
v___x_379_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_378_, v___x_377_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_380_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11);
v___x_381_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3);
v___x_382_ = lean_string_append(v___x_381_, v___x_380_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_383_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_384_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12);
v___x_385_ = lean_string_append(v___x_384_, v___x_383_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_389_ = 1;
v___x_390_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__15));
v___x_391_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_390_, v___x_389_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16);
v___x_393_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3);
v___x_394_ = lean_string_append(v___x_393_, v___x_392_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_396_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17);
v___x_397_ = lean_string_append(v___x_396_, v___x_395_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson(lean_object* v_json_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0));
lean_inc(v_json_398_);
v___x_400_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0(v_json_398_, v___x_399_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_json_398_);
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_410_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_410_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_410_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v___x_405_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8);
v___x_406_ = lean_string_append(v___x_405_, v_a_401_);
lean_dec(v_a_401_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_406_);
v___x_408_ = v___x_403_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_a_411_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_400_, 1);
v___x_412_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1));
lean_inc(v_json_398_);
v___x_413_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1(v_json_398_, v___x_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_a_411_);
lean_dec(v_json_398_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_423_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_418_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13);
v___x_419_ = lean_string_append(v___x_418_, v_a_414_);
lean_dec(v_a_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_419_);
v___x_421_ = v___x_416_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_a_424_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_413_, 1);
v___x_425_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2));
v___x_426_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2(v_json_398_, v___x_425_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_a_424_);
lean_dec(v_a_411_);
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_436_ == 0)
{
v___x_429_ = v___x_426_;
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_426_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_431_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18);
v___x_432_ = lean_string_append(v___x_431_, v_a_427_);
lean_dec(v_a_427_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 0, v___x_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_445_; 
v_a_437_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_445_ == 0)
{
v___x_439_ = v___x_426_;
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_426_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_445_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_441_, 0, v_a_411_);
lean_ctor_set(v___x_441_, 1, v_a_424_);
lean_ctor_set(v___x_441_, 2, v_a_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(uint8_t v_x_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_450_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0));
v___x_451_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_451_, 0, v_x_449_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_450_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = lean_box(0);
v___x_454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v___x_453_);
v___x_456_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_457_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_455_, v___x_456_);
v___x_458_ = l_Lean_Json_mkObj(v___x_457_);
lean_dec(v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___boxed(lean_object* v_x_459_){
_start:
{
uint8_t v_x_29__boxed_460_; lean_object* v_res_461_; 
v_x_29__boxed_460_ = lean_unbox(v_x_459_);
v_res_461_ = l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(v_x_29__boxed_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(lean_object* v_j_464_, lean_object* v_k_465_){
_start:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = l_Lean_Json_getObjValD(v_j_464_, v_k_465_);
v___x_467_ = l_Lean_Json_getBool_x3f(v___x_466_);
lean_dec(v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_468_, lean_object* v_k_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_j_468_, v_k_469_);
lean_dec_ref(v_k_469_);
return v_res_470_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = 1;
v___x_477_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1));
v___x_478_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_480_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2);
v___x_481_ = lean_string_append(v___x_480_, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5(void){
_start:
{
uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = 1;
v___x_485_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__4));
v___x_486_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_485_, v___x_484_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5);
v___x_488_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3);
v___x_489_ = lean_string_append(v___x_488_, v___x_487_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_491_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6);
v___x_492_ = lean_string_append(v___x_491_, v___x_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson(lean_object* v_json_493_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0));
v___x_495_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_493_, v___x_494_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_505_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_505_ == 0)
{
v___x_498_ = v___x_495_;
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_495_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_505_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_500_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7);
v___x_501_ = lean_string_append(v___x_500_, v_a_496_);
lean_dec(v_a_496_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_501_);
v___x_503_ = v___x_498_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_a_506_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_495_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_495_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(lean_object* v_k_516_, lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v___x_518_; 
lean_dec_ref(v_k_516_);
v___x_518_ = lean_box(0);
return v___x_518_;
}
else
{
lean_object* v_val_519_; uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_val_519_ = lean_ctor_get(v_x_517_, 0);
v___x_520_ = lean_unbox(v_val_519_);
v___x_521_ = l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(v___x_520_);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v_k_516_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_525_, lean_object* v_x_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(v_k_525_, v_x_526_);
lean_dec(v_x_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_530_ = ((lean_object*)(l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0));
v___x_531_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(v___x_530_, v_x_529_);
v___x_532_ = lean_box(0);
v___x_533_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_535_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_533_, v___x_534_);
v___x_536_ = l_Lean_Json_mkObj(v___x_535_);
lean_dec(v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___boxed(lean_object* v_x_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(v_x_537_);
lean_dec(v_x_537_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_541_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v___x_542_; 
v___x_542_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson(v_x_541_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_560_; 
v_a_552_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_560_ == 0)
{
v___x_554_ = v___x_543_;
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_543_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_560_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_556_, 0, v_a_552_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_556_);
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(lean_object* v_j_561_, lean_object* v_k_562_){
_start:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = l_Lean_Json_getObjValD(v_j_561_, v_k_562_);
v___x_564_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0_spec__0(v___x_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_565_, lean_object* v_k_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(v_j_565_, v_k_566_);
lean_dec_ref(v_k_566_);
return v_res_567_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = 1;
v___x_574_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1));
v___x_575_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_574_, v___x_573_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_577_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2);
v___x_578_ = lean_string_append(v___x_577_, v___x_576_);
return v___x_578_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = 1;
v___x_583_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__5));
v___x_584_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6);
v___x_586_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3);
v___x_587_ = lean_string_append(v___x_586_, v___x_585_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_589_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7);
v___x_590_ = lean_string_append(v___x_589_, v___x_588_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson(lean_object* v_json_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0));
v___x_593_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(v_json_591_, v___x_592_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_603_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_603_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_603_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_598_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8);
v___x_599_ = lean_string_append(v___x_598_, v_a_594_);
lean_dec(v_a_594_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_599_);
v___x_601_ = v___x_596_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
v_a_604_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_593_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_593_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(lean_object* v_x_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_616_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0));
v___x_617_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_616_, v_x_615_);
v___x_618_ = lean_box(0);
v___x_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_621_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_619_, v___x_620_);
v___x_622_ = l_Lean_Json_mkObj(v___x_621_);
lean_dec(v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___boxed(lean_object* v_x_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(v_x_623_);
lean_dec(v_x_623_);
return v_res_624_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2(void){
_start:
{
uint8_t v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = 1;
v___x_633_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1));
v___x_634_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_633_, v___x_632_);
return v___x_634_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_635_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_636_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2);
v___x_637_ = lean_string_append(v___x_636_, v___x_635_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6(void){
_start:
{
uint8_t v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = 1;
v___x_642_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__5));
v___x_643_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_642_, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6);
v___x_645_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3);
v___x_646_ = lean_string_append(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_648_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7);
v___x_649_ = lean_string_append(v___x_648_, v___x_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson(lean_object* v_json_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0));
v___x_652_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_650_, v___x_651_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_662_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_662_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_662_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_657_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8);
v___x_658_ = lean_string_append(v___x_657_, v_a_653_);
lean_dec(v_a_653_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_658_);
v___x_660_ = v___x_655_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
v_a_663_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_652_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_652_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(lean_object* v_k_673_, lean_object* v_x_674_){
_start:
{
if (lean_obj_tag(v_x_674_) == 0)
{
lean_object* v___x_675_; 
lean_dec_ref(v_k_673_);
v___x_675_ = lean_box(0);
return v___x_675_;
}
else
{
lean_object* v_val_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v_val_676_ = lean_ctor_get(v_x_674_, 0);
v___x_677_ = l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(v_val_676_);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_k_673_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = lean_box(0);
v___x_680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
return v___x_680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_681_, lean_object* v_x_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(v_k_681_, v_x_682_);
lean_dec(v_x_682_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(size_t v_sz_684_, size_t v_i_685_, lean_object* v_bs_686_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_lt(v_i_685_, v_sz_684_);
if (v___x_687_ == 0)
{
return v_bs_686_;
}
else
{
lean_object* v_v_688_; lean_object* v___x_689_; lean_object* v_bs_x27_690_; lean_object* v___x_691_; size_t v___x_692_; size_t v___x_693_; lean_object* v___x_694_; 
v_v_688_ = lean_array_uget(v_bs_686_, v_i_685_);
v___x_689_ = lean_unsigned_to_nat(0u);
v_bs_x27_690_ = lean_array_uset(v_bs_686_, v_i_685_, v___x_689_);
v___x_691_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_691_, 0, v_v_688_);
v___x_692_ = ((size_t)1ULL);
v___x_693_ = lean_usize_add(v_i_685_, v___x_692_);
v___x_694_ = lean_array_uset(v_bs_x27_690_, v_i_685_, v___x_691_);
v_i_685_ = v___x_693_;
v_bs_686_ = v___x_694_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_696_, lean_object* v_i_697_, lean_object* v_bs_698_){
_start:
{
size_t v_sz_boxed_699_; size_t v_i_boxed_700_; lean_object* v_res_701_; 
v_sz_boxed_699_ = lean_unbox_usize(v_sz_696_);
lean_dec(v_sz_696_);
v_i_boxed_700_ = lean_unbox_usize(v_i_697_);
lean_dec(v_i_697_);
v_res_701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(v_sz_boxed_699_, v_i_boxed_700_, v_bs_698_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1(lean_object* v_a_702_){
_start:
{
size_t v_sz_703_; size_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_sz_703_ = lean_array_size(v_a_702_);
v___x_704_ = ((size_t)0ULL);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(v_sz_703_, v___x_704_, v_a_702_);
v___x_706_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1(lean_object* v_k_707_, lean_object* v_x_708_){
_start:
{
if (lean_obj_tag(v_x_708_) == 0)
{
lean_object* v___x_709_; 
lean_dec_ref(v_k_707_);
v___x_709_ = lean_box(0);
return v___x_709_;
}
else
{
lean_object* v_val_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_val_710_ = lean_ctor_get(v_x_708_, 0);
lean_inc(v_val_710_);
lean_dec_ref_known(v_x_708_, 1);
v___x_711_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1(v_val_710_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_k_707_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson(lean_object* v_x_718_){
_start:
{
lean_object* v_documentChanges_x3f_719_; lean_object* v_changeAnnotationSupport_x3f_720_; lean_object* v_resourceOperations_x3f_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v_documentChanges_x3f_719_ = lean_ctor_get(v_x_718_, 0);
lean_inc(v_documentChanges_x3f_719_);
v_changeAnnotationSupport_x3f_720_ = lean_ctor_get(v_x_718_, 1);
lean_inc(v_changeAnnotationSupport_x3f_720_);
v_resourceOperations_x3f_721_ = lean_ctor_get(v_x_718_, 2);
lean_inc(v_resourceOperations_x3f_721_);
lean_dec_ref(v_x_718_);
v___x_722_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0));
v___x_723_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_722_, v_documentChanges_x3f_719_);
lean_dec(v_documentChanges_x3f_719_);
v___x_724_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1));
v___x_725_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(v___x_724_, v_changeAnnotationSupport_x3f_720_);
lean_dec(v_changeAnnotationSupport_x3f_720_);
v___x_726_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2));
v___x_727_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1(v___x_726_, v_resourceOperations_x3f_721_);
v___x_728_ = lean_box(0);
v___x_729_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_725_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_723_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_733_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_731_, v___x_732_);
v___x_734_ = l_Lean_Json_mkObj(v___x_733_);
lean_dec(v___x_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(size_t v_sz_737_, size_t v_i_738_, lean_object* v_bs_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = lean_usize_dec_lt(v_i_738_, v_sz_737_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_bs_739_);
return v___x_741_;
}
else
{
lean_object* v_v_742_; lean_object* v___x_743_; 
v_v_742_ = lean_array_uget_borrowed(v_bs_739_, v_i_738_);
lean_inc(v_v_742_);
v___x_743_ = l_Lean_Json_getStr_x3f(v_v_742_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec_ref(v_bs_739_);
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v_bs_x27_754_; size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v_a_752_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_743_, 1);
v___x_753_ = lean_unsigned_to_nat(0u);
v_bs_x27_754_ = lean_array_uset(v_bs_739_, v_i_738_, v___x_753_);
v___x_755_ = ((size_t)1ULL);
v___x_756_ = lean_usize_add(v_i_738_, v___x_755_);
v___x_757_ = lean_array_uset(v_bs_x27_754_, v_i_738_, v_a_752_);
v_i_738_ = v___x_756_;
v_bs_739_ = v___x_757_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_759_, lean_object* v_i_760_, lean_object* v_bs_761_){
_start:
{
size_t v_sz_boxed_762_; size_t v_i_boxed_763_; lean_object* v_res_764_; 
v_sz_boxed_762_ = lean_unbox_usize(v_sz_759_);
lean_dec(v_sz_759_);
v_i_boxed_763_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(v_sz_boxed_762_, v_i_boxed_763_, v_bs_761_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3(lean_object* v_x_767_){
_start:
{
if (lean_obj_tag(v_x_767_) == 4)
{
lean_object* v_elems_768_; size_t v_sz_769_; size_t v___x_770_; lean_object* v___x_771_; 
v_elems_768_ = lean_ctor_get(v_x_767_, 0);
lean_inc_ref(v_elems_768_);
lean_dec_ref_known(v_x_767_, 1);
v_sz_769_ = lean_array_size(v_elems_768_);
v___x_770_ = ((size_t)0ULL);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(v_sz_769_, v___x_770_, v_elems_768_);
return v___x_771_;
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_772_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__0));
v___x_773_ = lean_unsigned_to_nat(80u);
v___x_774_ = l_Lean_Json_pretty(v_x_767_, v___x_773_);
v___x_775_ = lean_string_append(v___x_772_, v___x_774_);
lean_dec_ref(v___x_774_);
v___x_776_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__1));
v___x_777_ = lean_string_append(v___x_775_, v___x_776_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_781_) == 0)
{
lean_object* v___x_782_; 
v___x_782_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_782_;
}
else
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3(v_x_781_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_800_; 
v_a_792_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_800_ == 0)
{
v___x_794_ = v___x_783_;
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_783_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_800_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v_a_792_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(lean_object* v_j_801_, lean_object* v_k_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = l_Lean_Json_getObjValD(v_j_801_, v_k_802_);
v___x_804_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2(v___x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1___boxed(lean_object* v_j_805_, lean_object* v_k_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(v_j_805_, v_k_806_);
lean_dec_ref(v_k_806_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_808_){
_start:
{
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v___x_809_; 
v___x_809_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_809_;
}
else
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson(v_x_808_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_827_; 
v_a_819_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_827_ == 0)
{
v___x_821_ = v___x_810_;
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_810_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_827_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_a_819_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_823_);
v___x_825_ = v___x_821_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(lean_object* v_j_828_, lean_object* v_k_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = l_Lean_Json_getObjValD(v_j_828_, v_k_829_);
v___x_831_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0_spec__0(v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_832_, lean_object* v_k_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(v_j_832_, v_k_833_);
lean_dec_ref(v_k_833_);
return v_res_834_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_840_ = 1;
v___x_841_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1));
v___x_842_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_841_, v___x_840_);
return v___x_842_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_843_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_844_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2);
v___x_845_ = lean_string_append(v___x_844_, v___x_843_);
return v___x_845_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = 1;
v___x_850_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__5));
v___x_851_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_850_, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6);
v___x_853_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3);
v___x_854_ = lean_string_append(v___x_853_, v___x_852_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_856_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7);
v___x_857_ = lean_string_append(v___x_856_, v___x_855_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = 1;
v___x_862_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__10));
v___x_863_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_862_, v___x_861_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11);
v___x_865_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3);
v___x_866_ = lean_string_append(v___x_865_, v___x_864_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_868_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12);
v___x_869_ = lean_string_append(v___x_868_, v___x_867_);
return v___x_869_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = 1;
v___x_874_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__15));
v___x_875_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_874_, v___x_873_);
return v___x_875_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16);
v___x_877_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3);
v___x_878_ = lean_string_append(v___x_877_, v___x_876_);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_880_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17);
v___x_881_ = lean_string_append(v___x_880_, v___x_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson(lean_object* v_json_882_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0));
lean_inc(v_json_882_);
v___x_884_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_882_, v___x_883_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_894_; 
lean_dec(v_json_882_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_894_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_894_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_889_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8);
v___x_890_ = lean_string_append(v___x_889_, v_a_885_);
lean_dec(v_a_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_890_);
v___x_892_ = v___x_887_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_a_895_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v___x_884_, 1);
v___x_896_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1));
lean_inc(v_json_882_);
v___x_897_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(v_json_882_, v___x_896_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_a_895_);
lean_dec(v_json_882_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_907_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_907_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_907_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_902_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13);
v___x_903_ = lean_string_append(v___x_902_, v_a_898_);
lean_dec(v_a_898_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_903_);
v___x_905_ = v___x_900_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_a_908_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_897_, 1);
v___x_909_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2));
v___x_910_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(v_json_882_, v___x_909_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_a_908_);
lean_dec(v_a_895_);
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_920_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_920_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_920_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_915_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18);
v___x_916_ = lean_string_append(v___x_915_, v_a_911_);
lean_dec(v_a_911_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_916_);
v___x_918_ = v___x_913_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_929_; 
v_a_921_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_929_ == 0)
{
v___x_923_ = v___x_910_;
v_isShared_924_ = v_isSharedCheck_929_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_910_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_929_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_925_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_925_, 0, v_a_895_);
lean_ctor_set(v___x_925_, 1, v_a_908_);
lean_ctor_set(v___x_925_, 2, v_a_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_925_);
v___x_927_ = v___x_923_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson_spec__0(lean_object* v_k_932_, lean_object* v_x_933_){
_start:
{
if (lean_obj_tag(v_x_933_) == 0)
{
lean_object* v___x_934_; 
lean_dec_ref(v_k_932_);
v___x_934_ = lean_box(0);
return v___x_934_;
}
else
{
lean_object* v_val_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_val_935_ = lean_ctor_get(v_x_933_, 0);
lean_inc(v_val_935_);
lean_dec_ref_known(v_x_933_, 1);
v___x_936_ = l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson(v_val_935_);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_k_932_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_box(0);
v___x_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson(lean_object* v_x_942_){
_start:
{
lean_object* v_applyEdit_x3f_943_; lean_object* v_workspaceEdit_x3f_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_960_; 
v_applyEdit_x3f_943_ = lean_ctor_get(v_x_942_, 0);
v_workspaceEdit_x3f_944_ = lean_ctor_get(v_x_942_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v_x_942_);
if (v_isSharedCheck_960_ == 0)
{
v___x_946_ = v_x_942_;
v_isShared_947_ = v_isSharedCheck_960_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_workspaceEdit_x3f_944_);
lean_inc(v_applyEdit_x3f_943_);
lean_dec(v_x_942_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_960_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_948_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0));
v___x_949_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_948_, v_applyEdit_x3f_943_);
lean_dec(v_applyEdit_x3f_943_);
v___x_950_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1));
v___x_951_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson_spec__0(v___x_950_, v_workspaceEdit_x3f_944_);
v___x_952_ = lean_box(0);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 1);
lean_ctor_set(v___x_946_, 1, v___x_952_);
lean_ctor_set(v___x_946_, 0, v___x_951_);
v___x_954_ = v___x_946_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v___x_952_);
v___x_954_ = v_reuseFailAlloc_959_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_949_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_957_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_955_, v___x_956_);
v___x_958_ = l_Lean_Json_mkObj(v___x_957_);
lean_dec(v___x_957_);
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_965_){
_start:
{
if (lean_obj_tag(v_x_965_) == 0)
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_966_;
}
else
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson(v_x_965_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_984_; 
v_a_976_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_984_ == 0)
{
v___x_978_ = v___x_967_;
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_967_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_984_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v_a_976_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_980_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(lean_object* v_j_985_, lean_object* v_k_986_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; 
v___x_987_ = l_Lean_Json_getObjValD(v_j_985_, v_k_986_);
v___x_988_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0(v___x_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_989_, lean_object* v_k_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(v_j_989_, v_k_990_);
lean_dec_ref(v_k_990_);
return v_res_991_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = 1;
v___x_998_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1));
v___x_999_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_998_, v___x_997_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1001_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2);
v___x_1002_ = lean_string_append(v___x_1001_, v___x_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = 1;
v___x_1007_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__5));
v___x_1008_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1007_, v___x_1006_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6);
v___x_1010_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3);
v___x_1011_ = lean_string_append(v___x_1010_, v___x_1009_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1013_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7);
v___x_1014_ = lean_string_append(v___x_1013_, v___x_1012_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = 1;
v___x_1019_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__10));
v___x_1020_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1019_, v___x_1018_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1021_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11);
v___x_1022_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3);
v___x_1023_ = lean_string_append(v___x_1022_, v___x_1021_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1024_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1025_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12);
v___x_1026_ = lean_string_append(v___x_1025_, v___x_1024_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson(lean_object* v_json_1027_){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0));
lean_inc(v_json_1027_);
v___x_1029_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_1027_, v___x_1028_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_json_1027_);
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1039_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1039_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1034_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8);
v___x_1035_ = lean_string_append(v___x_1034_, v_a_1030_);
lean_dec(v_a_1030_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1035_);
v___x_1037_ = v___x_1032_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_a_1040_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1029_, 1);
v___x_1041_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1));
v___x_1042_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(v_json_1027_, v___x_1041_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1052_; 
lean_dec(v_a_1040_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1052_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1052_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1047_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13);
v___x_1048_ = lean_string_append(v___x_1047_, v_a_1043_);
lean_dec(v_a_1043_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 0, v___x_1048_);
v___x_1050_ = v___x_1045_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
else
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1061_; 
v_a_1053_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1055_ = v___x_1042_;
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1042_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1061_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_a_1040_);
lean_ctor_set(v___x_1057_, 1, v_a_1053_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1057_);
v___x_1059_ = v___x_1055_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(lean_object* v_k_1064_, lean_object* v_x_1065_){
_start:
{
if (lean_obj_tag(v_x_1065_) == 0)
{
lean_object* v___x_1066_; 
lean_dec_ref(v_k_1064_);
v___x_1066_ = lean_box(0);
return v___x_1066_;
}
else
{
lean_object* v_val_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_val_1067_ = lean_ctor_get(v_x_1065_, 0);
v___x_1068_ = lean_unbox(v_val_1067_);
v___x_1069_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v___x_1068_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v_k_1064_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_1073_, lean_object* v_x_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(v_k_1073_, v_x_1074_);
lean_dec(v_x_1074_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(lean_object* v_x_1079_){
_start:
{
lean_object* v_incrementalDiagnosticSupport_x3f_1080_; lean_object* v_silentDiagnosticSupport_x3f_1081_; lean_object* v_rpcWireFormat_x3f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_incrementalDiagnosticSupport_x3f_1080_ = lean_ctor_get(v_x_1079_, 0);
v_silentDiagnosticSupport_x3f_1081_ = lean_ctor_get(v_x_1079_, 1);
v_rpcWireFormat_x3f_1082_ = lean_ctor_get(v_x_1079_, 2);
v___x_1083_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0));
v___x_1084_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_1083_, v_incrementalDiagnosticSupport_x3f_1080_);
v___x_1085_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1));
v___x_1086_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_1085_, v_silentDiagnosticSupport_x3f_1081_);
v___x_1087_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2));
v___x_1088_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(v___x_1087_, v_rpcWireFormat_x3f_1082_);
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1086_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1084_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1094_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1092_, v___x_1093_);
v___x_1095_ = l_Lean_Json_mkObj(v___x_1094_);
lean_dec(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___boxed(lean_object* v_x_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(v_x_1096_);
lean_dec_ref(v_x_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1102_){
_start:
{
if (lean_obj_tag(v_x_1102_) == 0)
{
lean_object* v___x_1103_; 
v___x_1103_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1103_;
}
else
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(v_x_1102_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1104_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1104_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1121_; 
v_a_1113_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1115_ = v___x_1104_;
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1104_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1121_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_a_1113_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1117_);
v___x_1119_ = v___x_1115_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(lean_object* v_j_1122_, lean_object* v_k_1123_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = l_Lean_Json_getObjValD(v_j_1122_, v_k_1123_);
v___x_1125_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0(v___x_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1126_, lean_object* v_k_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(v_j_1126_, v_k_1127_);
lean_dec_ref(v_k_1127_);
return v_res_1128_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1134_ = 1;
v___x_1135_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1));
v___x_1136_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1135_, v___x_1134_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1138_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2);
v___x_1139_ = lean_string_append(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = 1;
v___x_1144_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__5));
v___x_1145_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1144_, v___x_1143_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6);
v___x_1147_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3);
v___x_1148_ = lean_string_append(v___x_1147_, v___x_1146_);
return v___x_1148_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1150_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7);
v___x_1151_ = lean_string_append(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = 1;
v___x_1156_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__10));
v___x_1157_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1156_, v___x_1155_);
return v___x_1157_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11);
v___x_1159_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3);
v___x_1160_ = lean_string_append(v___x_1159_, v___x_1158_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1162_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12);
v___x_1163_ = lean_string_append(v___x_1162_, v___x_1161_);
return v___x_1163_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = 1;
v___x_1168_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__15));
v___x_1169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1168_, v___x_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16);
v___x_1171_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3);
v___x_1172_ = lean_string_append(v___x_1171_, v___x_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1174_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17);
v___x_1175_ = lean_string_append(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson(lean_object* v_json_1176_){
_start:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0));
lean_inc(v_json_1176_);
v___x_1178_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_1176_, v___x_1177_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_json_1176_);
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1181_ = v___x_1178_;
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1178_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1183_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8);
v___x_1184_ = lean_string_append(v___x_1183_, v_a_1179_);
lean_dec(v_a_1179_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1184_);
v___x_1186_ = v___x_1181_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_a_1189_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1178_, 1);
v___x_1190_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1));
lean_inc(v_json_1176_);
v___x_1191_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_1176_, v___x_1190_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_a_1189_);
lean_dec(v_json_1176_);
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1201_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1201_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1196_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13);
v___x_1197_ = lean_string_append(v___x_1196_, v_a_1192_);
lean_dec(v_a_1192_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1197_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_a_1202_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1191_, 1);
v___x_1203_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2));
v___x_1204_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(v_json_1176_, v___x_1203_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_a_1202_);
lean_dec(v_a_1189_);
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1214_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1214_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1209_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18);
v___x_1210_ = lean_string_append(v___x_1209_, v_a_1205_);
lean_dec(v_a_1205_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 0, v___x_1210_);
v___x_1212_ = v___x_1207_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
v_a_1215_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v___x_1204_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1204_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1219_, 0, v_a_1189_);
lean_ctor_set(v___x_1219_, 1, v_a_1202_);
lean_ctor_set(v___x_1219_, 2, v_a_1215_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__0(lean_object* v_k_1226_, lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref(v_k_1226_);
v___x_1228_ = lean_box(0);
return v___x_1228_;
}
else
{
lean_object* v_val_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v_val_1229_ = lean_ctor_get(v_x_1227_, 0);
lean_inc(v_val_1229_);
lean_dec_ref_known(v_x_1227_, 1);
v___x_1230_ = l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson(v_val_1229_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v_k_1226_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = lean_box(0);
v___x_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1231_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(lean_object* v_k_1234_, lean_object* v_x_1235_){
_start:
{
if (lean_obj_tag(v_x_1235_) == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref(v_k_1234_);
v___x_1236_ = lean_box(0);
return v___x_1236_;
}
else
{
lean_object* v_val_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_val_1237_ = lean_ctor_get(v_x_1235_, 0);
v___x_1238_ = l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(v_val_1237_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_k_1234_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1___boxed(lean_object* v_k_1242_, lean_object* v_x_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(v_k_1242_, v_x_1243_);
lean_dec(v_x_1243_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__2(lean_object* v_k_1245_, lean_object* v_x_1246_){
_start:
{
if (lean_obj_tag(v_x_1246_) == 0)
{
lean_object* v___x_1247_; 
lean_dec_ref(v_k_1245_);
v___x_1247_ = lean_box(0);
return v___x_1247_;
}
else
{
lean_object* v_val_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_val_1248_ = lean_ctor_get(v_x_1246_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v_x_1246_, 1);
v___x_1249_ = l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson(v_val_1248_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v_k_1245_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1250_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(lean_object* v_k_1253_, lean_object* v_x_1254_){
_start:
{
if (lean_obj_tag(v_x_1254_) == 0)
{
lean_object* v___x_1255_; 
lean_dec_ref(v_k_1253_);
v___x_1255_ = lean_box(0);
return v___x_1255_;
}
else
{
lean_object* v_val_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_val_1256_ = lean_ctor_get(v_x_1254_, 0);
v___x_1257_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(v_val_1256_);
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_k_1253_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_box(0);
v___x_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3___boxed(lean_object* v_k_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(v_k_1261_, v_x_1262_);
lean_dec(v_x_1262_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonClientCapabilities_toJson(lean_object* v_x_1268_){
_start:
{
lean_object* v_textDocument_x3f_1269_; lean_object* v_window_x3f_1270_; lean_object* v_workspace_x3f_1271_; lean_object* v_lean_x3f_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_textDocument_x3f_1269_ = lean_ctor_get(v_x_1268_, 0);
lean_inc(v_textDocument_x3f_1269_);
v_window_x3f_1270_ = lean_ctor_get(v_x_1268_, 1);
lean_inc(v_window_x3f_1270_);
v_workspace_x3f_1271_ = lean_ctor_get(v_x_1268_, 2);
lean_inc(v_workspace_x3f_1271_);
v_lean_x3f_1272_ = lean_ctor_get(v_x_1268_, 3);
lean_inc(v_lean_x3f_1272_);
lean_dec_ref(v_x_1268_);
v___x_1273_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0));
v___x_1274_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__0(v___x_1273_, v_textDocument_x3f_1269_);
v___x_1275_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1));
v___x_1276_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(v___x_1275_, v_window_x3f_1270_);
lean_dec(v_window_x3f_1270_);
v___x_1277_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2));
v___x_1278_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__2(v___x_1277_, v_workspace_x3f_1271_);
v___x_1279_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3));
v___x_1280_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(v___x_1279_, v_lean_x3f_1272_);
lean_dec(v_lean_x3f_1272_);
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1278_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1276_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1274_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1287_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1285_, v___x_1286_);
v___x_1288_ = l_Lean_Json_mkObj(v___x_1287_);
lean_dec(v___x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4(lean_object* v_x_1293_){
_start:
{
if (lean_obj_tag(v_x_1293_) == 0)
{
lean_object* v___x_1294_; 
v___x_1294_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4___closed__0));
return v___x_1294_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson(v_x_1293_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1312_; 
v_a_1304_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1306_ = v___x_1295_;
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1295_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_a_1304_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1308_);
v___x_1310_ = v___x_1306_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(lean_object* v_j_1313_, lean_object* v_k_1314_){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = l_Lean_Json_getObjValD(v_j_1313_, v_k_1314_);
v___x_1316_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4(v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2___boxed(lean_object* v_j_1317_, lean_object* v_k_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(v_j_1317_, v_k_1318_);
lean_dec_ref(v_k_1318_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6(lean_object* v_x_1322_){
_start:
{
if (lean_obj_tag(v_x_1322_) == 0)
{
lean_object* v___x_1323_; 
v___x_1323_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6___closed__0));
return v___x_1323_;
}
else
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson(v_x_1322_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1341_; 
v_a_1333_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1335_ = v___x_1324_;
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1324_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1341_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_a_1333_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1337_);
v___x_1339_ = v___x_1335_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(lean_object* v_j_1342_, lean_object* v_k_1343_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = l_Lean_Json_getObjValD(v_j_1342_, v_k_1343_);
v___x_1345_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6(v___x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3___boxed(lean_object* v_j_1346_, lean_object* v_k_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(v_j_1346_, v_k_1347_);
lean_dec_ref(v_k_1347_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_1349_){
_start:
{
if (lean_obj_tag(v_x_1349_) == 0)
{
lean_object* v___x_1350_; 
v___x_1350_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson(v_x_1349_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1368_; 
v_a_1360_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1362_ = v___x_1351_;
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1351_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1368_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_a_1360_);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 0, v___x_1364_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1364_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(lean_object* v_j_1369_, lean_object* v_k_1370_){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = l_Lean_Json_getObjValD(v_j_1369_, v_k_1370_);
v___x_1372_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1_spec__2(v___x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1___boxed(lean_object* v_j_1373_, lean_object* v_k_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(v_j_1373_, v_k_1374_);
lean_dec_ref(v_k_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1378_){
_start:
{
if (lean_obj_tag(v_x_1378_) == 0)
{
lean_object* v___x_1379_; 
v___x_1379_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1379_;
}
else
{
lean_object* v___x_1380_; 
v___x_1380_ = l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson(v_x_1378_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1397_; 
v_a_1389_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1391_ = v___x_1380_;
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1380_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1397_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1393_, 0, v_a_1389_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1395_ = v___x_1391_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1393_);
v___x_1395_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
return v___x_1395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(lean_object* v_j_1398_, lean_object* v_k_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = l_Lean_Json_getObjValD(v_j_1398_, v_k_1399_);
v___x_1401_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0(v___x_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1402_, lean_object* v_k_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(v_j_1402_, v_k_1403_);
lean_dec_ref(v_k_1403_);
return v_res_1404_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1410_ = 1;
v___x_1411_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1));
v___x_1412_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1411_, v___x_1410_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1414_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2);
v___x_1415_ = lean_string_append(v___x_1414_, v___x_1413_);
return v___x_1415_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = 1;
v___x_1420_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__5));
v___x_1421_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1420_, v___x_1419_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6);
v___x_1423_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1424_ = lean_string_append(v___x_1423_, v___x_1422_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1426_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7);
v___x_1427_ = lean_string_append(v___x_1426_, v___x_1425_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1431_ = 1;
v___x_1432_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__10));
v___x_1433_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1432_, v___x_1431_);
return v___x_1433_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11);
v___x_1435_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1436_ = lean_string_append(v___x_1435_, v___x_1434_);
return v___x_1436_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1438_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12);
v___x_1439_ = lean_string_append(v___x_1438_, v___x_1437_);
return v___x_1439_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = 1;
v___x_1444_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__15));
v___x_1445_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1444_, v___x_1443_);
return v___x_1445_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16);
v___x_1447_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1448_ = lean_string_append(v___x_1447_, v___x_1446_);
return v___x_1448_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1450_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17);
v___x_1451_ = lean_string_append(v___x_1450_, v___x_1449_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = 1;
v___x_1456_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__20));
v___x_1457_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1456_, v___x_1455_);
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21);
v___x_1459_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1460_ = lean_string_append(v___x_1459_, v___x_1458_);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1462_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22);
v___x_1463_ = lean_string_append(v___x_1462_, v___x_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson(lean_object* v_json_1464_){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0));
lean_inc(v_json_1464_);
v___x_1466_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(v_json_1464_, v___x_1465_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v_json_1464_);
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1476_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1476_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1471_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8);
v___x_1472_ = lean_string_append(v___x_1471_, v_a_1467_);
lean_dec(v_a_1467_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1472_);
v___x_1474_ = v___x_1469_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_a_1477_ = lean_ctor_get(v___x_1466_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1466_, 1);
v___x_1478_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1));
lean_inc(v_json_1464_);
v___x_1479_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(v_json_1464_, v___x_1478_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v_a_1477_);
lean_dec(v_json_1464_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1489_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1484_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13);
v___x_1485_ = lean_string_append(v___x_1484_, v_a_1480_);
lean_dec(v_a_1480_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1485_);
v___x_1487_ = v___x_1482_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1485_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_a_1490_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1490_);
lean_dec_ref_known(v___x_1479_, 1);
v___x_1491_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2));
lean_inc(v_json_1464_);
v___x_1492_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(v_json_1464_, v___x_1491_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v_a_1490_);
lean_dec(v_a_1477_);
lean_dec(v_json_1464_);
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1495_ = v___x_1492_;
v_isShared_1496_ = v_isSharedCheck_1502_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1492_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1502_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1497_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18);
v___x_1498_ = lean_string_append(v___x_1497_, v_a_1493_);
lean_dec(v_a_1493_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1498_);
v___x_1500_ = v___x_1495_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_a_1503_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v___x_1492_, 1);
v___x_1504_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3));
v___x_1505_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(v_json_1464_, v___x_1504_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1515_; 
lean_dec(v_a_1503_);
lean_dec(v_a_1490_);
lean_dec(v_a_1477_);
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1515_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1510_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23);
v___x_1511_ = lean_string_append(v___x_1510_, v_a_1506_);
lean_dec(v_a_1506_);
if (v_isShared_1509_ == 0)
{
lean_ctor_set(v___x_1508_, 0, v___x_1511_);
v___x_1513_ = v___x_1508_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
else
{
lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1524_; 
v_a_1516_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1518_ = v___x_1505_;
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1505_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1524_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1520_, 0, v_a_1477_);
lean_ctor_set(v___x_1520_, 1, v_a_1490_);
lean_ctor_set(v___x_1520_, 2, v_a_1503_);
lean_ctor_set(v___x_1520_, 3, v_a_1516_);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1520_);
v___x_1522_ = v___x_1518_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport(lean_object* v_c_1527_){
_start:
{
lean_object* v_lean_x3f_1528_; 
v_lean_x3f_1528_ = lean_ctor_get(v_c_1527_, 3);
if (lean_obj_tag(v_lean_x3f_1528_) == 1)
{
lean_object* v_val_1529_; lean_object* v_incrementalDiagnosticSupport_x3f_1530_; 
v_val_1529_ = lean_ctor_get(v_lean_x3f_1528_, 0);
v_incrementalDiagnosticSupport_x3f_1530_ = lean_ctor_get(v_val_1529_, 0);
if (lean_obj_tag(v_incrementalDiagnosticSupport_x3f_1530_) == 1)
{
lean_object* v_val_1531_; uint8_t v___x_1532_; 
v_val_1531_ = lean_ctor_get(v_incrementalDiagnosticSupport_x3f_1530_, 0);
v___x_1532_ = lean_unbox(v_val_1531_);
return v___x_1532_;
}
else
{
uint8_t v___x_1533_; 
v___x_1533_ = 0;
return v___x_1533_;
}
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = 0;
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport___boxed(lean_object* v_c_1535_){
_start:
{
uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport(v_c_1535_);
lean_dec_ref(v_c_1535_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(lean_object* v_c_1538_){
_start:
{
lean_object* v_lean_x3f_1539_; 
v_lean_x3f_1539_ = lean_ctor_get(v_c_1538_, 3);
if (lean_obj_tag(v_lean_x3f_1539_) == 1)
{
lean_object* v_val_1540_; lean_object* v_silentDiagnosticSupport_x3f_1541_; 
v_val_1540_ = lean_ctor_get(v_lean_x3f_1539_, 0);
v_silentDiagnosticSupport_x3f_1541_ = lean_ctor_get(v_val_1540_, 1);
if (lean_obj_tag(v_silentDiagnosticSupport_x3f_1541_) == 1)
{
lean_object* v_val_1542_; uint8_t v___x_1543_; 
v_val_1542_ = lean_ctor_get(v_silentDiagnosticSupport_x3f_1541_, 0);
v___x_1543_ = lean_unbox(v_val_1542_);
return v___x_1543_;
}
else
{
uint8_t v___x_1544_; 
v___x_1544_ = 0;
return v___x_1544_;
}
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = 0;
return v___x_1545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport___boxed(lean_object* v_c_1546_){
_start:
{
uint8_t v_res_1547_; lean_object* v_r_1548_; 
v_res_1547_ = l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(v_c_1546_);
lean_dec_ref(v_c_1546_);
v_r_1548_ = lean_box(v_res_1547_);
return v_r_1548_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ClientCapabilities_rpcWireFormat(lean_object* v_c_1549_){
_start:
{
lean_object* v_lean_x3f_1550_; 
v_lean_x3f_1550_ = lean_ctor_get(v_c_1549_, 3);
if (lean_obj_tag(v_lean_x3f_1550_) == 1)
{
lean_object* v_val_1551_; lean_object* v_rpcWireFormat_x3f_1552_; 
v_val_1551_ = lean_ctor_get(v_lean_x3f_1550_, 0);
v_rpcWireFormat_x3f_1552_ = lean_ctor_get(v_val_1551_, 2);
if (lean_obj_tag(v_rpcWireFormat_x3f_1552_) == 1)
{
lean_object* v_val_1553_; uint8_t v___x_1554_; 
v_val_1553_ = lean_ctor_get(v_rpcWireFormat_x3f_1552_, 0);
v___x_1554_ = lean_unbox(v_val_1553_);
return v___x_1554_;
}
else
{
uint8_t v___x_1555_; 
v___x_1555_ = 0;
return v___x_1555_;
}
}
else
{
uint8_t v___x_1556_; 
v___x_1556_ = 0;
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_rpcWireFormat___boxed(lean_object* v_c_1557_){
_start:
{
uint8_t v_res_1558_; lean_object* v_r_1559_; 
v_res_1558_ = l_Lean_Lsp_ClientCapabilities_rpcWireFormat(v_c_1557_);
lean_dec_ref(v_c_1557_);
v_r_1559_ = lean_box(v_res_1558_);
return v_r_1559_;
}
}
static lean_object* _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1563_){
_start:
{
if (lean_obj_tag(v_x_1563_) == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_obj_once(&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1, &l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1_once, _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v_a_1566_);
return v___x_1567_;
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_a_1568_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1568_);
v___x_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1569_, 0, v_a_1568_);
v___x_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1569_);
return v___x_1570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___boxed(lean_object* v_x_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(v_x_1571_);
lean_dec(v_x_1571_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(lean_object* v_j_1573_, lean_object* v_k_1574_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = l_Lean_Json_getObjValD(v_j_1573_, v_k_1574_);
v___x_1576_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(v___x_1575_);
lean_dec(v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1577_, lean_object* v_k_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(v_j_1577_, v_k_1578_);
lean_dec_ref(v_k_1578_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_1582_){
_start:
{
if (lean_obj_tag(v_x_1582_) == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson(v_x_1582_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1601_; 
v_a_1593_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1595_ = v___x_1584_;
v_isShared_1596_ = v_isSharedCheck_1601_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1584_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1601_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_a_1593_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1597_);
v___x_1599_ = v___x_1595_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(lean_object* v_j_1602_, lean_object* v_k_1603_){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = l_Lean_Json_getObjValD(v_j_1602_, v_k_1603_);
v___x_1605_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2(v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1___boxed(lean_object* v_j_1606_, lean_object* v_k_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(v_j_1606_, v_k_1607_);
lean_dec_ref(v_k_1607_);
return v_res_1608_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = 1;
v___x_1616_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2));
v___x_1617_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1616_, v___x_1615_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1618_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1619_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3);
v___x_1620_ = lean_string_append(v___x_1619_, v___x_1618_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = 1;
v___x_1625_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__6));
v___x_1626_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1625_, v___x_1624_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1627_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7);
v___x_1628_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4);
v___x_1629_ = lean_string_append(v___x_1628_, v___x_1627_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1630_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1631_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8);
v___x_1632_ = lean_string_append(v___x_1631_, v___x_1630_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1637_ = 1;
v___x_1638_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__12));
v___x_1639_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1638_, v___x_1637_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13);
v___x_1641_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4);
v___x_1642_ = lean_string_append(v___x_1641_, v___x_1640_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1643_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1644_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14);
v___x_1645_ = lean_string_append(v___x_1644_, v___x_1643_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson(lean_object* v_json_1646_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0));
lean_inc(v_json_1646_);
v___x_1648_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(v_json_1646_, v___x_1647_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_json_1646_);
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1651_ = v___x_1648_;
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1658_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1653_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9);
v___x_1654_ = lean_string_append(v___x_1653_, v_a_1649_);
lean_dec(v_a_1649_);
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 0, v___x_1654_);
v___x_1656_ = v___x_1651_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
else
{
lean_object* v_a_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_a_1659_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1659_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1660_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10));
v___x_1661_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(v_json_1646_, v___x_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1671_; 
lean_dec(v_a_1659_);
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1664_ = v___x_1661_;
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1661_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1671_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
v___x_1666_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15);
v___x_1667_ = lean_string_append(v___x_1666_, v_a_1662_);
lean_dec(v_a_1662_);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1667_);
v___x_1669_ = v___x_1664_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1680_; 
v_a_1672_ = lean_ctor_get(v___x_1661_, 0);
v_isSharedCheck_1680_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1674_ = v___x_1661_;
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1661_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v_a_1659_);
lean_ctor_set(v___x_1676_, 1, v_a_1672_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1676_);
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(lean_object* v_k_1684_, lean_object* v_x_1685_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 0)
{
lean_object* v___x_1686_; 
lean_dec_ref(v_k_1684_);
v___x_1686_ = lean_box(0);
return v___x_1686_;
}
else
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1687_ = lean_obj_once(&l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0, &l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0_once, _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v_k_1684_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = lean_box(0);
v___x_1690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___boxed(lean_object* v_k_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(v_k_1691_, v_x_1692_);
lean_dec(v_x_1692_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__1(lean_object* v_k_1694_, lean_object* v_x_1695_){
_start:
{
if (lean_obj_tag(v_x_1695_) == 0)
{
lean_object* v___x_1696_; 
lean_dec_ref(v_k_1694_);
v___x_1696_ = lean_box(0);
return v___x_1696_;
}
else
{
lean_object* v_val_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v_val_1697_ = lean_ctor_get(v_x_1695_, 0);
lean_inc(v_val_1697_);
lean_dec_ref_known(v_x_1695_, 1);
v___x_1698_ = l_Lean_Lsp_instToJsonRpcOptions_toJson(v_val_1697_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_k_1694_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
v___x_1700_ = lean_box(0);
v___x_1701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson(lean_object* v_x_1702_){
_start:
{
lean_object* v_moduleHierarchyProvider_x3f_1703_; lean_object* v_rpcProvider_x3f_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1720_; 
v_moduleHierarchyProvider_x3f_1703_ = lean_ctor_get(v_x_1702_, 0);
v_rpcProvider_x3f_1704_ = lean_ctor_get(v_x_1702_, 1);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_x_1702_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1706_ = v_x_1702_;
v_isShared_1707_ = v_isSharedCheck_1720_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_rpcProvider_x3f_1704_);
lean_inc(v_moduleHierarchyProvider_x3f_1703_);
lean_dec(v_x_1702_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1720_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1708_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0));
v___x_1709_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(v___x_1708_, v_moduleHierarchyProvider_x3f_1703_);
lean_dec(v_moduleHierarchyProvider_x3f_1703_);
v___x_1710_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10));
v___x_1711_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__1(v___x_1710_, v_rpcProvider_x3f_1704_);
v___x_1712_ = lean_box(0);
if (v_isShared_1707_ == 0)
{
lean_ctor_set_tag(v___x_1706_, 1);
lean_ctor_set(v___x_1706_, 1, v___x_1712_);
lean_ctor_set(v___x_1706_, 0, v___x_1711_);
v___x_1714_ = v___x_1706_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1715_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1709_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1717_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1715_, v___x_1716_);
v___x_1718_ = l_Lean_Json_mkObj(v___x_1717_);
lean_dec(v___x_1717_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(lean_object* v_k_1723_, lean_object* v_x_1724_){
_start:
{
if (lean_obj_tag(v_x_1724_) == 0)
{
lean_object* v___x_1725_; 
lean_dec_ref(v_k_1723_);
v___x_1725_ = lean_box(0);
return v___x_1725_;
}
else
{
lean_object* v_val_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_val_1726_ = lean_ctor_get(v_x_1724_, 0);
v___x_1727_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(v_val_1726_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_k_1723_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1728_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0___boxed(lean_object* v_k_1731_, lean_object* v_x_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(v_k_1731_, v_x_1732_);
lean_dec(v_x_1732_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__1(lean_object* v_k_1734_, lean_object* v_x_1735_){
_start:
{
if (lean_obj_tag(v_x_1735_) == 0)
{
lean_object* v___x_1736_; 
lean_dec_ref(v_k_1734_);
v___x_1736_ = lean_box(0);
return v___x_1736_;
}
else
{
lean_object* v_val_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v_val_1737_ = lean_ctor_get(v_x_1735_, 0);
lean_inc(v_val_1737_);
lean_dec_ref_known(v_x_1735_, 1);
v___x_1738_ = l_Lean_Lsp_instToJsonCompletionOptions_toJson(v_val_1737_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v_k_1734_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
v___x_1740_ = lean_box(0);
v___x_1741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1739_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
return v___x_1741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(lean_object* v_k_1742_, lean_object* v_x_1743_){
_start:
{
if (lean_obj_tag(v_x_1743_) == 0)
{
lean_object* v___x_1744_; 
lean_dec_ref(v_k_1742_);
v___x_1744_ = lean_box(0);
return v___x_1744_;
}
else
{
lean_object* v_val_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_val_1745_ = lean_ctor_get(v_x_1743_, 0);
v___x_1746_ = lean_unbox(v_val_1745_);
v___x_1747_ = l_Lean_Lsp_instToJsonRenameOptions_toJson(v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v_k_1742_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = lean_box(0);
v___x_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1748_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2___boxed(lean_object* v_k_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(v_k_1751_, v_x_1752_);
lean_dec(v_x_1752_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__3(lean_object* v_k_1754_, lean_object* v_x_1755_){
_start:
{
if (lean_obj_tag(v_x_1755_) == 0)
{
lean_object* v___x_1756_; 
lean_dec_ref(v_k_1754_);
v___x_1756_ = lean_box(0);
return v___x_1756_;
}
else
{
lean_object* v_val_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_val_1757_ = lean_ctor_get(v_x_1755_, 0);
lean_inc(v_val_1757_);
lean_dec_ref_known(v_x_1755_, 1);
v___x_1758_ = l_Lean_Lsp_instToJsonSemanticTokensOptions_toJson(v_val_1757_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v_k_1754_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_box(0);
v___x_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1759_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
return v___x_1761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__4(lean_object* v_k_1762_, lean_object* v_x_1763_){
_start:
{
if (lean_obj_tag(v_x_1763_) == 0)
{
lean_object* v___x_1764_; 
lean_dec_ref(v_k_1762_);
v___x_1764_ = lean_box(0);
return v___x_1764_;
}
else
{
lean_object* v_val_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_val_1765_ = lean_ctor_get(v_x_1763_, 0);
lean_inc(v_val_1765_);
lean_dec_ref_known(v_x_1763_, 1);
v___x_1766_ = l_Lean_Lsp_instToJsonCodeActionOptions_toJson(v_val_1765_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v_k_1762_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = lean_box(0);
v___x_1769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1767_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
return v___x_1769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(lean_object* v_k_1770_, lean_object* v_x_1771_){
_start:
{
if (lean_obj_tag(v_x_1771_) == 0)
{
lean_object* v___x_1772_; 
lean_dec_ref(v_k_1770_);
v___x_1772_ = lean_box(0);
return v___x_1772_;
}
else
{
lean_object* v_val_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v_val_1773_ = lean_ctor_get(v_x_1771_, 0);
v___x_1774_ = l_Lean_Lsp_instToJsonInlayHintOptions_toJson(v_val_1773_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_k_1770_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
v___x_1776_ = lean_box(0);
v___x_1777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5___boxed(lean_object* v_k_1778_, lean_object* v_x_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(v_k_1778_, v_x_1779_);
lean_dec(v_x_1779_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__6(lean_object* v_k_1781_, lean_object* v_x_1782_){
_start:
{
if (lean_obj_tag(v_x_1782_) == 0)
{
lean_object* v___x_1783_; 
lean_dec_ref(v_k_1781_);
v___x_1783_ = lean_box(0);
return v___x_1783_;
}
else
{
lean_object* v_val_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_val_1784_ = lean_ctor_get(v_x_1782_, 0);
lean_inc(v_val_1784_);
lean_dec_ref_known(v_x_1782_, 1);
v___x_1785_ = l_Lean_Lsp_instToJsonSignatureHelpOptions_toJson(v_val_1784_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v_k_1781_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = lean_box(0);
v___x_1788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1786_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
return v___x_1788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(lean_object* v_k_1789_, lean_object* v_x_1790_){
_start:
{
if (lean_obj_tag(v_x_1790_) == 0)
{
lean_object* v___x_1791_; 
lean_dec_ref(v_k_1789_);
v___x_1791_ = lean_box(0);
return v___x_1791_;
}
else
{
lean_object* v_val_1792_; uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v_val_1792_ = lean_ctor_get(v_x_1790_, 0);
v___x_1793_ = lean_unbox(v_val_1792_);
v___x_1794_ = l_Lean_Lsp_instToJsonDocumentColorOptions_toJson(v___x_1793_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v_k_1789_);
lean_ctor_set(v___x_1795_, 1, v___x_1794_);
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7___boxed(lean_object* v_k_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(v_k_1798_, v_x_1799_);
lean_dec(v_x_1799_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__8(lean_object* v_k_1801_, lean_object* v_x_1802_){
_start:
{
if (lean_obj_tag(v_x_1802_) == 0)
{
lean_object* v___x_1803_; 
lean_dec_ref(v_k_1801_);
v___x_1803_ = lean_box(0);
return v___x_1803_;
}
else
{
lean_object* v_val_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v_val_1804_ = lean_ctor_get(v_x_1802_, 0);
lean_inc(v_val_1804_);
lean_dec_ref_known(v_x_1802_, 1);
v___x_1805_ = l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson(v_val_1804_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v_k_1801_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_box(0);
v___x_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1806_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson(lean_object* v_x_1828_){
_start:
{
lean_object* v_textDocumentSync_x3f_1829_; lean_object* v_completionProvider_x3f_1830_; uint8_t v_hoverProvider_1831_; uint8_t v_documentHighlightProvider_1832_; uint8_t v_documentSymbolProvider_1833_; uint8_t v_definitionProvider_1834_; uint8_t v_declarationProvider_1835_; uint8_t v_typeDefinitionProvider_1836_; uint8_t v_referencesProvider_1837_; uint8_t v_callHierarchyProvider_1838_; lean_object* v_renameProvider_x3f_1839_; uint8_t v_workspaceSymbolProvider_1840_; uint8_t v_foldingRangeProvider_1841_; lean_object* v_semanticTokensProvider_x3f_1842_; lean_object* v_codeActionProvider_x3f_1843_; lean_object* v_inlayHintProvider_x3f_1844_; lean_object* v_signatureHelpProvider_x3f_1845_; lean_object* v_colorProvider_x3f_1846_; lean_object* v_experimental_x3f_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_textDocumentSync_x3f_1829_ = lean_ctor_get(v_x_1828_, 0);
lean_inc(v_textDocumentSync_x3f_1829_);
v_completionProvider_x3f_1830_ = lean_ctor_get(v_x_1828_, 1);
lean_inc(v_completionProvider_x3f_1830_);
v_hoverProvider_1831_ = lean_ctor_get_uint8(v_x_1828_, sizeof(void*)*9);
v_documentHighlightProvider_1832_ = lean_ctor_get_uint8(v_x_1828_, sizeof(void*)*9 + 1);
v_documentSymbolProvider_1833_ = lean_ctor_get_uint8(v_x_1828_, sizeof(void*)*9 + 2);
v_definitionProvider_1834_ = lean_ctor_get_uint8(v_x_1828_, sizeof(void*)*9 + 3);
v_declarationProvider_1835_ = lean_ctor_get_uint8(v_x_1828_, sizeof(void*)*9 + 4);
v_typeDefinitionProvider_1836_ = lean_ctor_get_uint8(v_x_1828_, sizeof(void*)*9 + 5);
v_referencesProvider_1837_ = lean_ctor_get_uint8(v_x_1828_, sizeof(void*)*9 + 6);
v_callHierarchyProvider_1838_ = lean_ctor_get_uint8(v_x_1828_, sizeof(void*)*9 + 7);
v_renameProvider_x3f_1839_ = lean_ctor_get(v_x_1828_, 2);
lean_inc(v_renameProvider_x3f_1839_);
v_workspaceSymbolProvider_1840_ = lean_ctor_get_uint8(v_x_1828_, sizeof(void*)*9 + 8);
v_foldingRangeProvider_1841_ = lean_ctor_get_uint8(v_x_1828_, sizeof(void*)*9 + 9);
v_semanticTokensProvider_x3f_1842_ = lean_ctor_get(v_x_1828_, 3);
lean_inc(v_semanticTokensProvider_x3f_1842_);
v_codeActionProvider_x3f_1843_ = lean_ctor_get(v_x_1828_, 4);
lean_inc(v_codeActionProvider_x3f_1843_);
v_inlayHintProvider_x3f_1844_ = lean_ctor_get(v_x_1828_, 5);
lean_inc(v_inlayHintProvider_x3f_1844_);
v_signatureHelpProvider_x3f_1845_ = lean_ctor_get(v_x_1828_, 6);
lean_inc(v_signatureHelpProvider_x3f_1845_);
v_colorProvider_x3f_1846_ = lean_ctor_get(v_x_1828_, 7);
lean_inc(v_colorProvider_x3f_1846_);
v_experimental_x3f_1847_ = lean_ctor_get(v_x_1828_, 8);
lean_inc(v_experimental_x3f_1847_);
lean_dec_ref(v_x_1828_);
v___x_1848_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0));
v___x_1849_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(v___x_1848_, v_textDocumentSync_x3f_1829_);
lean_dec(v_textDocumentSync_x3f_1829_);
v___x_1850_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1));
v___x_1851_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__1(v___x_1850_, v_completionProvider_x3f_1830_);
v___x_1852_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2));
v___x_1853_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1853_, 0, v_hoverProvider_1831_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3));
v___x_1858_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1858_, 0, v_documentHighlightProvider_1832_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v___x_1855_);
v___x_1861_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4));
v___x_1862_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1862_, 0, v_documentSymbolProvider_1833_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v___x_1855_);
v___x_1865_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5));
v___x_1866_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1866_, 0, v_definitionProvider_1834_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v___x_1855_);
v___x_1869_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6));
v___x_1870_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1870_, 0, v_declarationProvider_1835_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1855_);
v___x_1873_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7));
v___x_1874_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1874_, 0, v_typeDefinitionProvider_1836_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1855_);
v___x_1877_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8));
v___x_1878_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1878_, 0, v_referencesProvider_1837_);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v___x_1855_);
v___x_1881_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9));
v___x_1882_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1882_, 0, v_callHierarchyProvider_1838_);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v___x_1855_);
v___x_1885_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10));
v___x_1886_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(v___x_1885_, v_renameProvider_x3f_1839_);
lean_dec(v_renameProvider_x3f_1839_);
v___x_1887_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11));
v___x_1888_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1888_, 0, v_workspaceSymbolProvider_1840_);
v___x_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1887_);
lean_ctor_set(v___x_1889_, 1, v___x_1888_);
v___x_1890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v___x_1855_);
v___x_1891_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12));
v___x_1892_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1892_, 0, v_foldingRangeProvider_1841_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
lean_ctor_set(v___x_1894_, 1, v___x_1855_);
v___x_1895_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13));
v___x_1896_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__3(v___x_1895_, v_semanticTokensProvider_x3f_1842_);
v___x_1897_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14));
v___x_1898_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__4(v___x_1897_, v_codeActionProvider_x3f_1843_);
v___x_1899_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15));
v___x_1900_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(v___x_1899_, v_inlayHintProvider_x3f_1844_);
lean_dec(v_inlayHintProvider_x3f_1844_);
v___x_1901_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16));
v___x_1902_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__6(v___x_1901_, v_signatureHelpProvider_x3f_1845_);
v___x_1903_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17));
v___x_1904_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(v___x_1903_, v_colorProvider_x3f_1846_);
lean_dec(v_colorProvider_x3f_1846_);
v___x_1905_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18));
v___x_1906_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__8(v___x_1905_, v_experimental_x3f_1847_);
v___x_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v___x_1855_);
v___x_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1904_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1902_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1900_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1898_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1896_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1894_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1890_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1886_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1884_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1880_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1876_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1872_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1868_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1864_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1860_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1856_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1851_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1849_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1927_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1925_, v___x_1926_);
v___x_1928_ = l_Lean_Json_mkObj(v___x_1927_);
lean_dec(v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10(lean_object* v_x_1933_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10___closed__0));
return v___x_1934_;
}
else
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_Lsp_instFromJsonInlayHintOptions_fromJson(v_x_1933_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1952_; 
v_a_1944_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1946_ = v___x_1935_;
v_isShared_1947_ = v_isSharedCheck_1952_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1935_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1952_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1948_, 0, v_a_1944_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1948_);
v___x_1950_ = v___x_1946_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v___x_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(lean_object* v_j_1953_, lean_object* v_k_1954_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1955_ = l_Lean_Json_getObjValD(v_j_1953_, v_k_1954_);
v___x_1956_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10(v___x_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5___boxed(lean_object* v_j_1957_, lean_object* v_k_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(v_j_1957_, v_k_1958_);
lean_dec_ref(v_k_1958_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8(lean_object* v_x_1962_){
_start:
{
if (lean_obj_tag(v_x_1962_) == 0)
{
lean_object* v___x_1963_; 
v___x_1963_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8___closed__0));
return v___x_1963_;
}
else
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson(v_x_1962_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1981_; 
v_a_1973_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1975_ = v___x_1964_;
v_isShared_1976_ = v_isSharedCheck_1981_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1964_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1981_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_a_1973_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1977_);
v___x_1979_ = v___x_1975_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(lean_object* v_j_1982_, lean_object* v_k_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1984_ = l_Lean_Json_getObjValD(v_j_1982_, v_k_1983_);
v___x_1985_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8(v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4___boxed(lean_object* v_j_1986_, lean_object* v_k_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(v_j_1986_, v_k_1987_);
lean_dec_ref(v_k_1987_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16(lean_object* v_x_1991_){
_start:
{
if (lean_obj_tag(v_x_1991_) == 0)
{
lean_object* v___x_1992_; 
v___x_1992_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16___closed__0));
return v___x_1992_;
}
else
{
lean_object* v___x_1993_; 
v___x_1993_ = l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson(v_x_1991_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2010_; 
v_a_2002_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2004_ = v___x_1993_;
v_isShared_2005_ = v_isSharedCheck_2010_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_1993_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2010_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2008_; 
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_a_2002_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2006_);
v___x_2008_ = v___x_2004_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(lean_object* v_j_2011_, lean_object* v_k_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = l_Lean_Json_getObjValD(v_j_2011_, v_k_2012_);
v___x_2014_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16(v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8___boxed(lean_object* v_j_2015_, lean_object* v_k_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(v_j_2015_, v_k_2016_);
lean_dec_ref(v_k_2016_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12(lean_object* v_x_2020_){
_start:
{
if (lean_obj_tag(v_x_2020_) == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12___closed__0));
return v___x_2021_;
}
else
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Lsp_instFromJsonSignatureHelpOptions_fromJson(v_x_2020_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2039_; 
v_a_2031_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2033_ = v___x_2022_;
v_isShared_2034_ = v_isSharedCheck_2039_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2022_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2039_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v_a_2031_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2035_);
v___x_2037_ = v___x_2033_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(lean_object* v_j_2040_, lean_object* v_k_2041_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = l_Lean_Json_getObjValD(v_j_2040_, v_k_2041_);
v___x_2043_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12(v___x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6___boxed(lean_object* v_j_2044_, lean_object* v_k_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(v_j_2044_, v_k_2045_);
lean_dec_ref(v_k_2045_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_2049_){
_start:
{
if (lean_obj_tag(v_x_2049_) == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_2050_;
}
else
{
lean_object* v___x_2051_; 
v___x_2051_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(v_x_2049_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2059_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2054_ = v___x_2051_;
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_a_2052_);
lean_dec(v___x_2051_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2059_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v___x_2057_; 
if (v_isShared_2055_ == 0)
{
v___x_2057_ = v___x_2054_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_a_2052_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2068_; 
v_a_2060_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2062_ = v___x_2051_;
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2051_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2068_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_a_2060_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 0, v___x_2064_);
v___x_2066_ = v___x_2062_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(lean_object* v_j_2069_, lean_object* v_k_2070_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2071_ = l_Lean_Json_getObjValD(v_j_2069_, v_k_2070_);
v___x_2072_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0(v___x_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0___boxed(lean_object* v_j_2073_, lean_object* v_k_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(v_j_2073_, v_k_2074_);
lean_dec_ref(v_k_2074_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_2078_){
_start:
{
if (lean_obj_tag(v_x_2078_) == 0)
{
lean_object* v___x_2079_; 
v___x_2079_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_2079_;
}
else
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_Lsp_instFromJsonCompletionOptions_fromJson(v_x_2078_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2097_; 
v_a_2089_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2091_ = v___x_2080_;
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2080_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2097_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_a_2089_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 0, v___x_2093_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(lean_object* v_j_2098_, lean_object* v_k_2099_){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = l_Lean_Json_getObjValD(v_j_2098_, v_k_2099_);
v___x_2101_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2(v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1___boxed(lean_object* v_j_2102_, lean_object* v_k_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(v_j_2102_, v_k_2103_);
lean_dec_ref(v_k_2103_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7_spec__14(lean_object* v_x_2105_){
_start:
{
if (lean_obj_tag(v_x_2105_) == 0)
{
lean_object* v___x_2106_; 
v___x_2106_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_2106_;
}
else
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Lsp_instFromJsonDocumentColorOptions_fromJson(v_x_2105_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2107_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2107_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2124_; 
v_a_2116_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2118_ = v___x_2107_;
v_isShared_2119_ = v_isSharedCheck_2124_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2107_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2124_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v_a_2116_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2120_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(lean_object* v_j_2125_, lean_object* v_k_2126_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = l_Lean_Json_getObjValD(v_j_2125_, v_k_2126_);
v___x_2128_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7_spec__14(v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7___boxed(lean_object* v_j_2129_, lean_object* v_k_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(v_j_2129_, v_k_2130_);
lean_dec_ref(v_k_2130_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6(lean_object* v_x_2134_){
_start:
{
if (lean_obj_tag(v_x_2134_) == 0)
{
lean_object* v___x_2135_; 
v___x_2135_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6___closed__0));
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_Lsp_instFromJsonSemanticTokensOptions_fromJson(v_x_2134_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2153_; 
v_a_2145_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2147_ = v___x_2136_;
v_isShared_2148_ = v_isSharedCheck_2153_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2136_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2153_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v_a_2145_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 0, v___x_2149_);
v___x_2151_ = v___x_2147_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(lean_object* v_j_2154_, lean_object* v_k_2155_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = l_Lean_Json_getObjValD(v_j_2154_, v_k_2155_);
v___x_2157_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6(v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3___boxed(lean_object* v_j_2158_, lean_object* v_k_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(v_j_2158_, v_k_2159_);
lean_dec_ref(v_k_2159_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2_spec__4(lean_object* v_x_2161_){
_start:
{
if (lean_obj_tag(v_x_2161_) == 0)
{
lean_object* v___x_2162_; 
v___x_2162_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_2162_;
}
else
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_Lsp_instFromJsonRenameOptions_fromJson(v_x_2161_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2180_; 
v_a_2172_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2174_ = v___x_2163_;
v_isShared_2175_ = v_isSharedCheck_2180_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2163_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2180_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_a_2172_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2176_);
v___x_2178_ = v___x_2174_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2176_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(lean_object* v_j_2181_, lean_object* v_k_2182_){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = l_Lean_Json_getObjValD(v_j_2181_, v_k_2182_);
v___x_2184_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2_spec__4(v___x_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2___boxed(lean_object* v_j_2185_, lean_object* v_k_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(v_j_2185_, v_k_2186_);
lean_dec_ref(v_k_2186_);
return v_res_2187_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = 1;
v___x_2194_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1));
v___x_2195_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2194_, v___x_2193_);
return v___x_2195_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2196_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_2197_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2);
v___x_2198_ = lean_string_append(v___x_2197_, v___x_2196_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = 1;
v___x_2203_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__5));
v___x_2204_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2203_, v___x_2202_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6);
v___x_2206_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2207_ = lean_string_append(v___x_2206_, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2209_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7);
v___x_2210_ = lean_string_append(v___x_2209_, v___x_2208_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = 1;
v___x_2215_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__10));
v___x_2216_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2215_, v___x_2214_);
return v___x_2216_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11);
v___x_2218_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2219_ = lean_string_append(v___x_2218_, v___x_2217_);
return v___x_2219_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2220_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2221_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12);
v___x_2222_ = lean_string_append(v___x_2221_, v___x_2220_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15(void){
_start:
{
uint8_t v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = 1;
v___x_2226_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__14));
v___x_2227_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2226_, v___x_2225_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2228_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15);
v___x_2229_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2230_ = lean_string_append(v___x_2229_, v___x_2228_);
return v___x_2230_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2232_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16);
v___x_2233_ = lean_string_append(v___x_2232_, v___x_2231_);
return v___x_2233_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19(void){
_start:
{
uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = 1;
v___x_2237_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__18));
v___x_2238_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2237_, v___x_2236_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19);
v___x_2240_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2241_ = lean_string_append(v___x_2240_, v___x_2239_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2243_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20);
v___x_2244_ = lean_string_append(v___x_2243_, v___x_2242_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23(void){
_start:
{
uint8_t v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2247_ = 1;
v___x_2248_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__22));
v___x_2249_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2248_, v___x_2247_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23);
v___x_2251_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2252_ = lean_string_append(v___x_2251_, v___x_2250_);
return v___x_2252_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2253_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2254_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24);
v___x_2255_ = lean_string_append(v___x_2254_, v___x_2253_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27(void){
_start:
{
uint8_t v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = 1;
v___x_2259_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__26));
v___x_2260_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2259_, v___x_2258_);
return v___x_2260_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2261_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27);
v___x_2262_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2263_ = lean_string_append(v___x_2262_, v___x_2261_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2265_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28);
v___x_2266_ = lean_string_append(v___x_2265_, v___x_2264_);
return v___x_2266_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31(void){
_start:
{
uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = 1;
v___x_2270_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__30));
v___x_2271_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2270_, v___x_2269_);
return v___x_2271_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2272_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31);
v___x_2273_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2274_ = lean_string_append(v___x_2273_, v___x_2272_);
return v___x_2274_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2276_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32);
v___x_2277_ = lean_string_append(v___x_2276_, v___x_2275_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35(void){
_start:
{
uint8_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = 1;
v___x_2281_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__34));
v___x_2282_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2281_, v___x_2280_);
return v___x_2282_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35);
v___x_2284_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2285_ = lean_string_append(v___x_2284_, v___x_2283_);
return v___x_2285_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2287_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36);
v___x_2288_ = lean_string_append(v___x_2287_, v___x_2286_);
return v___x_2288_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39(void){
_start:
{
uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = 1;
v___x_2292_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__38));
v___x_2293_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2292_, v___x_2291_);
return v___x_2293_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39);
v___x_2295_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2296_ = lean_string_append(v___x_2295_, v___x_2294_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2298_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40);
v___x_2299_ = lean_string_append(v___x_2298_, v___x_2297_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43(void){
_start:
{
uint8_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = 1;
v___x_2303_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__42));
v___x_2304_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2303_, v___x_2302_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43);
v___x_2306_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2307_ = lean_string_append(v___x_2306_, v___x_2305_);
return v___x_2307_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2309_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44);
v___x_2310_ = lean_string_append(v___x_2309_, v___x_2308_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48(void){
_start:
{
uint8_t v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = 1;
v___x_2315_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__47));
v___x_2316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2315_, v___x_2314_);
return v___x_2316_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2317_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48);
v___x_2318_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2319_ = lean_string_append(v___x_2318_, v___x_2317_);
return v___x_2319_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2321_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49);
v___x_2322_ = lean_string_append(v___x_2321_, v___x_2320_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52(void){
_start:
{
uint8_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = 1;
v___x_2326_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__51));
v___x_2327_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2326_, v___x_2325_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52);
v___x_2329_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2330_ = lean_string_append(v___x_2329_, v___x_2328_);
return v___x_2330_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2332_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53);
v___x_2333_ = lean_string_append(v___x_2332_, v___x_2331_);
return v___x_2333_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56(void){
_start:
{
uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = 1;
v___x_2337_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__55));
v___x_2338_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2337_, v___x_2336_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57(void){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2339_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56);
v___x_2340_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2341_ = lean_string_append(v___x_2340_, v___x_2339_);
return v___x_2341_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58(void){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2342_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2343_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57);
v___x_2344_ = lean_string_append(v___x_2343_, v___x_2342_);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61(void){
_start:
{
uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2348_ = 1;
v___x_2349_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__60));
v___x_2350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2349_, v___x_2348_);
return v___x_2350_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2351_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61);
v___x_2352_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2353_ = lean_string_append(v___x_2352_, v___x_2351_);
return v___x_2353_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2354_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2355_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62);
v___x_2356_ = lean_string_append(v___x_2355_, v___x_2354_);
return v___x_2356_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66(void){
_start:
{
uint8_t v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = 1;
v___x_2361_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__65));
v___x_2362_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2361_, v___x_2360_);
return v___x_2362_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66);
v___x_2364_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2365_ = lean_string_append(v___x_2364_, v___x_2363_);
return v___x_2365_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2367_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67);
v___x_2368_ = lean_string_append(v___x_2367_, v___x_2366_);
return v___x_2368_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71(void){
_start:
{
uint8_t v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = 1;
v___x_2373_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__70));
v___x_2374_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2373_, v___x_2372_);
return v___x_2374_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71);
v___x_2376_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2377_ = lean_string_append(v___x_2376_, v___x_2375_);
return v___x_2377_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2379_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72);
v___x_2380_ = lean_string_append(v___x_2379_, v___x_2378_);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76(void){
_start:
{
uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = 1;
v___x_2385_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__75));
v___x_2386_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2385_, v___x_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76);
v___x_2388_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2389_ = lean_string_append(v___x_2388_, v___x_2387_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2390_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2391_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77);
v___x_2392_ = lean_string_append(v___x_2391_, v___x_2390_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81(void){
_start:
{
uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = 1;
v___x_2397_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__80));
v___x_2398_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2397_, v___x_2396_);
return v___x_2398_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81);
v___x_2400_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2401_ = lean_string_append(v___x_2400_, v___x_2399_);
return v___x_2401_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2403_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82);
v___x_2404_ = lean_string_append(v___x_2403_, v___x_2402_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86(void){
_start:
{
uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = 1;
v___x_2409_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__85));
v___x_2410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2409_, v___x_2408_);
return v___x_2410_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86);
v___x_2412_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2413_ = lean_string_append(v___x_2412_, v___x_2411_);
return v___x_2413_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2415_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87);
v___x_2416_ = lean_string_append(v___x_2415_, v___x_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(lean_object* v_json_2417_){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0));
lean_inc(v_json_2417_);
v___x_2419_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(v_json_2417_, v___x_2418_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v_json_2417_);
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2422_ = v___x_2419_;
v_isShared_2423_ = v_isSharedCheck_2429_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2419_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2429_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2424_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8);
v___x_2425_ = lean_string_append(v___x_2424_, v_a_2420_);
lean_dec(v_a_2420_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2425_);
v___x_2427_ = v___x_2422_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v___x_2425_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_a_2430_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2419_, 1);
v___x_2431_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1));
lean_inc(v_json_2417_);
v___x_2432_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(v_json_2417_, v___x_2431_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2442_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2442_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2437_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13);
v___x_2438_ = lean_string_append(v___x_2437_, v_a_2433_);
lean_dec(v_a_2433_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v___x_2438_);
v___x_2440_ = v___x_2435_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_a_2443_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2432_, 1);
v___x_2444_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2));
lean_inc(v_json_2417_);
v___x_2445_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2417_, v___x_2444_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2455_; 
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2455_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2450_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17);
v___x_2451_ = lean_string_append(v___x_2450_, v_a_2446_);
lean_dec(v_a_2446_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2451_);
v___x_2453_ = v___x_2448_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_a_2456_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2445_, 1);
v___x_2457_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3));
lean_inc(v_json_2417_);
v___x_2458_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2417_, v___x_2457_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2468_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2468_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2463_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21);
v___x_2464_ = lean_string_append(v___x_2463_, v_a_2459_);
lean_dec(v_a_2459_);
if (v_isShared_2462_ == 0)
{
lean_ctor_set(v___x_2461_, 0, v___x_2464_);
v___x_2466_ = v___x_2461_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_a_2469_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2470_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4));
lean_inc(v_json_2417_);
v___x_2471_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2417_, v___x_2470_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2481_; 
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2481_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2481_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2476_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25);
v___x_2477_ = lean_string_append(v___x_2476_, v_a_2472_);
lean_dec(v_a_2472_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2477_);
v___x_2479_ = v___x_2474_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
else
{
lean_object* v_a_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_a_2482_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2471_, 1);
v___x_2483_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5));
lean_inc(v_json_2417_);
v___x_2484_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2417_, v___x_2483_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2494_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2494_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2489_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29);
v___x_2490_ = lean_string_append(v___x_2489_, v_a_2485_);
lean_dec(v_a_2485_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2490_);
v___x_2492_ = v___x_2487_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2490_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v_a_2495_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2484_, 1);
v___x_2496_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6));
lean_inc(v_json_2417_);
v___x_2497_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2417_, v___x_2496_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2500_ = v___x_2497_;
v_isShared_2501_ = v_isSharedCheck_2507_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2497_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2507_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2505_; 
v___x_2502_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33);
v___x_2503_ = lean_string_append(v___x_2502_, v_a_2498_);
lean_dec(v_a_2498_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 0, v___x_2503_);
v___x_2505_ = v___x_2500_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2503_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v_a_2508_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2497_, 1);
v___x_2509_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7));
lean_inc(v_json_2417_);
v___x_2510_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2417_, v___x_2509_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2520_; 
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2520_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2520_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2515_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37);
v___x_2516_ = lean_string_append(v___x_2515_, v_a_2511_);
lean_dec(v_a_2511_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v___x_2516_);
v___x_2518_ = v___x_2513_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v_a_2521_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_a_2521_);
lean_dec_ref_known(v___x_2510_, 1);
v___x_2522_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8));
lean_inc(v_json_2417_);
v___x_2523_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2417_, v___x_2522_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2533_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2533_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
v___x_2528_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41);
v___x_2529_ = lean_string_append(v___x_2528_, v_a_2524_);
lean_dec(v_a_2524_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 0, v___x_2529_);
v___x_2531_ = v___x_2526_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
else
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_a_2534_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2523_, 1);
v___x_2535_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9));
lean_inc(v_json_2417_);
v___x_2536_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2417_, v___x_2535_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_a_2534_);
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2546_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2546_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2541_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45);
v___x_2542_ = lean_string_append(v___x_2541_, v_a_2537_);
lean_dec(v_a_2537_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2542_);
v___x_2544_ = v___x_2539_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v_a_2547_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2536_, 1);
v___x_2548_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10));
lean_inc(v_json_2417_);
v___x_2549_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(v_json_2417_, v___x_2548_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2559_; 
lean_dec(v_a_2547_);
lean_dec(v_a_2534_);
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2559_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_a_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2559_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2554_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50);
v___x_2555_ = lean_string_append(v___x_2554_, v_a_2550_);
lean_dec(v_a_2550_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 0, v___x_2555_);
v___x_2557_ = v___x_2552_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_a_2560_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2549_, 1);
v___x_2561_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11));
lean_inc(v_json_2417_);
v___x_2562_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2417_, v___x_2561_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2572_; 
lean_dec(v_a_2560_);
lean_dec(v_a_2547_);
lean_dec(v_a_2534_);
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2565_ = v___x_2562_;
v_isShared_2566_ = v_isSharedCheck_2572_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2562_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2572_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2567_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54);
v___x_2568_ = lean_string_append(v___x_2567_, v_a_2563_);
lean_dec(v_a_2563_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 0, v___x_2568_);
v___x_2570_ = v___x_2565_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
else
{
lean_object* v_a_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_a_2573_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2562_, 1);
v___x_2574_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12));
lean_inc(v_json_2417_);
v___x_2575_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2417_, v___x_2574_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v_a_2573_);
lean_dec(v_a_2560_);
lean_dec(v_a_2547_);
lean_dec(v_a_2534_);
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2585_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2585_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2580_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58);
v___x_2581_ = lean_string_append(v___x_2580_, v_a_2576_);
lean_dec(v_a_2576_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___x_2581_);
v___x_2583_ = v___x_2578_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_a_2586_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2587_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13));
lean_inc(v_json_2417_);
v___x_2588_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(v_json_2417_, v___x_2587_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2598_; 
lean_dec(v_a_2586_);
lean_dec(v_a_2573_);
lean_dec(v_a_2560_);
lean_dec(v_a_2547_);
lean_dec(v_a_2534_);
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2598_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2598_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2596_; 
v___x_2593_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63);
v___x_2594_ = lean_string_append(v___x_2593_, v_a_2589_);
lean_dec(v_a_2589_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2594_);
v___x_2596_ = v___x_2591_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2594_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_a_2599_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_a_2599_);
lean_dec_ref_known(v___x_2588_, 1);
v___x_2600_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14));
lean_inc(v_json_2417_);
v___x_2601_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(v_json_2417_, v___x_2600_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_a_2599_);
lean_dec(v_a_2586_);
lean_dec(v_a_2573_);
lean_dec(v_a_2560_);
lean_dec(v_a_2547_);
lean_dec(v_a_2534_);
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2611_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2611_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2606_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68);
v___x_2607_ = lean_string_append(v___x_2606_, v_a_2602_);
lean_dec(v_a_2602_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v___x_2607_);
v___x_2609_ = v___x_2604_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v_a_2612_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2613_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15));
lean_inc(v_json_2417_);
v___x_2614_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(v_json_2417_, v___x_2613_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v_a_2612_);
lean_dec(v_a_2599_);
lean_dec(v_a_2586_);
lean_dec(v_a_2573_);
lean_dec(v_a_2560_);
lean_dec(v_a_2547_);
lean_dec(v_a_2534_);
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2624_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2624_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; 
v___x_2619_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73);
v___x_2620_ = lean_string_append(v___x_2619_, v_a_2615_);
lean_dec(v_a_2615_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v___x_2620_);
v___x_2622_ = v___x_2617_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; 
v_a_2625_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2614_, 1);
v___x_2626_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16));
lean_inc(v_json_2417_);
v___x_2627_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(v_json_2417_, v___x_2626_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2637_; 
lean_dec(v_a_2625_);
lean_dec(v_a_2612_);
lean_dec(v_a_2599_);
lean_dec(v_a_2586_);
lean_dec(v_a_2573_);
lean_dec(v_a_2560_);
lean_dec(v_a_2547_);
lean_dec(v_a_2534_);
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2637_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2630_ = v___x_2627_;
v_isShared_2631_ = v_isSharedCheck_2637_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2627_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2637_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2632_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78);
v___x_2633_ = lean_string_append(v___x_2632_, v_a_2628_);
lean_dec(v_a_2628_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 0, v___x_2633_);
v___x_2635_ = v___x_2630_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_a_2638_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2639_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17));
lean_inc(v_json_2417_);
v___x_2640_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(v_json_2417_, v___x_2639_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2650_; 
lean_dec(v_a_2638_);
lean_dec(v_a_2625_);
lean_dec(v_a_2612_);
lean_dec(v_a_2599_);
lean_dec(v_a_2586_);
lean_dec(v_a_2573_);
lean_dec(v_a_2560_);
lean_dec(v_a_2547_);
lean_dec(v_a_2534_);
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
lean_dec(v_json_2417_);
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2643_ = v___x_2640_;
v_isShared_2644_ = v_isSharedCheck_2650_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2640_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2650_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2645_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83);
v___x_2646_ = lean_string_append(v___x_2645_, v_a_2641_);
lean_dec(v_a_2641_);
if (v_isShared_2644_ == 0)
{
lean_ctor_set(v___x_2643_, 0, v___x_2646_);
v___x_2648_ = v___x_2643_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_a_2651_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2640_, 1);
v___x_2652_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18));
v___x_2653_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(v_json_2417_, v___x_2652_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2663_; 
lean_dec(v_a_2651_);
lean_dec(v_a_2638_);
lean_dec(v_a_2625_);
lean_dec(v_a_2612_);
lean_dec(v_a_2599_);
lean_dec(v_a_2586_);
lean_dec(v_a_2573_);
lean_dec(v_a_2560_);
lean_dec(v_a_2547_);
lean_dec(v_a_2534_);
lean_dec(v_a_2521_);
lean_dec(v_a_2508_);
lean_dec(v_a_2495_);
lean_dec(v_a_2482_);
lean_dec(v_a_2469_);
lean_dec(v_a_2456_);
lean_dec(v_a_2443_);
lean_dec(v_a_2430_);
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2663_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2663_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2661_; 
v___x_2658_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88);
v___x_2659_ = lean_string_append(v___x_2658_, v_a_2654_);
lean_dec(v_a_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2659_);
v___x_2661_ = v___x_2656_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v___x_2659_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2682_; 
v_a_2664_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2666_ = v___x_2653_;
v_isShared_2667_ = v_isSharedCheck_2682_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2653_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2682_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; uint8_t v___x_2669_; uint8_t v___x_2670_; uint8_t v___x_2671_; uint8_t v___x_2672_; uint8_t v___x_2673_; uint8_t v___x_2674_; uint8_t v___x_2675_; uint8_t v___x_2676_; uint8_t v___x_2677_; uint8_t v___x_2678_; lean_object* v___x_2680_; 
v___x_2668_ = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(v___x_2668_, 0, v_a_2430_);
lean_ctor_set(v___x_2668_, 1, v_a_2443_);
lean_ctor_set(v___x_2668_, 2, v_a_2560_);
lean_ctor_set(v___x_2668_, 3, v_a_2599_);
lean_ctor_set(v___x_2668_, 4, v_a_2612_);
lean_ctor_set(v___x_2668_, 5, v_a_2625_);
lean_ctor_set(v___x_2668_, 6, v_a_2638_);
lean_ctor_set(v___x_2668_, 7, v_a_2651_);
lean_ctor_set(v___x_2668_, 8, v_a_2664_);
v___x_2669_ = lean_unbox(v_a_2456_);
lean_dec(v_a_2456_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*9, v___x_2669_);
v___x_2670_ = lean_unbox(v_a_2469_);
lean_dec(v_a_2469_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*9 + 1, v___x_2670_);
v___x_2671_ = lean_unbox(v_a_2482_);
lean_dec(v_a_2482_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*9 + 2, v___x_2671_);
v___x_2672_ = lean_unbox(v_a_2495_);
lean_dec(v_a_2495_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*9 + 3, v___x_2672_);
v___x_2673_ = lean_unbox(v_a_2508_);
lean_dec(v_a_2508_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*9 + 4, v___x_2673_);
v___x_2674_ = lean_unbox(v_a_2521_);
lean_dec(v_a_2521_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*9 + 5, v___x_2674_);
v___x_2675_ = lean_unbox(v_a_2534_);
lean_dec(v_a_2534_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*9 + 6, v___x_2675_);
v___x_2676_ = lean_unbox(v_a_2547_);
lean_dec(v_a_2547_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*9 + 7, v___x_2676_);
v___x_2677_ = lean_unbox(v_a_2573_);
lean_dec(v_a_2573_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*9 + 8, v___x_2677_);
v___x_2678_ = lean_unbox(v_a_2586_);
lean_dec(v_a_2586_);
lean_ctor_set_uint8(v___x_2668_, sizeof(void*)*9 + 9, v___x_2678_);
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 0, v___x_2668_);
v___x_2680_ = v___x_2666_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2668_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
lean_object* runtime_initialize_Lean_Data_JsonRpc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_CodeActions(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_Capabilities(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_CodeActions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_Capabilities(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_LanguageFeatures(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_CodeActions(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_Capabilities(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_JsonRpc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_LanguageFeatures(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_CodeActions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Capabilities(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_Capabilities(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_Capabilities(builtin);
}
#ifdef __cplusplus
}
#endif

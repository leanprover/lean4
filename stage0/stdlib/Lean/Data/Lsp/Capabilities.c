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
if (lean_obj_tag(v___x_95_) == 0)
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
lean_ctor_set_tag(v___x_108_, 0);
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_95_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_95_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0(lean_object* v_k_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v___x_126_; 
lean_dec_ref(v_k_124_);
v___x_126_ = lean_box(0);
return v___x_126_;
}
else
{
lean_object* v_val_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_val_127_ = lean_ctor_get(v_x_125_, 0);
v___x_128_ = l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson(v_val_127_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v_k_124_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_132_, lean_object* v_x_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0(v_k_132_, v_x_133_);
lean_dec(v_x_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson(lean_object* v_x_136_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_137_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0));
v___x_138_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionClientCapabilities_toJson_spec__0(v___x_137_, v_x_136_);
v___x_139_ = lean_box(0);
v___x_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_138_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_142_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_140_, v___x_141_);
v___x_143_ = l_Lean_Json_mkObj(v___x_142_);
lean_dec(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___boxed(lean_object* v_x_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson(v_x_144_);
lean_dec(v_x_144_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v___x_151_; 
v___x_151_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_151_;
}
else
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson(v_x_150_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_a_161_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___x_152_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_152_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0(lean_object* v_j_170_, lean_object* v_k_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = l_Lean_Json_getObjValD(v_j_170_, v_k_171_);
v___x_173_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_174_, lean_object* v_k_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0(v_j_174_, v_k_175_);
lean_dec_ref(v_k_175_);
return v_res_176_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_182_ = 1;
v___x_183_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__1));
v___x_184_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_183_, v___x_182_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_186_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__2);
v___x_187_ = lean_string_append(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = 1;
v___x_192_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__5));
v___x_193_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__6);
v___x_195_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__3);
v___x_196_ = lean_string_append(v___x_195_, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_198_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__7);
v___x_199_ = lean_string_append(v___x_198_, v___x_197_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson(lean_object* v_json_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson___closed__0));
v___x_202_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0(v_json_200_, v___x_201_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_212_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_212_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_207_ = lean_obj_once(&l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson___closed__8);
v___x_208_ = lean_string_append(v___x_207_, v_a_203_);
lean_dec(v_a_203_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v___x_208_);
v___x_210_ = v___x_205_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
v_a_213_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_202_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_202_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set_tag(v___x_215_, 0);
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
v_a_221_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_202_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_202_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0(lean_object* v_k_231_, lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
lean_object* v___x_233_; 
lean_dec_ref(v_k_231_);
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_val_234_ = lean_ctor_get(v_x_232_, 0);
v___x_235_ = l_Lean_Lsp_instToJsonCompletionClientCapabilities_toJson(v_val_234_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_k_231_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_239_, lean_object* v_x_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0(v_k_239_, v_x_240_);
lean_dec(v_x_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__1(lean_object* v_k_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v___x_244_; 
lean_dec_ref(v_k_242_);
v___x_244_ = lean_box(0);
return v___x_244_;
}
else
{
lean_object* v_val_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_val_245_ = lean_ctor_get(v_x_243_, 0);
lean_inc(v_val_245_);
lean_dec_ref_known(v_x_243_, 1);
v___x_246_ = l_Lean_Lsp_instToJsonCodeActionClientCapabilities_toJson(v_val_245_);
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_k_242_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__2(lean_object* v_k_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v_k_250_);
v___x_252_ = lean_box(0);
return v___x_252_;
}
else
{
lean_object* v_val_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_val_253_ = lean_ctor_get(v_x_251_, 0);
lean_inc(v_val_253_);
lean_dec_ref_known(v_x_251_, 1);
v___x_254_ = l_Lean_Lsp_instToJsonInlayHintClientCapabilities_toJson(v_val_253_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v_k_250_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson(lean_object* v_x_261_){
_start:
{
lean_object* v_completion_x3f_262_; lean_object* v_codeAction_x3f_263_; lean_object* v_inlayHint_x3f_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_completion_x3f_262_ = lean_ctor_get(v_x_261_, 0);
lean_inc(v_completion_x3f_262_);
v_codeAction_x3f_263_ = lean_ctor_get(v_x_261_, 1);
lean_inc(v_codeAction_x3f_263_);
v_inlayHint_x3f_264_ = lean_ctor_get(v_x_261_, 2);
lean_inc(v_inlayHint_x3f_264_);
lean_dec_ref(v_x_261_);
v___x_265_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0));
v___x_266_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__0(v___x_265_, v_completion_x3f_262_);
lean_dec(v_completion_x3f_262_);
v___x_267_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1));
v___x_268_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__1(v___x_267_, v_codeAction_x3f_263_);
v___x_269_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2));
v___x_270_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson_spec__2(v___x_269_, v_inlayHint_x3f_264_);
v___x_271_ = lean_box(0);
v___x_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_268_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_266_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_276_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_274_, v___x_275_);
v___x_277_ = l_Lean_Json_mkObj(v___x_276_);
lean_dec(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_282_){
_start:
{
if (lean_obj_tag(v_x_282_) == 0)
{
lean_object* v___x_283_; 
v___x_283_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_283_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Lsp_instFromJsonCodeActionClientCapabilities_fromJson(v_x_282_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
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
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
v_a_293_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_301_ == 0)
{
v___x_295_ = v___x_284_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_284_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v_a_293_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1(lean_object* v_j_302_, lean_object* v_k_303_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = l_Lean_Json_getObjValD(v_j_302_, v_k_303_);
v___x_305_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1_spec__2(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1___boxed(lean_object* v_j_306_, lean_object* v_k_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1(v_j_306_, v_k_307_);
lean_dec_ref(v_k_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
lean_object* v___x_312_; 
v___x_312_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_312_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson(v_x_311_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_330_; 
v_a_322_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_330_ == 0)
{
v___x_324_ = v___x_313_;
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_313_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_330_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_a_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_326_);
v___x_328_ = v___x_324_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0(lean_object* v_j_331_, lean_object* v_k_332_){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = l_Lean_Json_getObjValD(v_j_331_, v_k_332_);
v___x_334_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0_spec__0(v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_335_, lean_object* v_k_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0(v_j_335_, v_k_336_);
lean_dec_ref(v_k_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4(lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v___x_341_; 
v___x_341_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4___closed__0));
return v___x_341_;
}
else
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Lsp_instFromJsonInlayHintClientCapabilities_fromJson(v_x_340_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_359_; 
v_a_351_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_359_ == 0)
{
v___x_353_ = v___x_342_;
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_342_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_359_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_a_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2(lean_object* v_j_360_, lean_object* v_k_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = l_Lean_Json_getObjValD(v_j_360_, v_k_361_);
v___x_363_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2_spec__4(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2___boxed(lean_object* v_j_364_, lean_object* v_k_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2(v_j_364_, v_k_365_);
lean_dec_ref(v_k_365_);
return v_res_366_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = 1;
v___x_373_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__1));
v___x_374_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_373_, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_375_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_376_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__2);
v___x_377_ = lean_string_append(v___x_376_, v___x_375_);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = 1;
v___x_382_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__5));
v___x_383_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_382_, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__6);
v___x_385_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3);
v___x_386_ = lean_string_append(v___x_385_, v___x_384_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_388_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__7);
v___x_389_ = lean_string_append(v___x_388_, v___x_387_);
return v___x_389_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_393_ = 1;
v___x_394_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__10));
v___x_395_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_394_, v___x_393_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__11);
v___x_397_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3);
v___x_398_ = lean_string_append(v___x_397_, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_400_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__12);
v___x_401_ = lean_string_append(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = 1;
v___x_406_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__15));
v___x_407_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__16);
v___x_409_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__3);
v___x_410_ = lean_string_append(v___x_409_, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_412_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__17);
v___x_413_ = lean_string_append(v___x_412_, v___x_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson(lean_object* v_json_414_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__0));
lean_inc(v_json_414_);
v___x_416_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__0(v_json_414_, v___x_415_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_426_; 
lean_dec(v_json_414_);
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_426_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_426_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_426_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_421_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__8);
v___x_422_ = lean_string_append(v___x_421_, v_a_417_);
lean_dec(v_a_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_422_);
v___x_424_ = v___x_419_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
else
{
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v_json_414_);
v_a_427_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_416_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_416_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
lean_ctor_set_tag(v___x_429_, 0);
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
else
{
lean_object* v_a_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_a_435_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_416_, 1);
v___x_436_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__1));
lean_inc(v_json_414_);
v___x_437_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__1(v_json_414_, v___x_436_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_447_; 
lean_dec(v_a_435_);
lean_dec(v_json_414_);
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_447_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_442_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__13);
v___x_443_ = lean_string_append(v___x_442_, v_a_438_);
lean_dec(v_a_438_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_443_);
v___x_445_ = v___x_440_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec(v_a_435_);
lean_dec(v_json_414_);
v_a_448_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_437_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_437_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set_tag(v___x_450_, 0);
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v_a_456_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_456_);
lean_dec_ref_known(v___x_437_, 1);
v___x_457_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson___closed__2));
v___x_458_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson_spec__2(v_json_414_, v___x_457_);
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_468_; 
lean_dec(v_a_456_);
lean_dec(v_a_435_);
v_a_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_468_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_a_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_468_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_463_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson___closed__18);
v___x_464_ = lean_string_append(v___x_463_, v_a_459_);
lean_dec(v_a_459_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_464_);
v___x_466_ = v___x_461_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
else
{
if (lean_obj_tag(v___x_458_) == 0)
{
lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_476_; 
lean_dec(v_a_456_);
lean_dec(v_a_435_);
v_a_469_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_476_ == 0)
{
v___x_471_ = v___x_458_;
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_458_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_476_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_474_; 
if (v_isShared_472_ == 0)
{
lean_ctor_set_tag(v___x_471_, 0);
v___x_474_ = v___x_471_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_469_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
else
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_485_; 
v_a_477_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_485_ == 0)
{
v___x_479_ = v___x_458_;
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_458_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_485_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
v___x_481_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_481_, 0, v_a_435_);
lean_ctor_set(v___x_481_, 1, v_a_456_);
lean_ctor_set(v___x_481_, 2, v_a_477_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
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
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(uint8_t v_x_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_490_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0));
v___x_491_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_491_, 0, v_x_489_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = lean_box(0);
v___x_494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v___x_493_);
v___x_496_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_497_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_495_, v___x_496_);
v___x_498_ = l_Lean_Json_mkObj(v___x_497_);
lean_dec(v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___boxed(lean_object* v_x_499_){
_start:
{
uint8_t v_x_29__boxed_500_; lean_object* v_res_501_; 
v_x_29__boxed_500_ = lean_unbox(v_x_499_);
v_res_501_ = l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(v_x_29__boxed_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(lean_object* v_j_504_, lean_object* v_k_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = l_Lean_Json_getObjValD(v_j_504_, v_k_505_);
v___x_507_ = l_Lean_Json_getBool_x3f(v___x_506_);
lean_dec(v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_508_, lean_object* v_k_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_j_508_, v_k_509_);
lean_dec_ref(v_k_509_);
return v_res_510_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = 1;
v___x_517_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1));
v___x_518_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_517_, v___x_516_);
return v___x_518_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_520_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2);
v___x_521_ = lean_string_append(v___x_520_, v___x_519_);
return v___x_521_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5(void){
_start:
{
uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = 1;
v___x_525_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__4));
v___x_526_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_525_, v___x_524_);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5);
v___x_528_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3);
v___x_529_ = lean_string_append(v___x_528_, v___x_527_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_531_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6);
v___x_532_ = lean_string_append(v___x_531_, v___x_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson(lean_object* v_json_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0));
v___x_535_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_533_, v___x_534_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_545_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_545_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_545_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_540_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7);
v___x_541_ = lean_string_append(v___x_540_, v_a_536_);
lean_dec(v_a_536_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_541_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
else
{
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_a_546_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_535_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_535_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
lean_ctor_set_tag(v___x_548_, 0);
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
v_a_554_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_535_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_535_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(lean_object* v_k_564_, lean_object* v_x_565_){
_start:
{
if (lean_obj_tag(v_x_565_) == 0)
{
lean_object* v___x_566_; 
lean_dec_ref(v_k_564_);
v___x_566_ = lean_box(0);
return v___x_566_;
}
else
{
lean_object* v_val_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_val_567_ = lean_ctor_get(v_x_565_, 0);
v___x_568_ = lean_unbox(v_val_567_);
v___x_569_ = l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v_k_564_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_573_, lean_object* v_x_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(v_k_573_, v_x_574_);
lean_dec(v_x_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(lean_object* v_x_577_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_578_ = ((lean_object*)(l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0));
v___x_579_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(v___x_578_, v_x_577_);
v___x_580_ = lean_box(0);
v___x_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_583_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_581_, v___x_582_);
v___x_584_ = l_Lean_Json_mkObj(v___x_583_);
lean_dec(v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___boxed(lean_object* v_x_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(v_x_585_);
lean_dec(v_x_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_589_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
lean_object* v___x_590_; 
v___x_590_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_590_;
}
else
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson(v_x_589_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_608_; 
v_a_600_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_608_ == 0)
{
v___x_602_ = v___x_591_;
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_591_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_608_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v_a_600_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_604_);
v___x_606_ = v___x_602_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(lean_object* v_j_609_, lean_object* v_k_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = l_Lean_Json_getObjValD(v_j_609_, v_k_610_);
v___x_612_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0_spec__0(v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_613_, lean_object* v_k_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(v_j_613_, v_k_614_);
lean_dec_ref(v_k_614_);
return v_res_615_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = 1;
v___x_622_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1));
v___x_623_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_622_, v___x_621_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_625_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2);
v___x_626_ = lean_string_append(v___x_625_, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = 1;
v___x_631_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__5));
v___x_632_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_631_, v___x_630_);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6);
v___x_634_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3);
v___x_635_ = lean_string_append(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_637_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7);
v___x_638_ = lean_string_append(v___x_637_, v___x_636_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson(lean_object* v_json_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0));
v___x_641_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(v_json_639_, v___x_640_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_651_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_651_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_651_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_651_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_646_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8);
v___x_647_ = lean_string_append(v___x_646_, v_a_642_);
lean_dec(v_a_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_647_);
v___x_649_ = v___x_644_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_a_652_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_641_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_641_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 0);
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_a_660_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_641_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_641_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_672_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0));
v___x_673_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_672_, v_x_671_);
v___x_674_ = lean_box(0);
v___x_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_677_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_675_, v___x_676_);
v___x_678_ = l_Lean_Json_mkObj(v___x_677_);
lean_dec(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___boxed(lean_object* v_x_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(v_x_679_);
lean_dec(v_x_679_);
return v_res_680_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2(void){
_start:
{
uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_688_ = 1;
v___x_689_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1));
v___x_690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_689_, v___x_688_);
return v___x_690_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_692_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2);
v___x_693_ = lean_string_append(v___x_692_, v___x_691_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6(void){
_start:
{
uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = 1;
v___x_698_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__5));
v___x_699_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_698_, v___x_697_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6);
v___x_701_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3);
v___x_702_ = lean_string_append(v___x_701_, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_704_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7);
v___x_705_ = lean_string_append(v___x_704_, v___x_703_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson(lean_object* v_json_706_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0));
v___x_708_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_706_, v___x_707_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_718_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_718_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_718_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8);
v___x_714_ = lean_string_append(v___x_713_, v_a_709_);
lean_dec(v_a_709_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_a_719_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_708_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_708_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set_tag(v___x_721_, 0);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_708_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_708_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(lean_object* v_k_737_, lean_object* v_x_738_){
_start:
{
if (lean_obj_tag(v_x_738_) == 0)
{
lean_object* v___x_739_; 
lean_dec_ref(v_k_737_);
v___x_739_ = lean_box(0);
return v___x_739_;
}
else
{
lean_object* v_val_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v_val_740_ = lean_ctor_get(v_x_738_, 0);
v___x_741_ = l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(v_val_740_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v_k_737_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_box(0);
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_745_, lean_object* v_x_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(v_k_745_, v_x_746_);
lean_dec(v_x_746_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(size_t v_sz_748_, size_t v_i_749_, lean_object* v_bs_750_){
_start:
{
uint8_t v___x_751_; 
v___x_751_ = lean_usize_dec_lt(v_i_749_, v_sz_748_);
if (v___x_751_ == 0)
{
return v_bs_750_;
}
else
{
lean_object* v_v_752_; lean_object* v___x_753_; lean_object* v_bs_x27_754_; lean_object* v___x_755_; size_t v___x_756_; size_t v___x_757_; lean_object* v___x_758_; 
v_v_752_ = lean_array_uget(v_bs_750_, v_i_749_);
v___x_753_ = lean_unsigned_to_nat(0u);
v_bs_x27_754_ = lean_array_uset(v_bs_750_, v_i_749_, v___x_753_);
v___x_755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_755_, 0, v_v_752_);
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_749_, v___x_756_);
v___x_758_ = lean_array_uset(v_bs_x27_754_, v_i_749_, v___x_755_);
v_i_749_ = v___x_757_;
v_bs_750_ = v___x_758_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_bs_762_){
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_764_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(v_sz_boxed_763_, v_i_boxed_764_, v_bs_762_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1(lean_object* v_a_766_){
_start:
{
size_t v_sz_767_; size_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v_sz_767_ = lean_array_size(v_a_766_);
v___x_768_ = ((size_t)0ULL);
v___x_769_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(v_sz_767_, v___x_768_, v_a_766_);
v___x_770_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1(lean_object* v_k_771_, lean_object* v_x_772_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
lean_object* v___x_773_; 
lean_dec_ref(v_k_771_);
v___x_773_ = lean_box(0);
return v___x_773_;
}
else
{
lean_object* v_val_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_val_774_ = lean_ctor_get(v_x_772_, 0);
lean_inc(v_val_774_);
lean_dec_ref_known(v_x_772_, 1);
v___x_775_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1(v_val_774_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_k_771_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_776_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson(lean_object* v_x_782_){
_start:
{
lean_object* v_documentChanges_x3f_783_; lean_object* v_changeAnnotationSupport_x3f_784_; lean_object* v_resourceOperations_x3f_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_documentChanges_x3f_783_ = lean_ctor_get(v_x_782_, 0);
lean_inc(v_documentChanges_x3f_783_);
v_changeAnnotationSupport_x3f_784_ = lean_ctor_get(v_x_782_, 1);
lean_inc(v_changeAnnotationSupport_x3f_784_);
v_resourceOperations_x3f_785_ = lean_ctor_get(v_x_782_, 2);
lean_inc(v_resourceOperations_x3f_785_);
lean_dec_ref(v_x_782_);
v___x_786_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0));
v___x_787_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_786_, v_documentChanges_x3f_783_);
lean_dec(v_documentChanges_x3f_783_);
v___x_788_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1));
v___x_789_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(v___x_788_, v_changeAnnotationSupport_x3f_784_);
lean_dec(v_changeAnnotationSupport_x3f_784_);
v___x_790_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2));
v___x_791_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1(v___x_790_, v_resourceOperations_x3f_785_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_789_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_787_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_797_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_795_, v___x_796_);
v___x_798_ = l_Lean_Json_mkObj(v___x_797_);
lean_dec(v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(size_t v_sz_801_, size_t v_i_802_, lean_object* v_bs_803_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_lt(v_i_802_, v_sz_801_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v_bs_803_);
return v___x_805_;
}
else
{
lean_object* v_v_806_; lean_object* v___x_807_; 
v_v_806_ = lean_array_uget_borrowed(v_bs_803_, v_i_802_);
lean_inc(v_v_806_);
v___x_807_ = l_Lean_Json_getStr_x3f(v_v_806_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_bs_803_);
v_a_808_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_807_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_817_; lean_object* v_bs_x27_818_; size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
v_a_816_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_807_, 1);
v___x_817_ = lean_unsigned_to_nat(0u);
v_bs_x27_818_ = lean_array_uset(v_bs_803_, v_i_802_, v___x_817_);
v___x_819_ = ((size_t)1ULL);
v___x_820_ = lean_usize_add(v_i_802_, v___x_819_);
v___x_821_ = lean_array_uset(v_bs_x27_818_, v_i_802_, v_a_816_);
v_i_802_ = v___x_820_;
v_bs_803_ = v___x_821_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_823_, lean_object* v_i_824_, lean_object* v_bs_825_){
_start:
{
size_t v_sz_boxed_826_; size_t v_i_boxed_827_; lean_object* v_res_828_; 
v_sz_boxed_826_ = lean_unbox_usize(v_sz_823_);
lean_dec(v_sz_823_);
v_i_boxed_827_ = lean_unbox_usize(v_i_824_);
lean_dec(v_i_824_);
v_res_828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(v_sz_boxed_826_, v_i_boxed_827_, v_bs_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3(lean_object* v_x_831_){
_start:
{
if (lean_obj_tag(v_x_831_) == 4)
{
lean_object* v_elems_832_; size_t v_sz_833_; size_t v___x_834_; lean_object* v___x_835_; 
v_elems_832_ = lean_ctor_get(v_x_831_, 0);
lean_inc_ref(v_elems_832_);
lean_dec_ref_known(v_x_831_, 1);
v_sz_833_ = lean_array_size(v_elems_832_);
v___x_834_ = ((size_t)0ULL);
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(v_sz_833_, v___x_834_, v_elems_832_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_836_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__0));
v___x_837_ = lean_unsigned_to_nat(80u);
v___x_838_ = l_Lean_Json_pretty(v_x_831_, v___x_837_);
v___x_839_ = lean_string_append(v___x_836_, v___x_838_);
lean_dec_ref(v___x_838_);
v___x_840_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__1));
v___x_841_ = lean_string_append(v___x_839_, v___x_840_);
v___x_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
return v___x_842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_845_){
_start:
{
if (lean_obj_tag(v_x_845_) == 0)
{
lean_object* v___x_846_; 
v___x_846_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_846_;
}
else
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3(v_x_845_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_864_; 
v_a_856_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_864_ == 0)
{
v___x_858_ = v___x_847_;
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_847_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_862_; 
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v_a_856_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_860_);
v___x_862_ = v___x_858_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(lean_object* v_j_865_, lean_object* v_k_866_){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = l_Lean_Json_getObjValD(v_j_865_, v_k_866_);
v___x_868_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2(v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1___boxed(lean_object* v_j_869_, lean_object* v_k_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(v_j_869_, v_k_870_);
lean_dec_ref(v_k_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_872_){
_start:
{
if (lean_obj_tag(v_x_872_) == 0)
{
lean_object* v___x_873_; 
v___x_873_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_873_;
}
else
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson(v_x_872_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_891_; 
v_a_883_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_891_ == 0)
{
v___x_885_ = v___x_874_;
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_874_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v_a_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(lean_object* v_j_892_, lean_object* v_k_893_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = l_Lean_Json_getObjValD(v_j_892_, v_k_893_);
v___x_895_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0_spec__0(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_896_, lean_object* v_k_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(v_j_896_, v_k_897_);
lean_dec_ref(v_k_897_);
return v_res_898_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = 1;
v___x_905_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1));
v___x_906_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_905_, v___x_904_);
return v___x_906_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_908_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2);
v___x_909_ = lean_string_append(v___x_908_, v___x_907_);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = 1;
v___x_914_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__5));
v___x_915_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6);
v___x_917_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3);
v___x_918_ = lean_string_append(v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_920_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7);
v___x_921_ = lean_string_append(v___x_920_, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = 1;
v___x_926_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__10));
v___x_927_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11);
v___x_929_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3);
v___x_930_ = lean_string_append(v___x_929_, v___x_928_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_932_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12);
v___x_933_ = lean_string_append(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = 1;
v___x_938_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__15));
v___x_939_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_938_, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16);
v___x_941_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3);
v___x_942_ = lean_string_append(v___x_941_, v___x_940_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_944_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17);
v___x_945_ = lean_string_append(v___x_944_, v___x_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson(lean_object* v_json_946_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0));
lean_inc(v_json_946_);
v___x_948_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_946_, v___x_947_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_958_; 
lean_dec(v_json_946_);
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_958_ == 0)
{
v___x_951_ = v___x_948_;
v_isShared_952_ = v_isSharedCheck_958_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_948_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_958_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_953_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8);
v___x_954_ = lean_string_append(v___x_953_, v_a_949_);
lean_dec(v_a_949_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_954_);
v___x_956_ = v___x_951_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
else
{
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec(v_json_946_);
v_a_959_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_948_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_948_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 0);
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_a_967_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_948_, 1);
v___x_968_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1));
lean_inc(v_json_946_);
v___x_969_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(v_json_946_, v___x_968_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_979_; 
lean_dec(v_a_967_);
lean_dec(v_json_946_);
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_979_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_979_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_979_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_974_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13);
v___x_975_ = lean_string_append(v___x_974_, v_a_970_);
lean_dec(v_a_970_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_977_ = v___x_972_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
else
{
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec(v_a_967_);
lean_dec(v_json_946_);
v_a_980_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_969_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_969_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set_tag(v___x_982_, 0);
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_a_988_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_988_);
lean_dec_ref_known(v___x_969_, 1);
v___x_989_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2));
v___x_990_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(v_json_946_, v___x_989_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1000_; 
lean_dec(v_a_988_);
lean_dec(v_a_967_);
v_a_991_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_993_ = v___x_990_;
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_990_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_995_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18);
v___x_996_ = lean_string_append(v___x_995_, v_a_991_);
lean_dec(v_a_991_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_996_);
v___x_998_ = v___x_993_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v_a_988_);
lean_dec(v_a_967_);
v_a_1001_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_990_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_990_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
lean_ctor_set_tag(v___x_1003_, 0);
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1017_; 
v_a_1009_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1011_ = v___x_990_;
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_990_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1017_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1013_, 0, v_a_967_);
lean_ctor_set(v___x_1013_, 1, v_a_988_);
lean_ctor_set(v___x_1013_, 2, v_a_1009_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson_spec__0(lean_object* v_k_1020_, lean_object* v_x_1021_){
_start:
{
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_object* v___x_1022_; 
lean_dec_ref(v_k_1020_);
v___x_1022_ = lean_box(0);
return v___x_1022_;
}
else
{
lean_object* v_val_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v_val_1023_ = lean_ctor_get(v_x_1021_, 0);
lean_inc(v_val_1023_);
lean_dec_ref_known(v_x_1021_, 1);
v___x_1024_ = l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson(v_val_1023_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v_k_1020_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
return v___x_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson(lean_object* v_x_1030_){
_start:
{
lean_object* v_applyEdit_x3f_1031_; lean_object* v_workspaceEdit_x3f_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1048_; 
v_applyEdit_x3f_1031_ = lean_ctor_get(v_x_1030_, 0);
v_workspaceEdit_x3f_1032_ = lean_ctor_get(v_x_1030_, 1);
v_isSharedCheck_1048_ = !lean_is_exclusive(v_x_1030_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1034_ = v_x_1030_;
v_isShared_1035_ = v_isSharedCheck_1048_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_workspaceEdit_x3f_1032_);
lean_inc(v_applyEdit_x3f_1031_);
lean_dec(v_x_1030_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1048_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1036_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0));
v___x_1037_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_1036_, v_applyEdit_x3f_1031_);
lean_dec(v_applyEdit_x3f_1031_);
v___x_1038_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1));
v___x_1039_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson_spec__0(v___x_1038_, v_workspaceEdit_x3f_1032_);
v___x_1040_ = lean_box(0);
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 1);
lean_ctor_set(v___x_1034_, 1, v___x_1040_);
lean_ctor_set(v___x_1034_, 0, v___x_1039_);
v___x_1042_ = v___x_1034_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1047_, 1, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1037_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1045_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1043_, v___x_1044_);
v___x_1046_ = l_Lean_Json_mkObj(v___x_1045_);
lean_dec(v___x_1045_);
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1053_){
_start:
{
if (lean_obj_tag(v_x_1053_) == 0)
{
lean_object* v___x_1054_; 
v___x_1054_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson(v_x_1053_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1055_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1055_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1072_; 
v_a_1064_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1066_ = v___x_1055_;
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1055_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1068_, 0, v_a_1064_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(lean_object* v_j_1073_, lean_object* v_k_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = l_Lean_Json_getObjValD(v_j_1073_, v_k_1074_);
v___x_1076_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1077_, lean_object* v_k_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(v_j_1077_, v_k_1078_);
lean_dec_ref(v_k_1078_);
return v_res_1079_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1085_ = 1;
v___x_1086_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1));
v___x_1087_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1086_, v___x_1085_);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1089_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2);
v___x_1090_ = lean_string_append(v___x_1089_, v___x_1088_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1094_ = 1;
v___x_1095_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__5));
v___x_1096_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1095_, v___x_1094_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6);
v___x_1098_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3);
v___x_1099_ = lean_string_append(v___x_1098_, v___x_1097_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1101_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7);
v___x_1102_ = lean_string_append(v___x_1101_, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = 1;
v___x_1107_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__10));
v___x_1108_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1107_, v___x_1106_);
return v___x_1108_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11);
v___x_1110_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3);
v___x_1111_ = lean_string_append(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1113_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12);
v___x_1114_ = lean_string_append(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson(lean_object* v_json_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0));
lean_inc(v_json_1115_);
v___x_1117_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_1115_, v___x_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_json_1115_);
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1127_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1127_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
v___x_1122_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8);
v___x_1123_ = lean_string_append(v___x_1122_, v_a_1118_);
lean_dec(v_a_1118_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1123_);
v___x_1125_ = v___x_1120_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_json_1115_);
v_a_1128_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1117_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1117_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 0);
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v_a_1136_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1137_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1));
v___x_1138_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(v_json_1115_, v___x_1137_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_a_1136_);
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1148_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1148_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1146_; 
v___x_1143_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13);
v___x_1144_ = lean_string_append(v___x_1143_, v_a_1139_);
lean_dec(v_a_1139_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1144_);
v___x_1146_ = v___x_1141_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
else
{
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_a_1136_);
v_a_1149_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1138_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1138_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 0);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
v_a_1157_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1159_ = v___x_1138_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1138_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_a_1136_);
lean_ctor_set(v___x_1161_, 1, v_a_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(lean_object* v_k_1168_, lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
lean_object* v___x_1170_; 
lean_dec_ref(v_k_1168_);
v___x_1170_ = lean_box(0);
return v___x_1170_;
}
else
{
lean_object* v_val_1171_; uint8_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_val_1171_ = lean_ctor_get(v_x_1169_, 0);
v___x_1172_ = lean_unbox(v_val_1171_);
v___x_1173_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v___x_1172_);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_k_1168_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
v___x_1175_ = lean_box(0);
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_1177_, lean_object* v_x_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(v_k_1177_, v_x_1178_);
lean_dec(v_x_1178_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(lean_object* v_x_1183_){
_start:
{
lean_object* v_incrementalDiagnosticSupport_x3f_1184_; lean_object* v_silentDiagnosticSupport_x3f_1185_; lean_object* v_rpcWireFormat_x3f_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v_incrementalDiagnosticSupport_x3f_1184_ = lean_ctor_get(v_x_1183_, 0);
v_silentDiagnosticSupport_x3f_1185_ = lean_ctor_get(v_x_1183_, 1);
v_rpcWireFormat_x3f_1186_ = lean_ctor_get(v_x_1183_, 2);
v___x_1187_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0));
v___x_1188_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_1187_, v_incrementalDiagnosticSupport_x3f_1184_);
v___x_1189_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1));
v___x_1190_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_1189_, v_silentDiagnosticSupport_x3f_1185_);
v___x_1191_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2));
v___x_1192_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(v___x_1191_, v_rpcWireFormat_x3f_1186_);
v___x_1193_ = lean_box(0);
v___x_1194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1190_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v___x_1196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1188_);
lean_ctor_set(v___x_1196_, 1, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1198_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1196_, v___x_1197_);
v___x_1199_ = l_Lean_Json_mkObj(v___x_1198_);
lean_dec(v___x_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___boxed(lean_object* v_x_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(v_x_1200_);
lean_dec_ref(v_x_1200_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1206_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(v_x_1206_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
v_a_1217_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1219_ = v___x_1208_;
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1208_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_a_1217_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(lean_object* v_j_1226_, lean_object* v_k_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = l_Lean_Json_getObjValD(v_j_1226_, v_k_1227_);
v___x_1229_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0(v___x_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1230_, lean_object* v_k_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(v_j_1230_, v_k_1231_);
lean_dec_ref(v_k_1231_);
return v_res_1232_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = 1;
v___x_1239_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1));
v___x_1240_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1239_, v___x_1238_);
return v___x_1240_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1242_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2);
v___x_1243_ = lean_string_append(v___x_1242_, v___x_1241_);
return v___x_1243_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1247_ = 1;
v___x_1248_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__5));
v___x_1249_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1248_, v___x_1247_);
return v___x_1249_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6);
v___x_1251_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3);
v___x_1252_ = lean_string_append(v___x_1251_, v___x_1250_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1254_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7);
v___x_1255_ = lean_string_append(v___x_1254_, v___x_1253_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1259_ = 1;
v___x_1260_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__10));
v___x_1261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1260_, v___x_1259_);
return v___x_1261_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11);
v___x_1263_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3);
v___x_1264_ = lean_string_append(v___x_1263_, v___x_1262_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1266_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12);
v___x_1267_ = lean_string_append(v___x_1266_, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = 1;
v___x_1272_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__15));
v___x_1273_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1272_, v___x_1271_);
return v___x_1273_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16);
v___x_1275_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3);
v___x_1276_ = lean_string_append(v___x_1275_, v___x_1274_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1278_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17);
v___x_1279_ = lean_string_append(v___x_1278_, v___x_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson(lean_object* v_json_1280_){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0));
lean_inc(v_json_1280_);
v___x_1282_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_1280_, v___x_1281_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_json_1280_);
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1292_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1287_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8);
v___x_1288_ = lean_string_append(v___x_1287_, v_a_1283_);
lean_dec(v_a_1283_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1293_; lean_object* v___x_1295_; uint8_t v_isShared_1296_; uint8_t v_isSharedCheck_1300_; 
lean_dec(v_json_1280_);
v_a_1293_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1295_ = v___x_1282_;
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
else
{
lean_inc(v_a_1293_);
lean_dec(v___x_1282_);
v___x_1295_ = lean_box(0);
v_isShared_1296_ = v_isSharedCheck_1300_;
goto v_resetjp_1294_;
}
v_resetjp_1294_:
{
lean_object* v___x_1298_; 
if (v_isShared_1296_ == 0)
{
lean_ctor_set_tag(v___x_1295_, 0);
v___x_1298_ = v___x_1295_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_a_1293_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_a_1301_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1282_, 1);
v___x_1302_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1));
lean_inc(v_json_1280_);
v___x_1303_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_1280_, v___x_1302_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_a_1301_);
lean_dec(v_json_1280_);
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1313_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1313_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1308_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13);
v___x_1309_ = lean_string_append(v___x_1308_, v_a_1304_);
lean_dec(v_a_1304_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1309_);
v___x_1311_ = v___x_1306_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
else
{
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1321_; 
lean_dec(v_a_1301_);
lean_dec(v_json_1280_);
v_a_1314_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1316_ = v___x_1303_;
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1303_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1321_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1319_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set_tag(v___x_1316_, 0);
v___x_1319_ = v___x_1316_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1314_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v_a_1322_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1303_, 1);
v___x_1323_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2));
v___x_1324_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(v_json_1280_, v___x_1323_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1334_; 
lean_dec(v_a_1322_);
lean_dec(v_a_1301_);
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1334_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1334_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1332_; 
v___x_1329_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18);
v___x_1330_ = lean_string_append(v___x_1329_, v_a_1325_);
lean_dec(v_a_1325_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1330_);
v___x_1332_ = v___x_1327_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
else
{
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec(v_a_1322_);
lean_dec(v_a_1301_);
v_a_1335_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1324_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1324_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set_tag(v___x_1337_, 0);
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
v_a_1343_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1345_ = v___x_1324_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1324_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1347_, 0, v_a_1301_);
lean_ctor_set(v___x_1347_, 1, v_a_1322_);
lean_ctor_set(v___x_1347_, 2, v_a_1343_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__0(lean_object* v_k_1354_, lean_object* v_x_1355_){
_start:
{
if (lean_obj_tag(v_x_1355_) == 0)
{
lean_object* v___x_1356_; 
lean_dec_ref(v_k_1354_);
v___x_1356_ = lean_box(0);
return v___x_1356_;
}
else
{
lean_object* v_val_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_val_1357_ = lean_ctor_get(v_x_1355_, 0);
lean_inc(v_val_1357_);
lean_dec_ref_known(v_x_1355_, 1);
v___x_1358_ = l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson(v_val_1357_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_k_1354_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___x_1360_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(lean_object* v_k_1362_, lean_object* v_x_1363_){
_start:
{
if (lean_obj_tag(v_x_1363_) == 0)
{
lean_object* v___x_1364_; 
lean_dec_ref(v_k_1362_);
v___x_1364_ = lean_box(0);
return v___x_1364_;
}
else
{
lean_object* v_val_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v_val_1365_ = lean_ctor_get(v_x_1363_, 0);
v___x_1366_ = l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(v_val_1365_);
v___x_1367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1367_, 0, v_k_1362_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1___boxed(lean_object* v_k_1370_, lean_object* v_x_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(v_k_1370_, v_x_1371_);
lean_dec(v_x_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__2(lean_object* v_k_1373_, lean_object* v_x_1374_){
_start:
{
if (lean_obj_tag(v_x_1374_) == 0)
{
lean_object* v___x_1375_; 
lean_dec_ref(v_k_1373_);
v___x_1375_ = lean_box(0);
return v___x_1375_;
}
else
{
lean_object* v_val_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_val_1376_ = lean_ctor_get(v_x_1374_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v_x_1374_, 1);
v___x_1377_ = l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson(v_val_1376_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_k_1373_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
return v___x_1380_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(lean_object* v_k_1381_, lean_object* v_x_1382_){
_start:
{
if (lean_obj_tag(v_x_1382_) == 0)
{
lean_object* v___x_1383_; 
lean_dec_ref(v_k_1381_);
v___x_1383_ = lean_box(0);
return v___x_1383_;
}
else
{
lean_object* v_val_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_val_1384_ = lean_ctor_get(v_x_1382_, 0);
v___x_1385_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(v_val_1384_);
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_k_1381_);
lean_ctor_set(v___x_1386_, 1, v___x_1385_);
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1388_, 0, v___x_1386_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3___boxed(lean_object* v_k_1389_, lean_object* v_x_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(v_k_1389_, v_x_1390_);
lean_dec(v_x_1390_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonClientCapabilities_toJson(lean_object* v_x_1396_){
_start:
{
lean_object* v_textDocument_x3f_1397_; lean_object* v_window_x3f_1398_; lean_object* v_workspace_x3f_1399_; lean_object* v_lean_x3f_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_textDocument_x3f_1397_ = lean_ctor_get(v_x_1396_, 0);
lean_inc(v_textDocument_x3f_1397_);
v_window_x3f_1398_ = lean_ctor_get(v_x_1396_, 1);
lean_inc(v_window_x3f_1398_);
v_workspace_x3f_1399_ = lean_ctor_get(v_x_1396_, 2);
lean_inc(v_workspace_x3f_1399_);
v_lean_x3f_1400_ = lean_ctor_get(v_x_1396_, 3);
lean_inc(v_lean_x3f_1400_);
lean_dec_ref(v_x_1396_);
v___x_1401_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0));
v___x_1402_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__0(v___x_1401_, v_textDocument_x3f_1397_);
v___x_1403_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1));
v___x_1404_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(v___x_1403_, v_window_x3f_1398_);
lean_dec(v_window_x3f_1398_);
v___x_1405_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2));
v___x_1406_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__2(v___x_1405_, v_workspace_x3f_1399_);
v___x_1407_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3));
v___x_1408_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(v___x_1407_, v_lean_x3f_1400_);
lean_dec(v_lean_x3f_1400_);
v___x_1409_ = lean_box(0);
v___x_1410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1406_);
lean_ctor_set(v___x_1411_, 1, v___x_1410_);
v___x_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1404_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1402_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1415_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1413_, v___x_1414_);
v___x_1416_ = l_Lean_Json_mkObj(v___x_1415_);
lean_dec(v___x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4(lean_object* v_x_1421_){
_start:
{
if (lean_obj_tag(v_x_1421_) == 0)
{
lean_object* v___x_1422_; 
v___x_1422_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4___closed__0));
return v___x_1422_;
}
else
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson(v_x_1421_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1440_; 
v_a_1432_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1434_ = v___x_1423_;
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1423_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1432_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v___x_1436_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(lean_object* v_j_1441_, lean_object* v_k_1442_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = l_Lean_Json_getObjValD(v_j_1441_, v_k_1442_);
v___x_1444_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4(v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2___boxed(lean_object* v_j_1445_, lean_object* v_k_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(v_j_1445_, v_k_1446_);
lean_dec_ref(v_k_1446_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6(lean_object* v_x_1450_){
_start:
{
if (lean_obj_tag(v_x_1450_) == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6___closed__0));
return v___x_1451_;
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson(v_x_1450_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_a_1461_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1463_ = v___x_1452_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1452_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1465_, 0, v_a_1461_);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 0, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(lean_object* v_j_1470_, lean_object* v_k_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = l_Lean_Json_getObjValD(v_j_1470_, v_k_1471_);
v___x_1473_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6(v___x_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3___boxed(lean_object* v_j_1474_, lean_object* v_k_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(v_j_1474_, v_k_1475_);
lean_dec_ref(v_k_1475_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_1477_){
_start:
{
if (lean_obj_tag(v_x_1477_) == 0)
{
lean_object* v___x_1478_; 
v___x_1478_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1478_;
}
else
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson(v_x_1477_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1496_; 
v_a_1488_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1490_ = v___x_1479_;
v_isShared_1491_ = v_isSharedCheck_1496_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1479_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1496_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_a_1488_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v___x_1492_);
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(lean_object* v_j_1497_, lean_object* v_k_1498_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = l_Lean_Json_getObjValD(v_j_1497_, v_k_1498_);
v___x_1500_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1_spec__2(v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1___boxed(lean_object* v_j_1501_, lean_object* v_k_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(v_j_1501_, v_k_1502_);
lean_dec_ref(v_k_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1506_){
_start:
{
if (lean_obj_tag(v_x_1506_) == 0)
{
lean_object* v___x_1507_; 
v___x_1507_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1507_;
}
else
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson(v_x_1506_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
else
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1525_; 
v_a_1517_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1519_ = v___x_1508_;
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1508_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1525_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1521_, 0, v_a_1517_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1521_);
v___x_1523_ = v___x_1519_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(lean_object* v_j_1526_, lean_object* v_k_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = l_Lean_Json_getObjValD(v_j_1526_, v_k_1527_);
v___x_1529_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0(v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1530_, lean_object* v_k_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(v_j_1530_, v_k_1531_);
lean_dec_ref(v_k_1531_);
return v_res_1532_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = 1;
v___x_1539_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1));
v___x_1540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1539_, v___x_1538_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1542_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2);
v___x_1543_ = lean_string_append(v___x_1542_, v___x_1541_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = 1;
v___x_1548_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__5));
v___x_1549_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1548_, v___x_1547_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6);
v___x_1551_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1552_ = lean_string_append(v___x_1551_, v___x_1550_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1554_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7);
v___x_1555_ = lean_string_append(v___x_1554_, v___x_1553_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = 1;
v___x_1560_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__10));
v___x_1561_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1560_, v___x_1559_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11);
v___x_1563_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1564_ = lean_string_append(v___x_1563_, v___x_1562_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1566_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12);
v___x_1567_ = lean_string_append(v___x_1566_, v___x_1565_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = 1;
v___x_1572_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__15));
v___x_1573_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1572_, v___x_1571_);
return v___x_1573_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16);
v___x_1575_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1576_ = lean_string_append(v___x_1575_, v___x_1574_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1578_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17);
v___x_1579_ = lean_string_append(v___x_1578_, v___x_1577_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = 1;
v___x_1584_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__20));
v___x_1585_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1584_, v___x_1583_);
return v___x_1585_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21);
v___x_1587_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1588_ = lean_string_append(v___x_1587_, v___x_1586_);
return v___x_1588_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1590_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22);
v___x_1591_ = lean_string_append(v___x_1590_, v___x_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson(lean_object* v_json_1592_){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0));
lean_inc(v_json_1592_);
v___x_1594_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(v_json_1592_, v___x_1593_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1604_; 
lean_dec(v_json_1592_);
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1604_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1599_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8);
v___x_1600_ = lean_string_append(v___x_1599_, v_a_1595_);
lean_dec(v_a_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1600_);
v___x_1602_ = v___x_1597_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
else
{
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
lean_dec(v_json_1592_);
v_a_1605_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v___x_1594_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1594_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 0);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v_a_1613_ = lean_ctor_get(v___x_1594_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v___x_1594_, 1);
v___x_1614_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1));
lean_inc(v_json_1592_);
v___x_1615_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(v_json_1592_, v___x_1614_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v_a_1613_);
lean_dec(v_json_1592_);
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1625_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1620_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13);
v___x_1621_ = lean_string_append(v___x_1620_, v_a_1616_);
lean_dec(v_a_1616_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 0, v___x_1621_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
else
{
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v_a_1613_);
lean_dec(v_json_1592_);
v_a_1626_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1615_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1615_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set_tag(v___x_1628_, 0);
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_a_1634_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v___x_1615_, 1);
v___x_1635_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2));
lean_inc(v_json_1592_);
v___x_1636_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(v_json_1592_, v___x_1635_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_a_1634_);
lean_dec(v_a_1613_);
lean_dec(v_json_1592_);
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1646_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1646_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1641_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18);
v___x_1642_ = lean_string_append(v___x_1641_, v_a_1637_);
lean_dec(v_a_1637_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v___x_1642_);
v___x_1644_ = v___x_1639_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
else
{
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
lean_dec(v_a_1634_);
lean_dec(v_a_1613_);
lean_dec(v_json_1592_);
v_a_1647_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v___x_1636_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1636_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 0);
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_a_1655_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1655_);
lean_dec_ref_known(v___x_1636_, 1);
v___x_1656_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3));
v___x_1657_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(v_json_1592_, v___x_1656_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1667_; 
lean_dec(v_a_1655_);
lean_dec(v_a_1634_);
lean_dec(v_a_1613_);
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1660_ = v___x_1657_;
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1657_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1662_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23);
v___x_1663_ = lean_string_append(v___x_1662_, v_a_1658_);
lean_dec(v_a_1658_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 0, v___x_1663_);
v___x_1665_ = v___x_1660_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec(v_a_1655_);
lean_dec(v_a_1634_);
lean_dec(v_a_1613_);
v_a_1668_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1657_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1657_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 0);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1684_; 
v_a_1676_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1678_ = v___x_1657_;
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v___x_1657_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1680_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1680_, 0, v_a_1613_);
lean_ctor_set(v___x_1680_, 1, v_a_1634_);
lean_ctor_set(v___x_1680_, 2, v_a_1655_);
lean_ctor_set(v___x_1680_, 3, v_a_1676_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1680_);
v___x_1682_ = v___x_1678_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
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
LEAN_EXPORT uint8_t l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport(lean_object* v_c_1687_){
_start:
{
lean_object* v_lean_x3f_1688_; 
v_lean_x3f_1688_ = lean_ctor_get(v_c_1687_, 3);
if (lean_obj_tag(v_lean_x3f_1688_) == 1)
{
lean_object* v_val_1689_; lean_object* v_incrementalDiagnosticSupport_x3f_1690_; 
v_val_1689_ = lean_ctor_get(v_lean_x3f_1688_, 0);
v_incrementalDiagnosticSupport_x3f_1690_ = lean_ctor_get(v_val_1689_, 0);
if (lean_obj_tag(v_incrementalDiagnosticSupport_x3f_1690_) == 1)
{
lean_object* v_val_1691_; uint8_t v___x_1692_; 
v_val_1691_ = lean_ctor_get(v_incrementalDiagnosticSupport_x3f_1690_, 0);
v___x_1692_ = lean_unbox(v_val_1691_);
return v___x_1692_;
}
else
{
uint8_t v___x_1693_; 
v___x_1693_ = 0;
return v___x_1693_;
}
}
else
{
uint8_t v___x_1694_; 
v___x_1694_ = 0;
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport___boxed(lean_object* v_c_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport(v_c_1695_);
lean_dec_ref(v_c_1695_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(lean_object* v_c_1698_){
_start:
{
lean_object* v_lean_x3f_1699_; 
v_lean_x3f_1699_ = lean_ctor_get(v_c_1698_, 3);
if (lean_obj_tag(v_lean_x3f_1699_) == 1)
{
lean_object* v_val_1700_; lean_object* v_silentDiagnosticSupport_x3f_1701_; 
v_val_1700_ = lean_ctor_get(v_lean_x3f_1699_, 0);
v_silentDiagnosticSupport_x3f_1701_ = lean_ctor_get(v_val_1700_, 1);
if (lean_obj_tag(v_silentDiagnosticSupport_x3f_1701_) == 1)
{
lean_object* v_val_1702_; uint8_t v___x_1703_; 
v_val_1702_ = lean_ctor_get(v_silentDiagnosticSupport_x3f_1701_, 0);
v___x_1703_ = lean_unbox(v_val_1702_);
return v___x_1703_;
}
else
{
uint8_t v___x_1704_; 
v___x_1704_ = 0;
return v___x_1704_;
}
}
else
{
uint8_t v___x_1705_; 
v___x_1705_ = 0;
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport___boxed(lean_object* v_c_1706_){
_start:
{
uint8_t v_res_1707_; lean_object* v_r_1708_; 
v_res_1707_ = l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(v_c_1706_);
lean_dec_ref(v_c_1706_);
v_r_1708_ = lean_box(v_res_1707_);
return v_r_1708_;
}
}
LEAN_EXPORT uint8_t l_Lean_Lsp_ClientCapabilities_rpcWireFormat(lean_object* v_c_1709_){
_start:
{
lean_object* v_lean_x3f_1710_; 
v_lean_x3f_1710_ = lean_ctor_get(v_c_1709_, 3);
if (lean_obj_tag(v_lean_x3f_1710_) == 1)
{
lean_object* v_val_1711_; lean_object* v_rpcWireFormat_x3f_1712_; 
v_val_1711_ = lean_ctor_get(v_lean_x3f_1710_, 0);
v_rpcWireFormat_x3f_1712_ = lean_ctor_get(v_val_1711_, 2);
if (lean_obj_tag(v_rpcWireFormat_x3f_1712_) == 1)
{
lean_object* v_val_1713_; uint8_t v___x_1714_; 
v_val_1713_ = lean_ctor_get(v_rpcWireFormat_x3f_1712_, 0);
v___x_1714_ = lean_unbox(v_val_1713_);
return v___x_1714_;
}
else
{
uint8_t v___x_1715_; 
v___x_1715_ = 0;
return v___x_1715_;
}
}
else
{
uint8_t v___x_1716_; 
v___x_1716_ = 0;
return v___x_1716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_rpcWireFormat___boxed(lean_object* v_c_1717_){
_start:
{
uint8_t v_res_1718_; lean_object* v_r_1719_; 
v_res_1718_ = l_Lean_Lsp_ClientCapabilities_rpcWireFormat(v_c_1717_);
lean_dec_ref(v_c_1717_);
v_r_1719_ = lean_box(v_res_1718_);
return v_r_1719_;
}
}
static lean_object* _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1723_){
_start:
{
if (lean_obj_tag(v_x_1723_) == 0)
{
lean_object* v___x_1724_; 
v___x_1724_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_obj_once(&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1, &l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1_once, _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v_a_1726_);
return v___x_1727_;
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_a_1728_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1728_);
v___x_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1729_, 0, v_a_1728_);
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___boxed(lean_object* v_x_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(v_x_1731_);
lean_dec(v_x_1731_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(lean_object* v_j_1733_, lean_object* v_k_1734_){
_start:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1735_ = l_Lean_Json_getObjValD(v_j_1733_, v_k_1734_);
v___x_1736_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(v___x_1735_);
lean_dec(v___x_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1737_, lean_object* v_k_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(v_j_1737_, v_k_1738_);
lean_dec_ref(v_k_1738_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_1742_){
_start:
{
if (lean_obj_tag(v_x_1742_) == 0)
{
lean_object* v___x_1743_; 
v___x_1743_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson(v_x_1742_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1761_; 
v_a_1753_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1755_ = v___x_1744_;
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1744_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_a_1753_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1757_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(lean_object* v_j_1762_, lean_object* v_k_1763_){
_start:
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1764_ = l_Lean_Json_getObjValD(v_j_1762_, v_k_1763_);
v___x_1765_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2(v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1___boxed(lean_object* v_j_1766_, lean_object* v_k_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(v_j_1766_, v_k_1767_);
lean_dec_ref(v_k_1767_);
return v_res_1768_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = 1;
v___x_1776_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2));
v___x_1777_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1776_, v___x_1775_);
return v___x_1777_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1779_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3);
v___x_1780_ = lean_string_append(v___x_1779_, v___x_1778_);
return v___x_1780_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = 1;
v___x_1785_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__6));
v___x_1786_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1785_, v___x_1784_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1787_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7);
v___x_1788_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4);
v___x_1789_ = lean_string_append(v___x_1788_, v___x_1787_);
return v___x_1789_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1791_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8);
v___x_1792_ = lean_string_append(v___x_1791_, v___x_1790_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = 1;
v___x_1798_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__12));
v___x_1799_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1798_, v___x_1797_);
return v___x_1799_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13);
v___x_1801_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4);
v___x_1802_ = lean_string_append(v___x_1801_, v___x_1800_);
return v___x_1802_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1804_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14);
v___x_1805_ = lean_string_append(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson(lean_object* v_json_1806_){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0));
lean_inc(v_json_1806_);
v___x_1808_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(v_json_1806_, v___x_1807_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1818_; 
lean_dec(v_json_1806_);
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1818_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1813_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9);
v___x_1814_ = lean_string_append(v___x_1813_, v_a_1809_);
lean_dec(v_a_1809_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1814_);
v___x_1816_ = v___x_1811_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
else
{
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec(v_json_1806_);
v_a_1819_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1808_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1808_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set_tag(v___x_1821_, 0);
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_a_1827_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1828_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10));
v___x_1829_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(v_json_1806_, v___x_1828_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_a_1827_);
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1839_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1834_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15);
v___x_1835_ = lean_string_append(v___x_1834_, v_a_1830_);
lean_dec(v_a_1830_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1835_);
v___x_1837_ = v___x_1832_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_a_1827_);
v_a_1840_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1829_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1829_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set_tag(v___x_1842_, 0);
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1856_; 
v_a_1848_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1850_ = v___x_1829_;
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1829_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1856_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v_a_1827_);
lean_ctor_set(v___x_1852_, 1, v_a_1848_);
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1852_);
v___x_1854_ = v___x_1850_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(lean_object* v_k_1860_, lean_object* v_x_1861_){
_start:
{
if (lean_obj_tag(v_x_1861_) == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref(v_k_1860_);
v___x_1862_ = lean_box(0);
return v___x_1862_;
}
else
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = lean_obj_once(&l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0, &l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0_once, _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v_k_1860_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
return v___x_1866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___boxed(lean_object* v_k_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(v_k_1867_, v_x_1868_);
lean_dec(v_x_1868_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__1(lean_object* v_k_1870_, lean_object* v_x_1871_){
_start:
{
if (lean_obj_tag(v_x_1871_) == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v_k_1870_);
v___x_1872_ = lean_box(0);
return v___x_1872_;
}
else
{
lean_object* v_val_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_val_1873_ = lean_ctor_get(v_x_1871_, 0);
lean_inc(v_val_1873_);
lean_dec_ref_known(v_x_1871_, 1);
v___x_1874_ = l_Lean_Lsp_instToJsonRpcOptions_toJson(v_val_1873_);
v___x_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1875_, 0, v_k_1870_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_box(0);
v___x_1877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson(lean_object* v_x_1878_){
_start:
{
lean_object* v_moduleHierarchyProvider_x3f_1879_; lean_object* v_rpcProvider_x3f_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1896_; 
v_moduleHierarchyProvider_x3f_1879_ = lean_ctor_get(v_x_1878_, 0);
v_rpcProvider_x3f_1880_ = lean_ctor_get(v_x_1878_, 1);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_x_1878_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1882_ = v_x_1878_;
v_isShared_1883_ = v_isSharedCheck_1896_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_rpcProvider_x3f_1880_);
lean_inc(v_moduleHierarchyProvider_x3f_1879_);
lean_dec(v_x_1878_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1896_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1884_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0));
v___x_1885_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(v___x_1884_, v_moduleHierarchyProvider_x3f_1879_);
lean_dec(v_moduleHierarchyProvider_x3f_1879_);
v___x_1886_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10));
v___x_1887_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__1(v___x_1886_, v_rpcProvider_x3f_1880_);
v___x_1888_ = lean_box(0);
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 1);
lean_ctor_set(v___x_1882_, 1, v___x_1888_);
lean_ctor_set(v___x_1882_, 0, v___x_1887_);
v___x_1890_ = v___x_1882_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1885_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1893_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1891_, v___x_1892_);
v___x_1894_ = l_Lean_Json_mkObj(v___x_1893_);
lean_dec(v___x_1893_);
return v___x_1894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(lean_object* v_k_1899_, lean_object* v_x_1900_){
_start:
{
if (lean_obj_tag(v_x_1900_) == 0)
{
lean_object* v___x_1901_; 
lean_dec_ref(v_k_1899_);
v___x_1901_ = lean_box(0);
return v___x_1901_;
}
else
{
lean_object* v_val_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_val_1902_ = lean_ctor_get(v_x_1900_, 0);
v___x_1903_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(v_val_1902_);
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_k_1899_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1904_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0___boxed(lean_object* v_k_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(v_k_1907_, v_x_1908_);
lean_dec(v_x_1908_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__1(lean_object* v_k_1910_, lean_object* v_x_1911_){
_start:
{
if (lean_obj_tag(v_x_1911_) == 0)
{
lean_object* v___x_1912_; 
lean_dec_ref(v_k_1910_);
v___x_1912_ = lean_box(0);
return v___x_1912_;
}
else
{
lean_object* v_val_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v_val_1913_ = lean_ctor_get(v_x_1911_, 0);
lean_inc(v_val_1913_);
lean_dec_ref_known(v_x_1911_, 1);
v___x_1914_ = l_Lean_Lsp_instToJsonCompletionOptions_toJson(v_val_1913_);
v___x_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_k_1910_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_box(0);
v___x_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
return v___x_1917_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(lean_object* v_k_1918_, lean_object* v_x_1919_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
lean_object* v___x_1920_; 
lean_dec_ref(v_k_1918_);
v___x_1920_ = lean_box(0);
return v___x_1920_;
}
else
{
lean_object* v_val_1921_; uint8_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_val_1921_ = lean_ctor_get(v_x_1919_, 0);
v___x_1922_ = lean_unbox(v_val_1921_);
v___x_1923_ = l_Lean_Lsp_instToJsonRenameOptions_toJson(v___x_1922_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v_k_1918_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_box(0);
v___x_1926_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2___boxed(lean_object* v_k_1927_, lean_object* v_x_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(v_k_1927_, v_x_1928_);
lean_dec(v_x_1928_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__3(lean_object* v_k_1930_, lean_object* v_x_1931_){
_start:
{
if (lean_obj_tag(v_x_1931_) == 0)
{
lean_object* v___x_1932_; 
lean_dec_ref(v_k_1930_);
v___x_1932_ = lean_box(0);
return v___x_1932_;
}
else
{
lean_object* v_val_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_val_1933_ = lean_ctor_get(v_x_1931_, 0);
lean_inc(v_val_1933_);
lean_dec_ref_known(v_x_1931_, 1);
v___x_1934_ = l_Lean_Lsp_instToJsonSemanticTokensOptions_toJson(v_val_1933_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v_k_1930_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_box(0);
v___x_1937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__4(lean_object* v_k_1938_, lean_object* v_x_1939_){
_start:
{
if (lean_obj_tag(v_x_1939_) == 0)
{
lean_object* v___x_1940_; 
lean_dec_ref(v_k_1938_);
v___x_1940_ = lean_box(0);
return v___x_1940_;
}
else
{
lean_object* v_val_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_val_1941_ = lean_ctor_get(v_x_1939_, 0);
lean_inc(v_val_1941_);
lean_dec_ref_known(v_x_1939_, 1);
v___x_1942_ = l_Lean_Lsp_instToJsonCodeActionOptions_toJson(v_val_1941_);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v_k_1938_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_box(0);
v___x_1945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(lean_object* v_k_1946_, lean_object* v_x_1947_){
_start:
{
if (lean_obj_tag(v_x_1947_) == 0)
{
lean_object* v___x_1948_; 
lean_dec_ref(v_k_1946_);
v___x_1948_ = lean_box(0);
return v___x_1948_;
}
else
{
lean_object* v_val_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_val_1949_ = lean_ctor_get(v_x_1947_, 0);
v___x_1950_ = l_Lean_Lsp_instToJsonInlayHintOptions_toJson(v_val_1949_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_k_1946_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_box(0);
v___x_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
return v___x_1953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5___boxed(lean_object* v_k_1954_, lean_object* v_x_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(v_k_1954_, v_x_1955_);
lean_dec(v_x_1955_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__6(lean_object* v_k_1957_, lean_object* v_x_1958_){
_start:
{
if (lean_obj_tag(v_x_1958_) == 0)
{
lean_object* v___x_1959_; 
lean_dec_ref(v_k_1957_);
v___x_1959_ = lean_box(0);
return v___x_1959_;
}
else
{
lean_object* v_val_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v_val_1960_ = lean_ctor_get(v_x_1958_, 0);
lean_inc(v_val_1960_);
lean_dec_ref_known(v_x_1958_, 1);
v___x_1961_ = l_Lean_Lsp_instToJsonSignatureHelpOptions_toJson(v_val_1960_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_k_1957_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(lean_object* v_k_1965_, lean_object* v_x_1966_){
_start:
{
if (lean_obj_tag(v_x_1966_) == 0)
{
lean_object* v___x_1967_; 
lean_dec_ref(v_k_1965_);
v___x_1967_ = lean_box(0);
return v___x_1967_;
}
else
{
lean_object* v_val_1968_; uint8_t v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_val_1968_ = lean_ctor_get(v_x_1966_, 0);
v___x_1969_ = lean_unbox(v_val_1968_);
v___x_1970_ = l_Lean_Lsp_instToJsonDocumentColorOptions_toJson(v___x_1969_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v_k_1965_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_box(0);
v___x_1973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
return v___x_1973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7___boxed(lean_object* v_k_1974_, lean_object* v_x_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(v_k_1974_, v_x_1975_);
lean_dec(v_x_1975_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__8(lean_object* v_k_1977_, lean_object* v_x_1978_){
_start:
{
if (lean_obj_tag(v_x_1978_) == 0)
{
lean_object* v___x_1979_; 
lean_dec_ref(v_k_1977_);
v___x_1979_ = lean_box(0);
return v___x_1979_;
}
else
{
lean_object* v_val_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v_val_1980_ = lean_ctor_get(v_x_1978_, 0);
lean_inc(v_val_1980_);
lean_dec_ref_known(v_x_1978_, 1);
v___x_1981_ = l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson(v_val_1980_);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v_k_1977_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_box(0);
v___x_1984_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
return v___x_1984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson(lean_object* v_x_2004_){
_start:
{
lean_object* v_textDocumentSync_x3f_2005_; lean_object* v_completionProvider_x3f_2006_; uint8_t v_hoverProvider_2007_; uint8_t v_documentHighlightProvider_2008_; uint8_t v_documentSymbolProvider_2009_; uint8_t v_definitionProvider_2010_; uint8_t v_declarationProvider_2011_; uint8_t v_typeDefinitionProvider_2012_; uint8_t v_referencesProvider_2013_; uint8_t v_callHierarchyProvider_2014_; lean_object* v_renameProvider_x3f_2015_; uint8_t v_workspaceSymbolProvider_2016_; uint8_t v_foldingRangeProvider_2017_; lean_object* v_semanticTokensProvider_x3f_2018_; lean_object* v_codeActionProvider_x3f_2019_; lean_object* v_inlayHintProvider_x3f_2020_; lean_object* v_signatureHelpProvider_x3f_2021_; lean_object* v_colorProvider_x3f_2022_; lean_object* v_experimental_x3f_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v_textDocumentSync_x3f_2005_ = lean_ctor_get(v_x_2004_, 0);
lean_inc(v_textDocumentSync_x3f_2005_);
v_completionProvider_x3f_2006_ = lean_ctor_get(v_x_2004_, 1);
lean_inc(v_completionProvider_x3f_2006_);
v_hoverProvider_2007_ = lean_ctor_get_uint8(v_x_2004_, sizeof(void*)*9);
v_documentHighlightProvider_2008_ = lean_ctor_get_uint8(v_x_2004_, sizeof(void*)*9 + 1);
v_documentSymbolProvider_2009_ = lean_ctor_get_uint8(v_x_2004_, sizeof(void*)*9 + 2);
v_definitionProvider_2010_ = lean_ctor_get_uint8(v_x_2004_, sizeof(void*)*9 + 3);
v_declarationProvider_2011_ = lean_ctor_get_uint8(v_x_2004_, sizeof(void*)*9 + 4);
v_typeDefinitionProvider_2012_ = lean_ctor_get_uint8(v_x_2004_, sizeof(void*)*9 + 5);
v_referencesProvider_2013_ = lean_ctor_get_uint8(v_x_2004_, sizeof(void*)*9 + 6);
v_callHierarchyProvider_2014_ = lean_ctor_get_uint8(v_x_2004_, sizeof(void*)*9 + 7);
v_renameProvider_x3f_2015_ = lean_ctor_get(v_x_2004_, 2);
lean_inc(v_renameProvider_x3f_2015_);
v_workspaceSymbolProvider_2016_ = lean_ctor_get_uint8(v_x_2004_, sizeof(void*)*9 + 8);
v_foldingRangeProvider_2017_ = lean_ctor_get_uint8(v_x_2004_, sizeof(void*)*9 + 9);
v_semanticTokensProvider_x3f_2018_ = lean_ctor_get(v_x_2004_, 3);
lean_inc(v_semanticTokensProvider_x3f_2018_);
v_codeActionProvider_x3f_2019_ = lean_ctor_get(v_x_2004_, 4);
lean_inc(v_codeActionProvider_x3f_2019_);
v_inlayHintProvider_x3f_2020_ = lean_ctor_get(v_x_2004_, 5);
lean_inc(v_inlayHintProvider_x3f_2020_);
v_signatureHelpProvider_x3f_2021_ = lean_ctor_get(v_x_2004_, 6);
lean_inc(v_signatureHelpProvider_x3f_2021_);
v_colorProvider_x3f_2022_ = lean_ctor_get(v_x_2004_, 7);
lean_inc(v_colorProvider_x3f_2022_);
v_experimental_x3f_2023_ = lean_ctor_get(v_x_2004_, 8);
lean_inc(v_experimental_x3f_2023_);
lean_dec_ref(v_x_2004_);
v___x_2024_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0));
v___x_2025_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(v___x_2024_, v_textDocumentSync_x3f_2005_);
lean_dec(v_textDocumentSync_x3f_2005_);
v___x_2026_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1));
v___x_2027_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__1(v___x_2026_, v_completionProvider_x3f_2006_);
v___x_2028_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2));
v___x_2029_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2029_, 0, v_hoverProvider_2007_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_box(0);
v___x_2032_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3));
v___x_2034_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2034_, 0, v_documentHighlightProvider_2008_);
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2033_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
v___x_2036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v___x_2031_);
v___x_2037_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4));
v___x_2038_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2038_, 0, v_documentSymbolProvider_2009_);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2037_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
v___x_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v___x_2031_);
v___x_2041_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5));
v___x_2042_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2042_, 0, v_definitionProvider_2010_);
v___x_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2041_);
lean_ctor_set(v___x_2043_, 1, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2031_);
v___x_2045_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6));
v___x_2046_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2046_, 0, v_declarationProvider_2011_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2045_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
lean_ctor_set(v___x_2048_, 1, v___x_2031_);
v___x_2049_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7));
v___x_2050_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2050_, 0, v_typeDefinitionProvider_2012_);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2049_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
v___x_2052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v___x_2031_);
v___x_2053_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8));
v___x_2054_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2054_, 0, v_referencesProvider_2013_);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2053_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v___x_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
lean_ctor_set(v___x_2056_, 1, v___x_2031_);
v___x_2057_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9));
v___x_2058_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2058_, 0, v_callHierarchyProvider_2014_);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2057_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v___x_2031_);
v___x_2061_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10));
v___x_2062_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(v___x_2061_, v_renameProvider_x3f_2015_);
lean_dec(v_renameProvider_x3f_2015_);
v___x_2063_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11));
v___x_2064_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2064_, 0, v_workspaceSymbolProvider_2016_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v___x_2031_);
v___x_2067_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12));
v___x_2068_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2068_, 0, v_foldingRangeProvider_2017_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___x_2031_);
v___x_2071_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13));
v___x_2072_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__3(v___x_2071_, v_semanticTokensProvider_x3f_2018_);
v___x_2073_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14));
v___x_2074_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__4(v___x_2073_, v_codeActionProvider_x3f_2019_);
v___x_2075_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15));
v___x_2076_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(v___x_2075_, v_inlayHintProvider_x3f_2020_);
lean_dec(v_inlayHintProvider_x3f_2020_);
v___x_2077_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16));
v___x_2078_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__6(v___x_2077_, v_signatureHelpProvider_x3f_2021_);
v___x_2079_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17));
v___x_2080_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(v___x_2079_, v_colorProvider_x3f_2022_);
lean_dec(v_colorProvider_x3f_2022_);
v___x_2081_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18));
v___x_2082_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__8(v___x_2081_, v_experimental_x3f_2023_);
v___x_2083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
lean_ctor_set(v___x_2083_, 1, v___x_2031_);
v___x_2084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2080_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2078_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2076_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2074_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2072_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2070_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2066_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2062_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2060_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2056_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2052_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2048_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2044_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2040_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2036_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2032_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2027_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2025_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_2103_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_2101_, v___x_2102_);
v___x_2104_ = l_Lean_Json_mkObj(v___x_2103_);
lean_dec(v___x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10(lean_object* v_x_2109_){
_start:
{
if (lean_obj_tag(v_x_2109_) == 0)
{
lean_object* v___x_2110_; 
v___x_2110_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10___closed__0));
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; 
v___x_2111_ = l_Lean_Lsp_instFromJsonInlayHintOptions_fromJson(v_x_2109_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2119_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2119_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2117_; 
if (v_isShared_2115_ == 0)
{
v___x_2117_ = v___x_2114_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_a_2112_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2128_; 
v_a_2120_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2122_ = v___x_2111_;
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2111_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2128_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_a_2120_);
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 0, v___x_2124_);
v___x_2126_ = v___x_2122_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(lean_object* v_j_2129_, lean_object* v_k_2130_){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = l_Lean_Json_getObjValD(v_j_2129_, v_k_2130_);
v___x_2132_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10(v___x_2131_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5___boxed(lean_object* v_j_2133_, lean_object* v_k_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(v_j_2133_, v_k_2134_);
lean_dec_ref(v_k_2134_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8(lean_object* v_x_2138_){
_start:
{
if (lean_obj_tag(v_x_2138_) == 0)
{
lean_object* v___x_2139_; 
v___x_2139_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8___closed__0));
return v___x_2139_;
}
else
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson(v_x_2138_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2140_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2140_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2157_; 
v_a_2149_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2151_ = v___x_2140_;
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2140_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2155_; 
v___x_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_a_2149_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2153_);
v___x_2155_ = v___x_2151_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(lean_object* v_j_2158_, lean_object* v_k_2159_){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = l_Lean_Json_getObjValD(v_j_2158_, v_k_2159_);
v___x_2161_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8(v___x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4___boxed(lean_object* v_j_2162_, lean_object* v_k_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(v_j_2162_, v_k_2163_);
lean_dec_ref(v_k_2163_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16(lean_object* v_x_2167_){
_start:
{
if (lean_obj_tag(v_x_2167_) == 0)
{
lean_object* v___x_2168_; 
v___x_2168_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16___closed__0));
return v___x_2168_;
}
else
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson(v_x_2167_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2186_; 
v_a_2178_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2180_ = v___x_2169_;
v_isShared_2181_ = v_isSharedCheck_2186_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2169_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2186_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_a_2178_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2182_);
v___x_2184_ = v___x_2180_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(lean_object* v_j_2187_, lean_object* v_k_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = l_Lean_Json_getObjValD(v_j_2187_, v_k_2188_);
v___x_2190_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16(v___x_2189_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8___boxed(lean_object* v_j_2191_, lean_object* v_k_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(v_j_2191_, v_k_2192_);
lean_dec_ref(v_k_2192_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12(lean_object* v_x_2196_){
_start:
{
if (lean_obj_tag(v_x_2196_) == 0)
{
lean_object* v___x_2197_; 
v___x_2197_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12___closed__0));
return v___x_2197_;
}
else
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Lean_Lsp_instFromJsonSignatureHelpOptions_fromJson(v_x_2196_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_a_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2215_; 
v_a_2207_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2209_ = v___x_2198_;
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2198_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2215_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_a_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(lean_object* v_j_2216_, lean_object* v_k_2217_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = l_Lean_Json_getObjValD(v_j_2216_, v_k_2217_);
v___x_2219_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12(v___x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6___boxed(lean_object* v_j_2220_, lean_object* v_k_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(v_j_2220_, v_k_2221_);
lean_dec_ref(v_k_2221_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_2225_){
_start:
{
if (lean_obj_tag(v_x_2225_) == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(v_x_2225_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2227_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2227_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2244_; 
v_a_2236_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2238_ = v___x_2227_;
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2227_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2244_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2242_; 
v___x_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2240_, 0, v_a_2236_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2240_);
v___x_2242_ = v___x_2238_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(lean_object* v_j_2245_, lean_object* v_k_2246_){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = l_Lean_Json_getObjValD(v_j_2245_, v_k_2246_);
v___x_2248_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0(v___x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0___boxed(lean_object* v_j_2249_, lean_object* v_k_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(v_j_2249_, v_k_2250_);
lean_dec_ref(v_k_2250_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_2254_){
_start:
{
if (lean_obj_tag(v_x_2254_) == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_2255_;
}
else
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Lsp_instFromJsonCompletionOptions_fromJson(v_x_2254_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
else
{
lean_object* v_a_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2273_; 
v_a_2265_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2267_ = v___x_2256_;
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_a_2265_);
lean_dec(v___x_2256_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2273_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_a_2265_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 0, v___x_2269_);
v___x_2271_ = v___x_2267_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(lean_object* v_j_2274_, lean_object* v_k_2275_){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2276_ = l_Lean_Json_getObjValD(v_j_2274_, v_k_2275_);
v___x_2277_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1___boxed(lean_object* v_j_2278_, lean_object* v_k_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(v_j_2278_, v_k_2279_);
lean_dec_ref(v_k_2279_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7_spec__14(lean_object* v_x_2281_){
_start:
{
if (lean_obj_tag(v_x_2281_) == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Lsp_instFromJsonDocumentColorOptions_fromJson(v_x_2281_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2300_; 
v_a_2292_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2294_ = v___x_2283_;
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2283_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2296_, 0, v_a_2292_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v___x_2296_);
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(lean_object* v_j_2301_, lean_object* v_k_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = l_Lean_Json_getObjValD(v_j_2301_, v_k_2302_);
v___x_2304_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7_spec__14(v___x_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7___boxed(lean_object* v_j_2305_, lean_object* v_k_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(v_j_2305_, v_k_2306_);
lean_dec_ref(v_k_2306_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6(lean_object* v_x_2310_){
_start:
{
if (lean_obj_tag(v_x_2310_) == 0)
{
lean_object* v___x_2311_; 
v___x_2311_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6___closed__0));
return v___x_2311_;
}
else
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_Lsp_instFromJsonSemanticTokensOptions_fromJson(v_x_2310_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2329_; 
v_a_2321_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2323_ = v___x_2312_;
v_isShared_2324_ = v_isSharedCheck_2329_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2312_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2329_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
v___x_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_a_2321_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2325_);
v___x_2327_ = v___x_2323_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(lean_object* v_j_2330_, lean_object* v_k_2331_){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = l_Lean_Json_getObjValD(v_j_2330_, v_k_2331_);
v___x_2333_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6(v___x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3___boxed(lean_object* v_j_2334_, lean_object* v_k_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(v_j_2334_, v_k_2335_);
lean_dec_ref(v_k_2335_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2_spec__4(lean_object* v_x_2337_){
_start:
{
if (lean_obj_tag(v_x_2337_) == 0)
{
lean_object* v___x_2338_; 
v___x_2338_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_2338_;
}
else
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Lsp_instFromJsonRenameOptions_fromJson(v_x_2337_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2356_; 
v_a_2348_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2350_ = v___x_2339_;
v_isShared_2351_ = v_isSharedCheck_2356_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2339_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2356_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_a_2348_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2352_);
v___x_2354_ = v___x_2350_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(lean_object* v_j_2357_, lean_object* v_k_2358_){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = l_Lean_Json_getObjValD(v_j_2357_, v_k_2358_);
v___x_2360_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2_spec__4(v___x_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2___boxed(lean_object* v_j_2361_, lean_object* v_k_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(v_j_2361_, v_k_2362_);
lean_dec_ref(v_k_2362_);
return v_res_2363_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2369_ = 1;
v___x_2370_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1));
v___x_2371_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2370_, v___x_2369_);
return v___x_2371_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2372_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_2373_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2);
v___x_2374_ = lean_string_append(v___x_2373_, v___x_2372_);
return v___x_2374_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = 1;
v___x_2379_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__5));
v___x_2380_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2379_, v___x_2378_);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2381_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6);
v___x_2382_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2383_ = lean_string_append(v___x_2382_, v___x_2381_);
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2385_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7);
v___x_2386_ = lean_string_append(v___x_2385_, v___x_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2390_ = 1;
v___x_2391_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__10));
v___x_2392_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2391_, v___x_2390_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2393_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11);
v___x_2394_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2395_ = lean_string_append(v___x_2394_, v___x_2393_);
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2397_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12);
v___x_2398_ = lean_string_append(v___x_2397_, v___x_2396_);
return v___x_2398_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15(void){
_start:
{
uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = 1;
v___x_2402_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__14));
v___x_2403_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2402_, v___x_2401_);
return v___x_2403_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15);
v___x_2405_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2406_ = lean_string_append(v___x_2405_, v___x_2404_);
return v___x_2406_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2408_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16);
v___x_2409_ = lean_string_append(v___x_2408_, v___x_2407_);
return v___x_2409_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19(void){
_start:
{
uint8_t v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = 1;
v___x_2413_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__18));
v___x_2414_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2413_, v___x_2412_);
return v___x_2414_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19);
v___x_2416_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2417_ = lean_string_append(v___x_2416_, v___x_2415_);
return v___x_2417_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2418_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2419_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20);
v___x_2420_ = lean_string_append(v___x_2419_, v___x_2418_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23(void){
_start:
{
uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = 1;
v___x_2424_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__22));
v___x_2425_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2424_, v___x_2423_);
return v___x_2425_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24(void){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2426_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23);
v___x_2427_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2428_ = lean_string_append(v___x_2427_, v___x_2426_);
return v___x_2428_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2430_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24);
v___x_2431_ = lean_string_append(v___x_2430_, v___x_2429_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27(void){
_start:
{
uint8_t v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = 1;
v___x_2435_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__26));
v___x_2436_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2435_, v___x_2434_);
return v___x_2436_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2437_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27);
v___x_2438_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2439_ = lean_string_append(v___x_2438_, v___x_2437_);
return v___x_2439_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2441_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28);
v___x_2442_ = lean_string_append(v___x_2441_, v___x_2440_);
return v___x_2442_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31(void){
_start:
{
uint8_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = 1;
v___x_2446_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__30));
v___x_2447_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2446_, v___x_2445_);
return v___x_2447_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2448_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31);
v___x_2449_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2450_ = lean_string_append(v___x_2449_, v___x_2448_);
return v___x_2450_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2452_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32);
v___x_2453_ = lean_string_append(v___x_2452_, v___x_2451_);
return v___x_2453_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35(void){
_start:
{
uint8_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = 1;
v___x_2457_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__34));
v___x_2458_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2457_, v___x_2456_);
return v___x_2458_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35);
v___x_2460_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2461_ = lean_string_append(v___x_2460_, v___x_2459_);
return v___x_2461_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2463_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36);
v___x_2464_ = lean_string_append(v___x_2463_, v___x_2462_);
return v___x_2464_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39(void){
_start:
{
uint8_t v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = 1;
v___x_2468_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__38));
v___x_2469_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2468_, v___x_2467_);
return v___x_2469_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40(void){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39);
v___x_2471_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2472_ = lean_string_append(v___x_2471_, v___x_2470_);
return v___x_2472_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41(void){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2474_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40);
v___x_2475_ = lean_string_append(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43(void){
_start:
{
uint8_t v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = 1;
v___x_2479_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__42));
v___x_2480_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2479_, v___x_2478_);
return v___x_2480_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44(void){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43);
v___x_2482_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2483_ = lean_string_append(v___x_2482_, v___x_2481_);
return v___x_2483_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2485_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44);
v___x_2486_ = lean_string_append(v___x_2485_, v___x_2484_);
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48(void){
_start:
{
uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = 1;
v___x_2491_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__47));
v___x_2492_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2491_, v___x_2490_);
return v___x_2492_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49(void){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48);
v___x_2494_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2495_ = lean_string_append(v___x_2494_, v___x_2493_);
return v___x_2495_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2497_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49);
v___x_2498_ = lean_string_append(v___x_2497_, v___x_2496_);
return v___x_2498_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52(void){
_start:
{
uint8_t v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = 1;
v___x_2502_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__51));
v___x_2503_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2502_, v___x_2501_);
return v___x_2503_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53(void){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2504_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52);
v___x_2505_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2506_ = lean_string_append(v___x_2505_, v___x_2504_);
return v___x_2506_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2508_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53);
v___x_2509_ = lean_string_append(v___x_2508_, v___x_2507_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56(void){
_start:
{
uint8_t v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = 1;
v___x_2513_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__55));
v___x_2514_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2513_, v___x_2512_);
return v___x_2514_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56);
v___x_2516_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2517_ = lean_string_append(v___x_2516_, v___x_2515_);
return v___x_2517_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58(void){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2519_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57);
v___x_2520_ = lean_string_append(v___x_2519_, v___x_2518_);
return v___x_2520_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61(void){
_start:
{
uint8_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = 1;
v___x_2525_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__60));
v___x_2526_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2525_, v___x_2524_);
return v___x_2526_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61);
v___x_2528_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2529_ = lean_string_append(v___x_2528_, v___x_2527_);
return v___x_2529_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2531_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62);
v___x_2532_ = lean_string_append(v___x_2531_, v___x_2530_);
return v___x_2532_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66(void){
_start:
{
uint8_t v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = 1;
v___x_2537_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__65));
v___x_2538_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2537_, v___x_2536_);
return v___x_2538_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66);
v___x_2540_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2541_ = lean_string_append(v___x_2540_, v___x_2539_);
return v___x_2541_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2543_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67);
v___x_2544_ = lean_string_append(v___x_2543_, v___x_2542_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71(void){
_start:
{
uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = 1;
v___x_2549_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__70));
v___x_2550_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2549_, v___x_2548_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71);
v___x_2552_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2553_ = lean_string_append(v___x_2552_, v___x_2551_);
return v___x_2553_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2555_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72);
v___x_2556_ = lean_string_append(v___x_2555_, v___x_2554_);
return v___x_2556_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76(void){
_start:
{
uint8_t v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = 1;
v___x_2561_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__75));
v___x_2562_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2561_, v___x_2560_);
return v___x_2562_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76);
v___x_2564_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2565_ = lean_string_append(v___x_2564_, v___x_2563_);
return v___x_2565_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2567_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77);
v___x_2568_ = lean_string_append(v___x_2567_, v___x_2566_);
return v___x_2568_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81(void){
_start:
{
uint8_t v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = 1;
v___x_2573_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__80));
v___x_2574_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2573_, v___x_2572_);
return v___x_2574_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82(void){
_start:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2575_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81);
v___x_2576_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2577_ = lean_string_append(v___x_2576_, v___x_2575_);
return v___x_2577_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2579_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82);
v___x_2580_ = lean_string_append(v___x_2579_, v___x_2578_);
return v___x_2580_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86(void){
_start:
{
uint8_t v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = 1;
v___x_2585_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__85));
v___x_2586_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2585_, v___x_2584_);
return v___x_2586_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86);
v___x_2588_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2589_ = lean_string_append(v___x_2588_, v___x_2587_);
return v___x_2589_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2591_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87);
v___x_2592_ = lean_string_append(v___x_2591_, v___x_2590_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(lean_object* v_json_2593_){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0));
lean_inc(v_json_2593_);
v___x_2595_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(v_json_2593_, v___x_2594_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_json_2593_);
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2605_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v___x_2600_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8);
v___x_2601_ = lean_string_append(v___x_2600_, v_a_2596_);
lean_dec(v_a_2596_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v___x_2601_);
v___x_2603_ = v___x_2598_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
else
{
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v_json_2593_);
v_a_2606_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2595_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2595_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
lean_ctor_set_tag(v___x_2608_, 0);
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v_a_2614_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2615_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1));
lean_inc(v_json_2593_);
v___x_2616_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(v_json_2593_, v___x_2615_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2619_ = v___x_2616_;
v_isShared_2620_ = v_isSharedCheck_2626_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2626_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2624_; 
v___x_2621_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13);
v___x_2622_ = lean_string_append(v___x_2621_, v_a_2617_);
lean_dec(v_a_2617_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v___x_2622_);
v___x_2624_ = v___x_2619_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2627_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2616_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2616_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set_tag(v___x_2629_, 0);
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_a_2635_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2636_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2));
lean_inc(v_json_2593_);
v___x_2637_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2593_, v___x_2636_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2647_; 
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2640_ = v___x_2637_;
v_isShared_2641_ = v_isSharedCheck_2647_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2647_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2642_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17);
v___x_2643_ = lean_string_append(v___x_2642_, v_a_2638_);
lean_dec(v_a_2638_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 0, v___x_2643_);
v___x_2645_ = v___x_2640_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
else
{
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2648_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2637_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2637_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
lean_ctor_set_tag(v___x_2650_, 0);
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_a_2656_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2637_, 1);
v___x_2657_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3));
lean_inc(v_json_2593_);
v___x_2658_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2593_, v___x_2657_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2668_; 
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2668_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2668_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2666_; 
v___x_2663_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21);
v___x_2664_ = lean_string_append(v___x_2663_, v_a_2659_);
lean_dec(v_a_2659_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2664_);
v___x_2666_ = v___x_2661_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
else
{
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2669_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2658_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2658_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set_tag(v___x_2671_, 0);
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_a_2677_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2678_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4));
lean_inc(v_json_2593_);
v___x_2679_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2593_, v___x_2678_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2689_; 
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2682_ = v___x_2679_;
v_isShared_2683_ = v_isSharedCheck_2689_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2679_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2689_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2684_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25);
v___x_2685_ = lean_string_append(v___x_2684_, v_a_2680_);
lean_dec(v_a_2680_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v___x_2685_);
v___x_2687_ = v___x_2682_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
else
{
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2690_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2679_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2679_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
lean_ctor_set_tag(v___x_2692_, 0);
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
else
{
lean_object* v_a_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_a_2698_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2679_, 1);
v___x_2699_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5));
lean_inc(v_json_2593_);
v___x_2700_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2593_, v___x_2699_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2710_; 
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2703_ = v___x_2700_;
v_isShared_2704_ = v_isSharedCheck_2710_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2700_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2710_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
v___x_2705_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29);
v___x_2706_ = lean_string_append(v___x_2705_, v_a_2701_);
lean_dec(v_a_2701_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2706_);
v___x_2708_ = v___x_2703_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
else
{
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2711_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2700_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2700_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
lean_ctor_set_tag(v___x_2713_, 0);
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
else
{
lean_object* v_a_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v_a_2719_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2700_, 1);
v___x_2720_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6));
lean_inc(v_json_2593_);
v___x_2721_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2593_, v___x_2720_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2731_; 
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2731_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2731_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2726_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33);
v___x_2727_ = lean_string_append(v___x_2726_, v_a_2722_);
lean_dec(v_a_2722_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2727_);
v___x_2729_ = v___x_2724_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
else
{
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2732_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2721_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2721_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set_tag(v___x_2734_, 0);
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v_a_2740_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2721_, 1);
v___x_2741_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7));
lean_inc(v_json_2593_);
v___x_2742_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2593_, v___x_2741_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2752_; 
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2745_ = v___x_2742_;
v_isShared_2746_ = v_isSharedCheck_2752_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2742_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2752_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2747_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37);
v___x_2748_ = lean_string_append(v___x_2747_, v_a_2743_);
lean_dec(v_a_2743_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2748_);
v___x_2750_ = v___x_2745_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
else
{
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2753_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2742_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2742_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
lean_ctor_set_tag(v___x_2755_, 0);
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v_a_2761_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2742_, 1);
v___x_2762_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8));
lean_inc(v_json_2593_);
v___x_2763_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2593_, v___x_2762_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2773_; 
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2766_ = v___x_2763_;
v_isShared_2767_ = v_isSharedCheck_2773_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2763_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2773_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2771_; 
v___x_2768_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41);
v___x_2769_ = lean_string_append(v___x_2768_, v_a_2764_);
lean_dec(v_a_2764_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2769_);
v___x_2771_ = v___x_2766_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2769_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
else
{
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2774_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2763_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2763_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
lean_ctor_set_tag(v___x_2776_, 0);
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
v_a_2782_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2763_, 1);
v___x_2783_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9));
lean_inc(v_json_2593_);
v___x_2784_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2593_, v___x_2783_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2794_; 
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2794_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2794_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2789_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45);
v___x_2790_ = lean_string_append(v___x_2789_, v_a_2785_);
lean_dec(v_a_2785_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2790_);
v___x_2792_ = v___x_2787_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2790_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
else
{
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2795_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2784_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2784_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
lean_ctor_set_tag(v___x_2797_, 0);
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_a_2803_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2804_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10));
lean_inc(v_json_2593_);
v___x_2805_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(v_json_2593_, v___x_2804_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2808_ = v___x_2805_;
v_isShared_2809_ = v_isSharedCheck_2815_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2815_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2810_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50);
v___x_2811_ = lean_string_append(v___x_2810_, v_a_2806_);
lean_dec(v_a_2806_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2811_);
v___x_2813_ = v___x_2808_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2816_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2805_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2805_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
lean_ctor_set_tag(v___x_2818_, 0);
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_a_2824_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2825_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11));
lean_inc(v_json_2593_);
v___x_2826_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2593_, v___x_2825_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2836_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2836_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2831_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54);
v___x_2832_ = lean_string_append(v___x_2831_, v_a_2827_);
lean_dec(v_a_2827_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2832_);
v___x_2834_ = v___x_2829_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
else
{
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2837_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2826_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2826_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set_tag(v___x_2839_, 0);
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v_a_2845_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2826_, 1);
v___x_2846_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12));
lean_inc(v_json_2593_);
v___x_2847_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2593_, v___x_2846_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2857_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2857_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2852_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58);
v___x_2853_ = lean_string_append(v___x_2852_, v_a_2848_);
lean_dec(v_a_2848_);
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 0, v___x_2853_);
v___x_2855_ = v___x_2850_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2853_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
else
{
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2858_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2847_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2847_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
lean_ctor_set_tag(v___x_2860_, 0);
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v_a_2866_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2847_, 1);
v___x_2867_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13));
lean_inc(v_json_2593_);
v___x_2868_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(v_json_2593_, v___x_2867_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2878_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2878_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2873_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63);
v___x_2874_ = lean_string_append(v___x_2873_, v_a_2869_);
lean_dec(v_a_2869_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2874_);
v___x_2876_ = v___x_2871_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
else
{
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2879_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2868_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2868_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 0);
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; 
v_a_2887_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2888_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14));
lean_inc(v_json_2593_);
v___x_2889_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(v_json_2593_, v___x_2888_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_a_2887_);
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_2899_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2899_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2894_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68);
v___x_2895_ = lean_string_append(v___x_2894_, v_a_2890_);
lean_dec(v_a_2890_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2895_);
v___x_2897_ = v___x_2892_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
else
{
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_a_2887_);
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2900_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2889_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2889_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set_tag(v___x_2902_, 0);
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; 
v_a_2908_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2889_, 1);
v___x_2909_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15));
lean_inc(v_json_2593_);
v___x_2910_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(v_json_2593_, v___x_2909_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v_a_2908_);
lean_dec(v_a_2887_);
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2920_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2920_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2915_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73);
v___x_2916_ = lean_string_append(v___x_2915_, v_a_2911_);
lean_dec(v_a_2911_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2916_);
v___x_2918_ = v___x_2913_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_a_2908_);
lean_dec(v_a_2887_);
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2921_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2910_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2910_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set_tag(v___x_2923_, 0);
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v_a_2929_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2910_, 1);
v___x_2930_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16));
lean_inc(v_json_2593_);
v___x_2931_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(v_json_2593_, v___x_2930_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v_a_2929_);
lean_dec(v_a_2908_);
lean_dec(v_a_2887_);
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2934_ = v___x_2931_;
v_isShared_2935_ = v_isSharedCheck_2941_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2941_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2936_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78);
v___x_2937_ = lean_string_append(v___x_2936_, v_a_2932_);
lean_dec(v_a_2932_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set(v___x_2934_, 0, v___x_2937_);
v___x_2939_ = v___x_2934_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
else
{
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_dec(v_a_2929_);
lean_dec(v_a_2908_);
lean_dec(v_a_2887_);
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2942_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2931_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2931_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
lean_ctor_set_tag(v___x_2944_, 0);
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_a_2950_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2931_, 1);
v___x_2951_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17));
lean_inc(v_json_2593_);
v___x_2952_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(v_json_2593_, v___x_2951_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v_a_2950_);
lean_dec(v_a_2929_);
lean_dec(v_a_2908_);
lean_dec(v_a_2887_);
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2962_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2962_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2960_; 
v___x_2957_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83);
v___x_2958_ = lean_string_append(v___x_2957_, v_a_2953_);
lean_dec(v_a_2953_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 0, v___x_2958_);
v___x_2960_ = v___x_2955_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
else
{
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec(v_a_2950_);
lean_dec(v_a_2929_);
lean_dec(v_a_2908_);
lean_dec(v_a_2887_);
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
lean_dec(v_json_2593_);
v_a_2963_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2952_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2952_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set_tag(v___x_2965_, 0);
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_a_2971_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2971_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2972_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18));
v___x_2973_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(v_json_2593_, v___x_2972_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2983_; 
lean_dec(v_a_2971_);
lean_dec(v_a_2950_);
lean_dec(v_a_2929_);
lean_dec(v_a_2908_);
lean_dec(v_a_2887_);
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_2983_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2983_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2978_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88);
v___x_2979_ = lean_string_append(v___x_2978_, v_a_2974_);
lean_dec(v_a_2974_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___x_2979_);
v___x_2981_ = v___x_2976_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2979_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
else
{
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec(v_a_2971_);
lean_dec(v_a_2950_);
lean_dec(v_a_2929_);
lean_dec(v_a_2908_);
lean_dec(v_a_2887_);
lean_dec(v_a_2866_);
lean_dec(v_a_2845_);
lean_dec(v_a_2824_);
lean_dec(v_a_2803_);
lean_dec(v_a_2782_);
lean_dec(v_a_2761_);
lean_dec(v_a_2740_);
lean_dec(v_a_2719_);
lean_dec(v_a_2698_);
lean_dec(v_a_2677_);
lean_dec(v_a_2656_);
lean_dec(v_a_2635_);
lean_dec(v_a_2614_);
v_a_2984_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2973_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2973_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 0);
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3010_; 
v_a_2992_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2994_ = v___x_2973_;
v_isShared_2995_ = v_isSharedCheck_3010_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2973_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3010_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; uint8_t v___x_2997_; uint8_t v___x_2998_; uint8_t v___x_2999_; uint8_t v___x_3000_; uint8_t v___x_3001_; uint8_t v___x_3002_; uint8_t v___x_3003_; uint8_t v___x_3004_; uint8_t v___x_3005_; uint8_t v___x_3006_; lean_object* v___x_3008_; 
v___x_2996_ = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(v___x_2996_, 0, v_a_2614_);
lean_ctor_set(v___x_2996_, 1, v_a_2635_);
lean_ctor_set(v___x_2996_, 2, v_a_2824_);
lean_ctor_set(v___x_2996_, 3, v_a_2887_);
lean_ctor_set(v___x_2996_, 4, v_a_2908_);
lean_ctor_set(v___x_2996_, 5, v_a_2929_);
lean_ctor_set(v___x_2996_, 6, v_a_2950_);
lean_ctor_set(v___x_2996_, 7, v_a_2971_);
lean_ctor_set(v___x_2996_, 8, v_a_2992_);
v___x_2997_ = lean_unbox(v_a_2656_);
lean_dec(v_a_2656_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*9, v___x_2997_);
v___x_2998_ = lean_unbox(v_a_2677_);
lean_dec(v_a_2677_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*9 + 1, v___x_2998_);
v___x_2999_ = lean_unbox(v_a_2698_);
lean_dec(v_a_2698_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*9 + 2, v___x_2999_);
v___x_3000_ = lean_unbox(v_a_2719_);
lean_dec(v_a_2719_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*9 + 3, v___x_3000_);
v___x_3001_ = lean_unbox(v_a_2740_);
lean_dec(v_a_2740_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*9 + 4, v___x_3001_);
v___x_3002_ = lean_unbox(v_a_2761_);
lean_dec(v_a_2761_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*9 + 5, v___x_3002_);
v___x_3003_ = lean_unbox(v_a_2782_);
lean_dec(v_a_2782_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*9 + 6, v___x_3003_);
v___x_3004_ = lean_unbox(v_a_2803_);
lean_dec(v_a_2803_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*9 + 7, v___x_3004_);
v___x_3005_ = lean_unbox(v_a_2845_);
lean_dec(v_a_2845_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*9 + 8, v___x_3005_);
v___x_3006_ = lean_unbox(v_a_2866_);
lean_dec(v_a_2866_);
lean_ctor_set_uint8(v___x_2996_, sizeof(void*)*9 + 9, v___x_3006_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_2996_);
v___x_3008_ = v___x_2994_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_2996_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
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

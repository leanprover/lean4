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
lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(uint8_t v_x_489_){
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
LEAN_EXPORT void l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_489_ = stack[0].m_num;
lean_object* v_res_499_;
v_res_499_ = l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(v_x_489_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___boxed(lean_object* v_x_500_){
_start:
{
uint8_t v_x_29__boxed_501_; lean_object* v_res_502_; 
v_x_29__boxed_501_ = lean_unbox(v_x_500_);
v_res_502_ = l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(v_x_29__boxed_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(lean_object* v_j_505_, lean_object* v_k_506_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = l_Lean_Json_getObjValD(v_j_505_, v_k_506_);
v___x_508_ = l_Lean_Json_getBool_x3f(v___x_507_);
lean_dec(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_509_, lean_object* v_k_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_j_509_, v_k_510_);
lean_dec_ref(v_k_510_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_517_ = 1;
v___x_518_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__1));
v___x_519_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_518_, v___x_517_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_521_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__2);
v___x_522_ = lean_string_append(v___x_521_, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5(void){
_start:
{
uint8_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = 1;
v___x_526_ = ((lean_object*)(l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__4));
v___x_527_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_526_, v___x_525_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__5);
v___x_529_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__3);
v___x_530_ = lean_string_append(v___x_529_, v___x_528_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_532_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__6);
v___x_533_ = lean_string_append(v___x_532_, v___x_531_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson(lean_object* v_json_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson___closed__0));
v___x_536_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_534_, v___x_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_546_; 
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_546_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_546_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_541_ = lean_obj_once(&l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson___closed__7);
v___x_542_ = lean_string_append(v___x_541_, v_a_537_);
lean_dec(v_a_537_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
else
{
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_536_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_536_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 0);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v_a_555_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_536_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_536_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(lean_object* v_k_565_, lean_object* v_x_566_){
_start:
{
if (lean_obj_tag(v_x_566_) == 0)
{
lean_object* v___x_567_; 
lean_dec_ref(v_k_565_);
v___x_567_ = lean_box(0);
return v___x_567_;
}
else
{
lean_object* v_val_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v_val_568_ = lean_ctor_get(v_x_566_, 0);
v___x_569_ = lean_unbox(v_val_568_);
v___x_570_ = l_Lean_Lsp_instToJsonShowDocumentClientCapabilities_toJson(v___x_569_);
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_k_565_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_571_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_574_, lean_object* v_x_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(v_k_574_, v_x_575_);
lean_dec(v_x_575_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(lean_object* v_x_578_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_579_ = ((lean_object*)(l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0));
v___x_580_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWindowClientCapabilities_toJson_spec__0(v___x_579_, v_x_578_);
v___x_581_ = lean_box(0);
v___x_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_584_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_582_, v___x_583_);
v___x_585_ = l_Lean_Json_mkObj(v___x_584_);
lean_dec(v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___boxed(lean_object* v_x_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(v_x_586_);
lean_dec(v_x_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_590_){
_start:
{
if (lean_obj_tag(v_x_590_) == 0)
{
lean_object* v___x_591_; 
v___x_591_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_591_;
}
else
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson(v_x_590_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_592_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_609_; 
v_a_601_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_609_ == 0)
{
v___x_603_ = v___x_592_;
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_592_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_609_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v_a_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_605_);
v___x_607_ = v___x_603_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(lean_object* v_j_610_, lean_object* v_k_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = l_Lean_Json_getObjValD(v_j_610_, v_k_611_);
v___x_613_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0_spec__0(v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_614_, lean_object* v_k_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(v_j_614_, v_k_615_);
lean_dec_ref(v_k_615_);
return v_res_616_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = 1;
v___x_623_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__1));
v___x_624_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_623_, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_626_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__2);
v___x_627_ = lean_string_append(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = 1;
v___x_632_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__5));
v___x_633_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__6);
v___x_635_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__3);
v___x_636_ = lean_string_append(v___x_635_, v___x_634_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_637_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_638_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__7);
v___x_639_ = lean_string_append(v___x_638_, v___x_637_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson(lean_object* v_json_640_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson___closed__0));
v___x_642_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson_spec__0(v_json_640_, v___x_641_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_652_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_652_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_652_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_647_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson___closed__8);
v___x_648_ = lean_string_append(v___x_647_, v_a_643_);
lean_dec(v_a_643_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v___x_648_);
v___x_650_ = v___x_645_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
v_a_653_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_642_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_642_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set_tag(v___x_655_, 0);
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_642_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_642_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(lean_object* v_x_672_){
_start:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_673_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0));
v___x_674_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_673_, v_x_672_);
v___x_675_ = lean_box(0);
v___x_676_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_678_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_676_, v___x_677_);
v___x_679_ = l_Lean_Json_mkObj(v___x_678_);
lean_dec(v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___boxed(lean_object* v_x_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(v_x_680_);
lean_dec(v_x_680_);
return v_res_681_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2(void){
_start:
{
uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = 1;
v___x_690_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__1));
v___x_691_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_690_, v___x_689_);
return v___x_691_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_692_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_693_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__2);
v___x_694_ = lean_string_append(v___x_693_, v___x_692_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6(void){
_start:
{
uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_698_ = 1;
v___x_699_ = ((lean_object*)(l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__5));
v___x_700_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_699_, v___x_698_);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_701_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__6);
v___x_702_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__3);
v___x_703_ = lean_string_append(v___x_702_, v___x_701_);
return v___x_703_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_705_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__7);
v___x_706_ = lean_string_append(v___x_705_, v___x_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson(lean_object* v_json_707_){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson___closed__0));
v___x_709_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_707_, v___x_708_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_719_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_719_ == 0)
{
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_719_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = lean_obj_once(&l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8, &l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson___closed__8);
v___x_715_ = lean_string_append(v___x_714_, v_a_710_);
lean_dec(v_a_710_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_715_);
v___x_717_ = v___x_712_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
v_a_720_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_709_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_709_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 0);
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_709_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_709_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(lean_object* v_k_738_, lean_object* v_x_739_){
_start:
{
if (lean_obj_tag(v_x_739_) == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v_k_738_);
v___x_740_ = lean_box(0);
return v___x_740_;
}
else
{
lean_object* v_val_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v_val_741_ = lean_ctor_get(v_x_739_, 0);
v___x_742_ = l_Lean_Lsp_instToJsonChangeAnnotationSupport_toJson(v_val_741_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v_k_738_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v___x_744_ = lean_box(0);
v___x_745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_743_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_746_, lean_object* v_x_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(v_k_746_, v_x_747_);
lean_dec(v_x_747_);
return v_res_748_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(size_t v_sz_749_, size_t v_i_750_, lean_object* v_bs_751_){
_start:
{
uint8_t v___x_752_; 
v___x_752_ = lean_usize_dec_lt(v_i_750_, v_sz_749_);
if (v___x_752_ == 0)
{
return v_bs_751_;
}
else
{
lean_object* v_v_753_; lean_object* v___x_754_; lean_object* v_bs_x27_755_; lean_object* v___x_756_; size_t v___x_757_; size_t v___x_758_; lean_object* v___x_759_; 
v_v_753_ = lean_array_uget(v_bs_751_, v_i_750_);
v___x_754_ = lean_unsigned_to_nat(0u);
v_bs_x27_755_ = lean_array_uset(v_bs_751_, v_i_750_, v___x_754_);
v___x_756_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_756_, 0, v_v_753_);
v___x_757_ = ((size_t)1ULL);
v___x_758_ = lean_usize_add(v_i_750_, v___x_757_);
v___x_759_ = lean_array_uset(v_bs_x27_755_, v_i_750_, v___x_756_);
v_i_750_ = v___x_758_;
v_bs_751_ = v___x_759_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_749_ = stack[0].m_num;
size_t v_i_750_ = stack[1].m_num;
lean_object* v_bs_751_ = stack[2].m_obj;
lean_object* v_res_761_;
v_res_761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(v_sz_749_, v_i_750_, v_bs_751_);
stack->m_obj
 = v_res_761_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2___boxed(lean_object* v_sz_762_, lean_object* v_i_763_, lean_object* v_bs_764_){
_start:
{
size_t v_sz_boxed_765_; size_t v_i_boxed_766_; lean_object* v_res_767_; 
v_sz_boxed_765_ = lean_unbox_usize(v_sz_762_);
lean_dec(v_sz_762_);
v_i_boxed_766_ = lean_unbox_usize(v_i_763_);
lean_dec(v_i_763_);
v_res_767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(v_sz_boxed_765_, v_i_boxed_766_, v_bs_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1(lean_object* v_a_768_){
_start:
{
size_t v_sz_769_; size_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_sz_769_ = lean_array_size(v_a_768_);
v___x_770_ = ((size_t)0ULL);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1_spec__2(v_sz_769_, v___x_770_, v_a_768_);
v___x_772_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1(lean_object* v_k_773_, lean_object* v_x_774_){
_start:
{
if (lean_obj_tag(v_x_774_) == 0)
{
lean_object* v___x_775_; 
lean_dec_ref(v_k_773_);
v___x_775_ = lean_box(0);
return v___x_775_;
}
else
{
lean_object* v_val_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v_val_776_ = lean_ctor_get(v_x_774_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v_x_774_, 1);
v___x_777_ = l_Lean_Array_toJson___at___00Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1_spec__1(v_val_776_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_k_773_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_778_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
return v___x_780_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson(lean_object* v_x_784_){
_start:
{
lean_object* v_documentChanges_x3f_785_; lean_object* v_changeAnnotationSupport_x3f_786_; lean_object* v_resourceOperations_x3f_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_documentChanges_x3f_785_ = lean_ctor_get(v_x_784_, 0);
lean_inc(v_documentChanges_x3f_785_);
v_changeAnnotationSupport_x3f_786_ = lean_ctor_get(v_x_784_, 1);
lean_inc(v_changeAnnotationSupport_x3f_786_);
v_resourceOperations_x3f_787_ = lean_ctor_get(v_x_784_, 2);
lean_inc(v_resourceOperations_x3f_787_);
lean_dec_ref(v_x_784_);
v___x_788_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0));
v___x_789_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_788_, v_documentChanges_x3f_785_);
lean_dec(v_documentChanges_x3f_785_);
v___x_790_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1));
v___x_791_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__0(v___x_790_, v_changeAnnotationSupport_x3f_786_);
lean_dec(v_changeAnnotationSupport_x3f_786_);
v___x_792_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2));
v___x_793_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson_spec__1(v___x_792_, v_resourceOperations_x3f_787_);
v___x_794_ = lean_box(0);
v___x_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_791_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_789_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_799_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_797_, v___x_798_);
v___x_800_ = l_Lean_Json_mkObj(v___x_799_);
lean_dec(v___x_799_);
return v___x_800_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(size_t v_sz_803_, size_t v_i_804_, lean_object* v_bs_805_){
_start:
{
uint8_t v___x_806_; 
v___x_806_ = lean_usize_dec_lt(v_i_804_, v_sz_803_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; 
v___x_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_807_, 0, v_bs_805_);
return v___x_807_;
}
else
{
lean_object* v_v_808_; lean_object* v___x_809_; 
v_v_808_ = lean_array_uget_borrowed(v_bs_805_, v_i_804_);
lean_inc(v_v_808_);
v___x_809_ = l_Lean_Json_getStr_x3f(v_v_808_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_bs_805_);
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_819_; lean_object* v_bs_x27_820_; size_t v___x_821_; size_t v___x_822_; lean_object* v___x_823_; 
v_a_818_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_809_, 1);
v___x_819_ = lean_unsigned_to_nat(0u);
v_bs_x27_820_ = lean_array_uset(v_bs_805_, v_i_804_, v___x_819_);
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_add(v_i_804_, v___x_821_);
v___x_823_ = lean_array_uset(v_bs_x27_820_, v_i_804_, v_a_818_);
v_i_804_ = v___x_822_;
v_bs_805_ = v___x_823_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_803_ = stack[0].m_num;
size_t v_i_804_ = stack[1].m_num;
lean_object* v_bs_805_ = stack[2].m_obj;
lean_object* v_res_825_;
v_res_825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(v_sz_803_, v_i_804_, v_bs_805_);
stack->m_obj
 = v_res_825_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_826_, lean_object* v_i_827_, lean_object* v_bs_828_){
_start:
{
size_t v_sz_boxed_829_; size_t v_i_boxed_830_; lean_object* v_res_831_; 
v_sz_boxed_829_ = lean_unbox_usize(v_sz_826_);
lean_dec(v_sz_826_);
v_i_boxed_830_ = lean_unbox_usize(v_i_827_);
lean_dec(v_i_827_);
v_res_831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(v_sz_boxed_829_, v_i_boxed_830_, v_bs_828_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3(lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_834_) == 4)
{
lean_object* v_elems_835_; size_t v_sz_836_; size_t v___x_837_; lean_object* v___x_838_; 
v_elems_835_ = lean_ctor_get(v_x_834_, 0);
lean_inc_ref(v_elems_835_);
lean_dec_ref_known(v_x_834_, 1);
v_sz_836_ = lean_array_size(v_elems_835_);
v___x_837_ = ((size_t)0ULL);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3_spec__4(v_sz_836_, v___x_837_, v_elems_835_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_839_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__0));
v___x_840_ = lean_unsigned_to_nat(80u);
v___x_841_ = l_Lean_Json_pretty(v_x_834_, v___x_840_);
v___x_842_ = lean_string_append(v___x_839_, v___x_841_);
lean_dec_ref(v___x_841_);
v___x_843_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3___closed__1));
v___x_844_ = lean_string_append(v___x_842_, v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_848_){
_start:
{
if (lean_obj_tag(v_x_848_) == 0)
{
lean_object* v___x_849_; 
v___x_849_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_849_;
}
else
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2_spec__3(v_x_848_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_867_; 
v_a_859_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_867_ == 0)
{
v___x_861_ = v___x_850_;
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_850_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_865_; 
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_a_859_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_863_);
v___x_865_ = v___x_861_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(lean_object* v_j_868_, lean_object* v_k_869_){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = l_Lean_Json_getObjValD(v_j_868_, v_k_869_);
v___x_871_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1_spec__2(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1___boxed(lean_object* v_j_872_, lean_object* v_k_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(v_j_872_, v_k_873_);
lean_dec_ref(v_k_873_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_875_){
_start:
{
if (lean_obj_tag(v_x_875_) == 0)
{
lean_object* v___x_876_; 
v___x_876_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_876_;
}
else
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_Lsp_instFromJsonChangeAnnotationSupport_fromJson(v_x_875_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_894_; 
v_a_886_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_894_ == 0)
{
v___x_888_ = v___x_877_;
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_877_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(lean_object* v_j_895_, lean_object* v_k_896_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = l_Lean_Json_getObjValD(v_j_895_, v_k_896_);
v___x_898_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0_spec__0(v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_899_, lean_object* v_k_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(v_j_899_, v_k_900_);
lean_dec_ref(v_k_900_);
return v_res_901_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = 1;
v___x_908_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__1));
v___x_909_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_908_, v___x_907_);
return v___x_909_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_911_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__2);
v___x_912_ = lean_string_append(v___x_911_, v___x_910_);
return v___x_912_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = 1;
v___x_917_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__5));
v___x_918_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_919_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__6);
v___x_920_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3);
v___x_921_ = lean_string_append(v___x_920_, v___x_919_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_923_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__7);
v___x_924_ = lean_string_append(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = 1;
v___x_929_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__10));
v___x_930_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_929_, v___x_928_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__11);
v___x_932_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3);
v___x_933_ = lean_string_append(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_935_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__12);
v___x_936_ = lean_string_append(v___x_935_, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = 1;
v___x_941_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__15));
v___x_942_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_941_, v___x_940_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__16);
v___x_944_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__3);
v___x_945_ = lean_string_append(v___x_944_, v___x_943_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_947_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__17);
v___x_948_ = lean_string_append(v___x_947_, v___x_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson(lean_object* v_json_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__0));
lean_inc(v_json_949_);
v___x_951_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_949_, v___x_950_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_json_949_);
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_961_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_961_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_961_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_959_; 
v___x_956_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__8);
v___x_957_ = lean_string_append(v___x_956_, v_a_952_);
lean_dec(v_a_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_957_);
v___x_959_ = v___x_954_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v_json_949_);
v_a_962_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_951_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_951_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 0);
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_a_970_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_951_, 1);
v___x_971_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__1));
lean_inc(v_json_949_);
v___x_972_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__0(v_json_949_, v___x_971_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_a_970_);
lean_dec(v_json_949_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_982_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_982_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_982_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_977_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__13);
v___x_978_ = lean_string_append(v___x_977_, v_a_973_);
lean_dec(v_a_973_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_978_);
v___x_980_ = v___x_975_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
else
{
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec(v_a_970_);
lean_dec(v_json_949_);
v_a_983_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_972_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_972_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set_tag(v___x_985_, 0);
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v_a_991_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_972_, 1);
v___x_992_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson___closed__2));
v___x_993_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson_spec__1(v_json_949_, v___x_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1003_; 
lean_dec(v_a_991_);
lean_dec(v_a_970_);
v_a_994_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_996_ = v___x_993_;
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1003_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1001_; 
v___x_998_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson___closed__18);
v___x_999_ = lean_string_append(v___x_998_, v_a_994_);
lean_dec(v_a_994_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_999_);
v___x_1001_ = v___x_996_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
else
{
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_a_991_);
lean_dec(v_a_970_);
v_a_1004_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_993_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_993_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set_tag(v___x_1006_, 0);
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1020_; 
v_a_1012_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1014_ = v___x_993_;
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_993_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1020_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1016_, 0, v_a_970_);
lean_ctor_set(v___x_1016_, 1, v_a_991_);
lean_ctor_set(v___x_1016_, 2, v_a_1012_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1016_);
v___x_1018_ = v___x_1014_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson_spec__0(lean_object* v_k_1023_, lean_object* v_x_1024_){
_start:
{
if (lean_obj_tag(v_x_1024_) == 0)
{
lean_object* v___x_1025_; 
lean_dec_ref(v_k_1023_);
v___x_1025_ = lean_box(0);
return v___x_1025_;
}
else
{
lean_object* v_val_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_val_1026_ = lean_ctor_get(v_x_1024_, 0);
lean_inc(v_val_1026_);
lean_dec_ref_known(v_x_1024_, 1);
v___x_1027_ = l_Lean_Lsp_instToJsonWorkspaceEditClientCapabilities_toJson(v_val_1026_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v_k_1023_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_box(0);
v___x_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson(lean_object* v_x_1033_){
_start:
{
lean_object* v_applyEdit_x3f_1034_; lean_object* v_workspaceEdit_x3f_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1051_; 
v_applyEdit_x3f_1034_ = lean_ctor_get(v_x_1033_, 0);
v_workspaceEdit_x3f_1035_ = lean_ctor_get(v_x_1033_, 1);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_x_1033_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1037_ = v_x_1033_;
v_isShared_1038_ = v_isSharedCheck_1051_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_workspaceEdit_x3f_1035_);
lean_inc(v_applyEdit_x3f_1034_);
lean_dec(v_x_1033_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1051_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1039_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0));
v___x_1040_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_1039_, v_applyEdit_x3f_1034_);
lean_dec(v_applyEdit_x3f_1034_);
v___x_1041_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1));
v___x_1042_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson_spec__0(v___x_1041_, v_workspaceEdit_x3f_1035_);
v___x_1043_ = lean_box(0);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 1);
lean_ctor_set(v___x_1037_, 1, v___x_1043_);
lean_ctor_set(v___x_1037_, 0, v___x_1042_);
v___x_1045_ = v___x_1037_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1040_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1048_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1046_, v___x_1047_);
v___x_1049_ = l_Lean_Json_mkObj(v___x_1048_);
lean_dec(v___x_1048_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1056_){
_start:
{
if (lean_obj_tag(v_x_1056_) == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Lsp_instFromJsonWorkspaceEditClientCapabilities_fromJson(v_x_1056_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1058_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1075_; 
v_a_1067_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1075_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1069_ = v___x_1058_;
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1058_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1075_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_a_1067_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1071_);
v___x_1073_ = v___x_1069_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(lean_object* v_j_1076_, lean_object* v_k_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = l_Lean_Json_getObjValD(v_j_1076_, v_k_1077_);
v___x_1079_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0_spec__0(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1080_, lean_object* v_k_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(v_j_1080_, v_k_1081_);
lean_dec_ref(v_k_1081_);
return v_res_1082_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1088_ = 1;
v___x_1089_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__1));
v___x_1090_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1089_, v___x_1088_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1092_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__2);
v___x_1093_ = lean_string_append(v___x_1092_, v___x_1091_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = 1;
v___x_1098_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__5));
v___x_1099_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1098_, v___x_1097_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__6);
v___x_1101_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3);
v___x_1102_ = lean_string_append(v___x_1101_, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1104_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__7);
v___x_1105_ = lean_string_append(v___x_1104_, v___x_1103_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = 1;
v___x_1110_ = ((lean_object*)(l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__10));
v___x_1111_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__11);
v___x_1113_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__3);
v___x_1114_ = lean_string_append(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1116_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__12);
v___x_1117_ = lean_string_append(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson(lean_object* v_json_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__0));
lean_inc(v_json_1118_);
v___x_1120_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_1118_, v___x_1119_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_json_1118_);
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1123_ = v___x_1120_;
v_isShared_1124_ = v_isSharedCheck_1130_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1120_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1130_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1125_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__8);
v___x_1126_ = lean_string_append(v___x_1125_, v_a_1121_);
lean_dec(v_a_1121_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 0, v___x_1126_);
v___x_1128_ = v___x_1123_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
else
{
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_json_1118_);
v_a_1131_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1120_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1120_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_a_1139_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1140_ = ((lean_object*)(l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson___closed__1));
v___x_1141_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson_spec__0(v_json_1118_, v___x_1140_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1151_; 
lean_dec(v_a_1139_);
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1151_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1151_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1146_ = lean_obj_once(&l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson___closed__13);
v___x_1147_ = lean_string_append(v___x_1146_, v_a_1142_);
lean_dec(v_a_1142_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1147_);
v___x_1149_ = v___x_1144_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
}
else
{
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_a_1139_);
v_a_1152_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1141_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1141_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 0);
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
v_a_1160_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1162_ = v___x_1141_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1141_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v_a_1139_);
lean_ctor_set(v___x_1164_, 1, v_a_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(lean_object* v_k_1171_, lean_object* v_x_1172_){
_start:
{
if (lean_obj_tag(v_x_1172_) == 0)
{
lean_object* v___x_1173_; 
lean_dec_ref(v_k_1171_);
v___x_1173_ = lean_box(0);
return v___x_1173_;
}
else
{
lean_object* v_val_1174_; uint8_t v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v_val_1174_ = lean_ctor_get(v_x_1172_, 0);
v___x_1175_ = lean_unbox(v_val_1174_);
v___x_1176_ = l_Lean_Lsp_instToJsonRpcWireFormat_toJson(v___x_1175_);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v_k_1171_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1178_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0___boxed(lean_object* v_k_1180_, lean_object* v_x_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(v_k_1180_, v_x_1181_);
lean_dec(v_x_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(lean_object* v_x_1186_){
_start:
{
lean_object* v_incrementalDiagnosticSupport_x3f_1187_; lean_object* v_silentDiagnosticSupport_x3f_1188_; lean_object* v_rpcWireFormat_x3f_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_incrementalDiagnosticSupport_x3f_1187_ = lean_ctor_get(v_x_1186_, 0);
v_silentDiagnosticSupport_x3f_1188_ = lean_ctor_get(v_x_1186_, 1);
v_rpcWireFormat_x3f_1189_ = lean_ctor_get(v_x_1186_, 2);
v___x_1190_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0));
v___x_1191_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_1190_, v_incrementalDiagnosticSupport_x3f_1187_);
v___x_1192_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1));
v___x_1193_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__0(v___x_1192_, v_silentDiagnosticSupport_x3f_1188_);
v___x_1194_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2));
v___x_1195_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanClientCapabilities_toJson_spec__0(v___x_1194_, v_rpcWireFormat_x3f_1189_);
v___x_1196_ = lean_box(0);
v___x_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1193_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1191_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1201_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1199_, v___x_1200_);
v___x_1202_ = l_Lean_Json_mkObj(v___x_1201_);
lean_dec(v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___boxed(lean_object* v_x_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(v_x_1203_);
lean_dec_ref(v_x_1203_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1209_){
_start:
{
if (lean_obj_tag(v_x_1209_) == 0)
{
lean_object* v___x_1210_; 
v___x_1210_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1210_;
}
else
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_Lsp_instFromJsonRpcWireFormat_fromJson(v_x_1209_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1228_; 
v_a_1220_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1222_ = v___x_1211_;
v_isShared_1223_ = v_isSharedCheck_1228_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1211_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1228_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; lean_object* v___x_1226_; 
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v_a_1220_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 0, v___x_1224_);
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(lean_object* v_j_1229_, lean_object* v_k_1230_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = l_Lean_Json_getObjValD(v_j_1229_, v_k_1230_);
v___x_1232_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0_spec__0(v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1233_, lean_object* v_k_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(v_j_1233_, v_k_1234_);
lean_dec_ref(v_k_1234_);
return v_res_1235_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = 1;
v___x_1242_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__1));
v___x_1243_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1242_, v___x_1241_);
return v___x_1243_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1245_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__2);
v___x_1246_ = lean_string_append(v___x_1245_, v___x_1244_);
return v___x_1246_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = 1;
v___x_1251_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__5));
v___x_1252_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1251_, v___x_1250_);
return v___x_1252_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1253_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__6);
v___x_1254_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3);
v___x_1255_ = lean_string_append(v___x_1254_, v___x_1253_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1257_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__7);
v___x_1258_ = lean_string_append(v___x_1257_, v___x_1256_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = 1;
v___x_1263_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__10));
v___x_1264_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1263_, v___x_1262_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__11);
v___x_1266_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3);
v___x_1267_ = lean_string_append(v___x_1266_, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1269_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__12);
v___x_1270_ = lean_string_append(v___x_1269_, v___x_1268_);
return v___x_1270_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = 1;
v___x_1275_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__15));
v___x_1276_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1275_, v___x_1274_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__16);
v___x_1278_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__3);
v___x_1279_ = lean_string_append(v___x_1278_, v___x_1277_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1280_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1281_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__17);
v___x_1282_ = lean_string_append(v___x_1281_, v___x_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson(lean_object* v_json_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__0));
lean_inc(v_json_1283_);
v___x_1285_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_1283_, v___x_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_json_1283_);
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1295_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1295_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1290_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__8);
v___x_1291_ = lean_string_append(v___x_1290_, v_a_1286_);
lean_dec(v_a_1286_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1291_);
v___x_1293_ = v___x_1288_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
else
{
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_json_1283_);
v_a_1296_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1285_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1285_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 0);
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
lean_object* v_a_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_a_1304_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1304_);
lean_dec_ref_known(v___x_1285_, 1);
v___x_1305_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__1));
lean_inc(v_json_1283_);
v___x_1306_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0(v_json_1283_, v___x_1305_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1316_; 
lean_dec(v_a_1304_);
lean_dec(v_json_1283_);
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1316_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1316_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1311_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__13);
v___x_1312_ = lean_string_append(v___x_1311_, v_a_1307_);
lean_dec(v_a_1307_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 0, v___x_1312_);
v___x_1314_ = v___x_1309_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec(v_a_1304_);
lean_dec(v_json_1283_);
v_a_1317_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1306_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1306_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 0);
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v_a_1325_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1326_ = ((lean_object*)(l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson___closed__2));
v___x_1327_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson_spec__0(v_json_1283_, v___x_1326_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_a_1325_);
lean_dec(v_a_1304_);
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1337_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1337_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1332_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson___closed__18);
v___x_1333_ = lean_string_append(v___x_1332_, v_a_1328_);
lean_dec(v_a_1328_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1333_);
v___x_1335_ = v___x_1330_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
else
{
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec(v_a_1325_);
lean_dec(v_a_1304_);
v_a_1338_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1327_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1327_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set_tag(v___x_1340_, 0);
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1354_; 
v_a_1346_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1348_ = v___x_1327_;
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1327_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1354_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1350_, 0, v_a_1304_);
lean_ctor_set(v___x_1350_, 1, v_a_1325_);
lean_ctor_set(v___x_1350_, 2, v_a_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1350_);
v___x_1352_ = v___x_1348_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
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
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__0(lean_object* v_k_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1358_) == 0)
{
lean_object* v___x_1359_; 
lean_dec_ref(v_k_1357_);
v___x_1359_ = lean_box(0);
return v___x_1359_;
}
else
{
lean_object* v_val_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
v_val_1360_ = lean_ctor_get(v_x_1358_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v_x_1358_, 1);
v___x_1361_ = l_Lean_Lsp_instToJsonTextDocumentClientCapabilities_toJson(v_val_1360_);
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_k_1357_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1362_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
return v___x_1364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(lean_object* v_k_1365_, lean_object* v_x_1366_){
_start:
{
if (lean_obj_tag(v_x_1366_) == 0)
{
lean_object* v___x_1367_; 
lean_dec_ref(v_k_1365_);
v___x_1367_ = lean_box(0);
return v___x_1367_;
}
else
{
lean_object* v_val_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v_val_1368_ = lean_ctor_get(v_x_1366_, 0);
v___x_1369_ = l_Lean_Lsp_instToJsonWindowClientCapabilities_toJson(v_val_1368_);
v___x_1370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1370_, 0, v_k_1365_);
lean_ctor_set(v___x_1370_, 1, v___x_1369_);
v___x_1371_ = lean_box(0);
v___x_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1372_, 0, v___x_1370_);
lean_ctor_set(v___x_1372_, 1, v___x_1371_);
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1___boxed(lean_object* v_k_1373_, lean_object* v_x_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(v_k_1373_, v_x_1374_);
lean_dec(v_x_1374_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__2(lean_object* v_k_1376_, lean_object* v_x_1377_){
_start:
{
if (lean_obj_tag(v_x_1377_) == 0)
{
lean_object* v___x_1378_; 
lean_dec_ref(v_k_1376_);
v___x_1378_ = lean_box(0);
return v___x_1378_;
}
else
{
lean_object* v_val_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_val_1379_ = lean_ctor_get(v_x_1377_, 0);
lean_inc(v_val_1379_);
lean_dec_ref_known(v_x_1377_, 1);
v___x_1380_ = l_Lean_Lsp_instToJsonWorkspaceClientCapabilities_toJson(v_val_1379_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_k_1376_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_box(0);
v___x_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1381_);
lean_ctor_set(v___x_1383_, 1, v___x_1382_);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(lean_object* v_k_1384_, lean_object* v_x_1385_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_object* v___x_1386_; 
lean_dec_ref(v_k_1384_);
v___x_1386_ = lean_box(0);
return v___x_1386_;
}
else
{
lean_object* v_val_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_val_1387_ = lean_ctor_get(v_x_1385_, 0);
v___x_1388_ = l_Lean_Lsp_instToJsonLeanClientCapabilities_toJson(v_val_1387_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_k_1384_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3___boxed(lean_object* v_k_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(v_k_1392_, v_x_1393_);
lean_dec(v_x_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonClientCapabilities_toJson(lean_object* v_x_1399_){
_start:
{
lean_object* v_textDocument_x3f_1400_; lean_object* v_window_x3f_1401_; lean_object* v_workspace_x3f_1402_; lean_object* v_lean_x3f_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_textDocument_x3f_1400_ = lean_ctor_get(v_x_1399_, 0);
lean_inc(v_textDocument_x3f_1400_);
v_window_x3f_1401_ = lean_ctor_get(v_x_1399_, 1);
lean_inc(v_window_x3f_1401_);
v_workspace_x3f_1402_ = lean_ctor_get(v_x_1399_, 2);
lean_inc(v_workspace_x3f_1402_);
v_lean_x3f_1403_ = lean_ctor_get(v_x_1399_, 3);
lean_inc(v_lean_x3f_1403_);
lean_dec_ref(v_x_1399_);
v___x_1404_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0));
v___x_1405_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__0(v___x_1404_, v_textDocument_x3f_1400_);
v___x_1406_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1));
v___x_1407_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__1(v___x_1406_, v_window_x3f_1401_);
lean_dec(v_window_x3f_1401_);
v___x_1408_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2));
v___x_1409_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__2(v___x_1408_, v_workspace_x3f_1402_);
v___x_1410_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3));
v___x_1411_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonClientCapabilities_toJson_spec__3(v___x_1410_, v_lean_x3f_1403_);
lean_dec(v_lean_x3f_1403_);
v___x_1412_ = lean_box(0);
v___x_1413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1411_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1409_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1407_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1405_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1418_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1416_, v___x_1417_);
v___x_1419_ = l_Lean_Json_mkObj(v___x_1418_);
lean_dec(v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4(lean_object* v_x_1424_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
lean_object* v___x_1425_; 
v___x_1425_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4___closed__0));
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Lsp_instFromJsonWorkspaceClientCapabilities_fromJson(v_x_1424_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1434_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1434_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1434_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1434_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1432_; 
if (v_isShared_1430_ == 0)
{
v___x_1432_ = v___x_1429_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1443_; 
v_a_1435_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1437_ = v___x_1426_;
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1426_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v_a_1435_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 0, v___x_1439_);
v___x_1441_ = v___x_1437_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(lean_object* v_j_1444_, lean_object* v_k_1445_){
_start:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1446_ = l_Lean_Json_getObjValD(v_j_1444_, v_k_1445_);
v___x_1447_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2_spec__4(v___x_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2___boxed(lean_object* v_j_1448_, lean_object* v_k_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(v_j_1448_, v_k_1449_);
lean_dec_ref(v_k_1449_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6(lean_object* v_x_1453_){
_start:
{
if (lean_obj_tag(v_x_1453_) == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6___closed__0));
return v___x_1454_;
}
else
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Lsp_instFromJsonLeanClientCapabilities_fromJson(v_x_1453_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1472_; 
v_a_1464_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1466_ = v___x_1455_;
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1455_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_a_1464_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 0, v___x_1468_);
v___x_1470_ = v___x_1466_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(lean_object* v_j_1473_, lean_object* v_k_1474_){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = l_Lean_Json_getObjValD(v_j_1473_, v_k_1474_);
v___x_1476_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3_spec__6(v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3___boxed(lean_object* v_j_1477_, lean_object* v_k_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(v_j_1477_, v_k_1478_);
lean_dec_ref(v_k_1478_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_1480_){
_start:
{
if (lean_obj_tag(v_x_1480_) == 0)
{
lean_object* v___x_1481_; 
v___x_1481_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1481_;
}
else
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Lsp_instFromJsonWindowClientCapabilities_fromJson(v_x_1480_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1499_; 
v_a_1491_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1493_ = v___x_1482_;
v_isShared_1494_ = v_isSharedCheck_1499_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1482_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1499_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v_a_1491_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 0, v___x_1495_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(lean_object* v_j_1500_, lean_object* v_k_1501_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = l_Lean_Json_getObjValD(v_j_1500_, v_k_1501_);
v___x_1503_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1_spec__2(v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1___boxed(lean_object* v_j_1504_, lean_object* v_k_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(v_j_1504_, v_k_1505_);
lean_dec_ref(v_k_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1509_){
_start:
{
if (lean_obj_tag(v_x_1509_) == 0)
{
lean_object* v___x_1510_; 
v___x_1510_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Lsp_instFromJsonTextDocumentClientCapabilities_fromJson(v_x_1509_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1511_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1511_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1528_; 
v_a_1520_ = lean_ctor_get(v___x_1511_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1511_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1522_ = v___x_1511_;
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1511_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1528_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v_a_1520_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 0, v___x_1524_);
v___x_1526_ = v___x_1522_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(lean_object* v_j_1529_, lean_object* v_k_1530_){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = l_Lean_Json_getObjValD(v_j_1529_, v_k_1530_);
v___x_1532_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0_spec__0(v___x_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1533_, lean_object* v_k_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(v_j_1533_, v_k_1534_);
lean_dec_ref(v_k_1534_);
return v_res_1535_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = 1;
v___x_1542_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__1));
v___x_1543_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1542_, v___x_1541_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1545_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__2);
v___x_1546_ = lean_string_append(v___x_1545_, v___x_1544_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = 1;
v___x_1551_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__5));
v___x_1552_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1551_, v___x_1550_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__6);
v___x_1554_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1555_ = lean_string_append(v___x_1554_, v___x_1553_);
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1556_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1557_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__7);
v___x_1558_ = lean_string_append(v___x_1557_, v___x_1556_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = 1;
v___x_1563_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__10));
v___x_1564_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1563_, v___x_1562_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1565_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__11);
v___x_1566_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1567_ = lean_string_append(v___x_1566_, v___x_1565_);
return v___x_1567_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1569_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__12);
v___x_1570_ = lean_string_append(v___x_1569_, v___x_1568_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16(void){
_start:
{
uint8_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = 1;
v___x_1575_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__15));
v___x_1576_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1575_, v___x_1574_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__16);
v___x_1578_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1579_ = lean_string_append(v___x_1578_, v___x_1577_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1581_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__17);
v___x_1582_ = lean_string_append(v___x_1581_, v___x_1580_);
return v___x_1582_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21(void){
_start:
{
uint8_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = 1;
v___x_1587_ = ((lean_object*)(l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__20));
v___x_1588_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1587_, v___x_1586_);
return v___x_1588_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__21);
v___x_1590_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__3);
v___x_1591_ = lean_string_append(v___x_1590_, v___x_1589_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1593_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__22);
v___x_1594_ = lean_string_append(v___x_1593_, v___x_1592_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonClientCapabilities_fromJson(lean_object* v_json_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__0));
lean_inc(v_json_1595_);
v___x_1597_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__0(v_json_1595_, v___x_1596_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1607_; 
lean_dec(v_json_1595_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1607_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1607_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1602_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__8);
v___x_1603_ = lean_string_append(v___x_1602_, v_a_1598_);
lean_dec(v_a_1598_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 0, v___x_1603_);
v___x_1605_ = v___x_1600_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
else
{
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec(v_json_1595_);
v_a_1608_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1597_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1597_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set_tag(v___x_1610_, 0);
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_a_1616_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1597_, 1);
v___x_1617_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__1));
lean_inc(v_json_1595_);
v___x_1618_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__1(v_json_1595_, v___x_1617_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v_a_1616_);
lean_dec(v_json_1595_);
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1628_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1623_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__13);
v___x_1624_ = lean_string_append(v___x_1623_, v_a_1619_);
lean_dec(v_a_1619_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1624_);
v___x_1626_ = v___x_1621_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
else
{
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec(v_a_1616_);
lean_dec(v_json_1595_);
v_a_1629_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1618_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1618_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set_tag(v___x_1631_, 0);
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_a_1637_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v___x_1618_, 1);
v___x_1638_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__2));
lean_inc(v_json_1595_);
v___x_1639_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__2(v_json_1595_, v___x_1638_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1649_; 
lean_dec(v_a_1637_);
lean_dec(v_a_1616_);
lean_dec(v_json_1595_);
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1649_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1649_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1644_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__18);
v___x_1645_ = lean_string_append(v___x_1644_, v_a_1640_);
lean_dec(v_a_1640_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 0, v___x_1645_);
v___x_1647_ = v___x_1642_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
else
{
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_a_1637_);
lean_dec(v_a_1616_);
lean_dec(v_json_1595_);
v_a_1650_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1639_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1639_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set_tag(v___x_1652_, 0);
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_a_1658_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1639_, 1);
v___x_1659_ = ((lean_object*)(l_Lean_Lsp_instToJsonClientCapabilities_toJson___closed__3));
v___x_1660_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonClientCapabilities_fromJson_spec__3(v_json_1595_, v___x_1659_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_a_1658_);
lean_dec(v_a_1637_);
lean_dec(v_a_1616_);
v_a_1661_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1663_ = v___x_1660_;
v_isShared_1664_ = v_isSharedCheck_1670_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1660_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1670_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1665_ = lean_obj_once(&l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23, &l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonClientCapabilities_fromJson___closed__23);
v___x_1666_ = lean_string_append(v___x_1665_, v_a_1661_);
lean_dec(v_a_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 0, v___x_1666_);
v___x_1668_ = v___x_1663_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
else
{
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_a_1658_);
lean_dec(v_a_1637_);
lean_dec(v_a_1616_);
v_a_1671_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1660_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1660_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set_tag(v___x_1673_, 0);
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1687_; 
v_a_1679_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1681_ = v___x_1660_;
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1660_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1687_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1683_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1683_, 0, v_a_1616_);
lean_ctor_set(v___x_1683_, 1, v_a_1637_);
lean_ctor_set(v___x_1683_, 2, v_a_1658_);
lean_ctor_set(v___x_1683_, 3, v_a_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 0, v___x_1683_);
v___x_1685_ = v___x_1681_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
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
uint8_t l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport(lean_object* v_c_1690_){
_start:
{
lean_object* v_lean_x3f_1691_; 
v_lean_x3f_1691_ = lean_ctor_get(v_c_1690_, 3);
if (lean_obj_tag(v_lean_x3f_1691_) == 1)
{
lean_object* v_val_1692_; lean_object* v_incrementalDiagnosticSupport_x3f_1693_; 
v_val_1692_ = lean_ctor_get(v_lean_x3f_1691_, 0);
v_incrementalDiagnosticSupport_x3f_1693_ = lean_ctor_get(v_val_1692_, 0);
if (lean_obj_tag(v_incrementalDiagnosticSupport_x3f_1693_) == 1)
{
lean_object* v_val_1694_; uint8_t v___x_1695_; 
v_val_1694_ = lean_ctor_get(v_incrementalDiagnosticSupport_x3f_1693_, 0);
v___x_1695_ = lean_unbox(v_val_1694_);
return v___x_1695_;
}
else
{
uint8_t v___x_1696_; 
v___x_1696_ = 0;
return v___x_1696_;
}
}
else
{
uint8_t v___x_1697_; 
v___x_1697_ = 0;
return v___x_1697_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1690_ = stack[0].m_obj;
uint8_t v_res_1698_;
v_res_1698_ = l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport(v_c_1690_);
stack->m_num = v_res_1698_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport___boxed(lean_object* v_c_1699_){
_start:
{
uint8_t v_res_1700_; lean_object* v_r_1701_; 
v_res_1700_ = l_Lean_Lsp_ClientCapabilities_incrementalDiagnosticSupport(v_c_1699_);
lean_dec_ref(v_c_1699_);
v_r_1701_ = lean_box(v_res_1700_);
return v_r_1701_;
}
}
uint8_t l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(lean_object* v_c_1702_){
_start:
{
lean_object* v_lean_x3f_1703_; 
v_lean_x3f_1703_ = lean_ctor_get(v_c_1702_, 3);
if (lean_obj_tag(v_lean_x3f_1703_) == 1)
{
lean_object* v_val_1704_; lean_object* v_silentDiagnosticSupport_x3f_1705_; 
v_val_1704_ = lean_ctor_get(v_lean_x3f_1703_, 0);
v_silentDiagnosticSupport_x3f_1705_ = lean_ctor_get(v_val_1704_, 1);
if (lean_obj_tag(v_silentDiagnosticSupport_x3f_1705_) == 1)
{
lean_object* v_val_1706_; uint8_t v___x_1707_; 
v_val_1706_ = lean_ctor_get(v_silentDiagnosticSupport_x3f_1705_, 0);
v___x_1707_ = lean_unbox(v_val_1706_);
return v___x_1707_;
}
else
{
uint8_t v___x_1708_; 
v___x_1708_ = 0;
return v___x_1708_;
}
}
else
{
uint8_t v___x_1709_; 
v___x_1709_ = 0;
return v___x_1709_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1702_ = stack[0].m_obj;
uint8_t v_res_1710_;
v_res_1710_ = l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(v_c_1702_);
stack->m_num = v_res_1710_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport___boxed(lean_object* v_c_1711_){
_start:
{
uint8_t v_res_1712_; lean_object* v_r_1713_; 
v_res_1712_ = l_Lean_Lsp_ClientCapabilities_silentDiagnosticSupport(v_c_1711_);
lean_dec_ref(v_c_1711_);
v_r_1713_ = lean_box(v_res_1712_);
return v_r_1713_;
}
}
uint8_t l_Lean_Lsp_ClientCapabilities_rpcWireFormat(lean_object* v_c_1714_){
_start:
{
lean_object* v_lean_x3f_1715_; 
v_lean_x3f_1715_ = lean_ctor_get(v_c_1714_, 3);
if (lean_obj_tag(v_lean_x3f_1715_) == 1)
{
lean_object* v_val_1716_; lean_object* v_rpcWireFormat_x3f_1717_; 
v_val_1716_ = lean_ctor_get(v_lean_x3f_1715_, 0);
v_rpcWireFormat_x3f_1717_ = lean_ctor_get(v_val_1716_, 2);
if (lean_obj_tag(v_rpcWireFormat_x3f_1717_) == 1)
{
lean_object* v_val_1718_; uint8_t v___x_1719_; 
v_val_1718_ = lean_ctor_get(v_rpcWireFormat_x3f_1717_, 0);
v___x_1719_ = lean_unbox(v_val_1718_);
return v___x_1719_;
}
else
{
uint8_t v___x_1720_; 
v___x_1720_ = 0;
return v___x_1720_;
}
}
else
{
uint8_t v___x_1721_; 
v___x_1721_ = 0;
return v___x_1721_;
}
}
}
LEAN_EXPORT void l_Lean_Lsp_ClientCapabilities_rpcWireFormat_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1714_ = stack[0].m_obj;
uint8_t v_res_1722_;
v_res_1722_ = l_Lean_Lsp_ClientCapabilities_rpcWireFormat(v_c_1714_);
stack->m_num = v_res_1722_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_ClientCapabilities_rpcWireFormat___boxed(lean_object* v_c_1723_){
_start:
{
uint8_t v_res_1724_; lean_object* v_r_1725_; 
v_res_1724_ = l_Lean_Lsp_ClientCapabilities_rpcWireFormat(v_c_1723_);
lean_dec_ref(v_c_1723_);
v_r_1725_ = lean_box(v_res_1724_);
return v_r_1725_;
}
}
static lean_object* _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_Lsp_instFromJsonModuleHierarchyOptions_fromJson___redArg();
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_1729_){
_start:
{
if (lean_obj_tag(v_x_1729_) == 0)
{
lean_object* v___x_1730_; 
v___x_1730_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_obj_once(&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1, &l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1_once, _init_l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___closed__1);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1733_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_a_1732_);
return v___x_1733_;
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_a_1734_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1734_);
v___x_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1735_, 0, v_a_1734_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
return v___x_1736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0___boxed(lean_object* v_x_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(v_x_1737_);
lean_dec(v_x_1737_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(lean_object* v_j_1739_, lean_object* v_k_1740_){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = l_Lean_Json_getObjValD(v_j_1739_, v_k_1740_);
v___x_1742_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0_spec__0(v___x_1741_);
lean_dec(v___x_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0___boxed(lean_object* v_j_1743_, lean_object* v_k_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(v_j_1743_, v_k_1744_);
lean_dec_ref(v_k_1744_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_1748_){
_start:
{
if (lean_obj_tag(v_x_1748_) == 0)
{
lean_object* v___x_1749_; 
v___x_1749_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_1749_;
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Lsp_instFromJsonRpcOptions_fromJson(v_x_1748_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1767_; 
v_a_1759_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1761_ = v___x_1750_;
v_isShared_1762_ = v_isSharedCheck_1767_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1750_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1767_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
v___x_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1763_, 0, v_a_1759_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1763_);
v___x_1765_ = v___x_1761_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(lean_object* v_j_1768_, lean_object* v_k_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = l_Lean_Json_getObjValD(v_j_1768_, v_k_1769_);
v___x_1771_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1_spec__2(v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1___boxed(lean_object* v_j_1772_, lean_object* v_k_1773_){
_start:
{
lean_object* v_res_1774_; 
v_res_1774_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(v_j_1772_, v_k_1773_);
lean_dec_ref(v_k_1773_);
return v_res_1774_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3(void){
_start:
{
uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = 1;
v___x_1782_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__2));
v___x_1783_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1782_, v___x_1781_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_1785_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__3);
v___x_1786_ = lean_string_append(v___x_1785_, v___x_1784_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7(void){
_start:
{
uint8_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = 1;
v___x_1791_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__6));
v___x_1792_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1791_, v___x_1790_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__7);
v___x_1794_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4);
v___x_1795_ = lean_string_append(v___x_1794_, v___x_1793_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9(void){
_start:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1796_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1797_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__8);
v___x_1798_ = lean_string_append(v___x_1797_, v___x_1796_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = 1;
v___x_1804_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__12));
v___x_1805_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__13);
v___x_1807_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__4);
v___x_1808_ = lean_string_append(v___x_1807_, v___x_1806_);
return v___x_1808_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_1810_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__14);
v___x_1811_ = lean_string_append(v___x_1810_, v___x_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson(lean_object* v_json_1812_){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0));
lean_inc(v_json_1812_);
v___x_1814_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__0(v_json_1812_, v___x_1813_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_json_1812_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1819_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__9);
v___x_1820_ = lean_string_append(v___x_1819_, v_a_1815_);
lean_dec(v_a_1815_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1820_);
v___x_1822_ = v___x_1817_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec(v_json_1812_);
v_a_1825_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1814_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1814_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 0);
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v_a_1833_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1833_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1834_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10));
v___x_1835_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson_spec__1(v_json_1812_, v___x_1834_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1845_; 
lean_dec(v_a_1833_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1845_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1840_ = lean_obj_once(&l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15, &l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__15);
v___x_1841_ = lean_string_append(v___x_1840_, v_a_1836_);
lean_dec(v_a_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
else
{
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_a_1833_);
v_a_1846_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1835_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1835_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 0);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1862_; 
v_a_1854_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1856_ = v___x_1835_;
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1835_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1862_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v_a_1833_);
lean_ctor_set(v___x_1858_, 1, v_a_1854_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1858_);
v___x_1860_ = v___x_1856_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
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
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_Lsp_instToJsonModuleHierarchyOptions_toJson___redArg();
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(lean_object* v_k_1866_, lean_object* v_x_1867_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v_k_1866_);
v___x_1868_ = lean_box(0);
return v___x_1868_;
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1869_ = lean_obj_once(&l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0, &l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0_once, _init_l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___closed__0);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v_k_1866_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0___boxed(lean_object* v_k_1873_, lean_object* v_x_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(v_k_1873_, v_x_1874_);
lean_dec(v_x_1874_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__1(lean_object* v_k_1876_, lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
lean_object* v___x_1878_; 
lean_dec_ref(v_k_1876_);
v___x_1878_ = lean_box(0);
return v___x_1878_;
}
else
{
lean_object* v_val_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_val_1879_ = lean_ctor_get(v_x_1877_, 0);
lean_inc(v_val_1879_);
lean_dec_ref_known(v_x_1877_, 1);
v___x_1880_ = l_Lean_Lsp_instToJsonRpcOptions_toJson(v_val_1879_);
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_k_1876_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = lean_box(0);
v___x_1883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
return v___x_1883_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson(lean_object* v_x_1884_){
_start:
{
lean_object* v_moduleHierarchyProvider_x3f_1885_; lean_object* v_rpcProvider_x3f_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1902_; 
v_moduleHierarchyProvider_x3f_1885_ = lean_ctor_get(v_x_1884_, 0);
v_rpcProvider_x3f_1886_ = lean_ctor_get(v_x_1884_, 1);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_x_1884_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1888_ = v_x_1884_;
v_isShared_1889_ = v_isSharedCheck_1902_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_rpcProvider_x3f_1886_);
lean_inc(v_moduleHierarchyProvider_x3f_1885_);
lean_dec(v_x_1884_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1902_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1890_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__0));
v___x_1891_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__0(v___x_1890_, v_moduleHierarchyProvider_x3f_1885_);
lean_dec(v_moduleHierarchyProvider_x3f_1885_);
v___x_1892_ = ((lean_object*)(l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson___closed__10));
v___x_1893_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonLeanServerCapabilities_toJson_spec__1(v___x_1892_, v_rpcProvider_x3f_1886_);
v___x_1894_ = lean_box(0);
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 1);
lean_ctor_set(v___x_1888_, 1, v___x_1894_);
lean_ctor_set(v___x_1888_, 0, v___x_1893_);
v___x_1896_ = v___x_1888_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1891_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_1899_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_1897_, v___x_1898_);
v___x_1900_ = l_Lean_Json_mkObj(v___x_1899_);
lean_dec(v___x_1899_);
return v___x_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(lean_object* v_k_1905_, lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v___x_1907_; 
lean_dec_ref(v_k_1905_);
v___x_1907_ = lean_box(0);
return v___x_1907_;
}
else
{
lean_object* v_val_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_val_1908_ = lean_ctor_get(v_x_1906_, 0);
v___x_1909_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(v_val_1908_);
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_k_1905_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_box(0);
v___x_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0___boxed(lean_object* v_k_1913_, lean_object* v_x_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(v_k_1913_, v_x_1914_);
lean_dec(v_x_1914_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__1(lean_object* v_k_1916_, lean_object* v_x_1917_){
_start:
{
if (lean_obj_tag(v_x_1917_) == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref(v_k_1916_);
v___x_1918_ = lean_box(0);
return v___x_1918_;
}
else
{
lean_object* v_val_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_val_1919_ = lean_ctor_get(v_x_1917_, 0);
lean_inc(v_val_1919_);
lean_dec_ref_known(v_x_1917_, 1);
v___x_1920_ = l_Lean_Lsp_instToJsonCompletionOptions_toJson(v_val_1919_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v_k_1916_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_box(0);
v___x_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
return v___x_1923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(lean_object* v_k_1924_, lean_object* v_x_1925_){
_start:
{
if (lean_obj_tag(v_x_1925_) == 0)
{
lean_object* v___x_1926_; 
lean_dec_ref(v_k_1924_);
v___x_1926_ = lean_box(0);
return v___x_1926_;
}
else
{
lean_object* v_val_1927_; uint8_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_val_1927_ = lean_ctor_get(v_x_1925_, 0);
v___x_1928_ = lean_unbox(v_val_1927_);
v___x_1929_ = l_Lean_Lsp_instToJsonRenameOptions_toJson(v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v_k_1924_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_box(0);
v___x_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2___boxed(lean_object* v_k_1933_, lean_object* v_x_1934_){
_start:
{
lean_object* v_res_1935_; 
v_res_1935_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(v_k_1933_, v_x_1934_);
lean_dec(v_x_1934_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__3(lean_object* v_k_1936_, lean_object* v_x_1937_){
_start:
{
if (lean_obj_tag(v_x_1937_) == 0)
{
lean_object* v___x_1938_; 
lean_dec_ref(v_k_1936_);
v___x_1938_ = lean_box(0);
return v___x_1938_;
}
else
{
lean_object* v_val_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v_val_1939_ = lean_ctor_get(v_x_1937_, 0);
lean_inc(v_val_1939_);
lean_dec_ref_known(v_x_1937_, 1);
v___x_1940_ = l_Lean_Lsp_instToJsonSemanticTokensOptions_toJson(v_val_1939_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_k_1936_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__4(lean_object* v_k_1944_, lean_object* v_x_1945_){
_start:
{
if (lean_obj_tag(v_x_1945_) == 0)
{
lean_object* v___x_1946_; 
lean_dec_ref(v_k_1944_);
v___x_1946_ = lean_box(0);
return v___x_1946_;
}
else
{
lean_object* v_val_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v_val_1947_ = lean_ctor_get(v_x_1945_, 0);
lean_inc(v_val_1947_);
lean_dec_ref_known(v_x_1945_, 1);
v___x_1948_ = l_Lean_Lsp_instToJsonCodeActionOptions_toJson(v_val_1947_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_k_1944_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_box(0);
v___x_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
return v___x_1951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(lean_object* v_k_1952_, lean_object* v_x_1953_){
_start:
{
if (lean_obj_tag(v_x_1953_) == 0)
{
lean_object* v___x_1954_; 
lean_dec_ref(v_k_1952_);
v___x_1954_ = lean_box(0);
return v___x_1954_;
}
else
{
lean_object* v_val_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_val_1955_ = lean_ctor_get(v_x_1953_, 0);
v___x_1956_ = l_Lean_Lsp_instToJsonInlayHintOptions_toJson(v_val_1955_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v_k_1952_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_box(0);
v___x_1959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
return v___x_1959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5___boxed(lean_object* v_k_1960_, lean_object* v_x_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(v_k_1960_, v_x_1961_);
lean_dec(v_x_1961_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__6(lean_object* v_k_1963_, lean_object* v_x_1964_){
_start:
{
if (lean_obj_tag(v_x_1964_) == 0)
{
lean_object* v___x_1965_; 
lean_dec_ref(v_k_1963_);
v___x_1965_ = lean_box(0);
return v___x_1965_;
}
else
{
lean_object* v_val_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v_val_1966_ = lean_ctor_get(v_x_1964_, 0);
lean_inc(v_val_1966_);
lean_dec_ref_known(v_x_1964_, 1);
v___x_1967_ = l_Lean_Lsp_instToJsonSignatureHelpOptions_toJson(v_val_1966_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_k_1963_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1968_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(lean_object* v_k_1971_, lean_object* v_x_1972_){
_start:
{
if (lean_obj_tag(v_x_1972_) == 0)
{
lean_object* v___x_1973_; 
lean_dec_ref(v_k_1971_);
v___x_1973_ = lean_box(0);
return v___x_1973_;
}
else
{
lean_object* v_val_1974_; uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_val_1974_ = lean_ctor_get(v_x_1972_, 0);
v___x_1975_ = lean_unbox(v_val_1974_);
v___x_1976_ = l_Lean_Lsp_instToJsonDocumentColorOptions_toJson(v___x_1975_);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v_k_1971_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = lean_box(0);
v___x_1979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7___boxed(lean_object* v_k_1980_, lean_object* v_x_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(v_k_1980_, v_x_1981_);
lean_dec(v_x_1981_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__8(lean_object* v_k_1983_, lean_object* v_x_1984_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 0)
{
lean_object* v___x_1985_; 
lean_dec_ref(v_k_1983_);
v___x_1985_ = lean_box(0);
return v___x_1985_;
}
else
{
lean_object* v_val_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v_val_1986_ = lean_ctor_get(v_x_1984_, 0);
lean_inc(v_val_1986_);
lean_dec_ref_known(v_x_1984_, 1);
v___x_1987_ = l_Lean_Lsp_instToJsonLeanServerCapabilities_toJson(v_val_1986_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v_k_1983_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_box(0);
v___x_1990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonServerCapabilities_toJson(lean_object* v_x_2010_){
_start:
{
lean_object* v_textDocumentSync_x3f_2011_; lean_object* v_completionProvider_x3f_2012_; uint8_t v_hoverProvider_2013_; uint8_t v_documentHighlightProvider_2014_; uint8_t v_documentSymbolProvider_2015_; uint8_t v_definitionProvider_2016_; uint8_t v_declarationProvider_2017_; uint8_t v_typeDefinitionProvider_2018_; uint8_t v_referencesProvider_2019_; uint8_t v_callHierarchyProvider_2020_; lean_object* v_renameProvider_x3f_2021_; uint8_t v_workspaceSymbolProvider_2022_; uint8_t v_foldingRangeProvider_2023_; lean_object* v_semanticTokensProvider_x3f_2024_; lean_object* v_codeActionProvider_x3f_2025_; lean_object* v_inlayHintProvider_x3f_2026_; lean_object* v_signatureHelpProvider_x3f_2027_; lean_object* v_colorProvider_x3f_2028_; lean_object* v_experimental_x3f_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_textDocumentSync_x3f_2011_ = lean_ctor_get(v_x_2010_, 0);
lean_inc(v_textDocumentSync_x3f_2011_);
v_completionProvider_x3f_2012_ = lean_ctor_get(v_x_2010_, 1);
lean_inc(v_completionProvider_x3f_2012_);
v_hoverProvider_2013_ = lean_ctor_get_uint8(v_x_2010_, sizeof(void*)*9);
v_documentHighlightProvider_2014_ = lean_ctor_get_uint8(v_x_2010_, sizeof(void*)*9 + 1);
v_documentSymbolProvider_2015_ = lean_ctor_get_uint8(v_x_2010_, sizeof(void*)*9 + 2);
v_definitionProvider_2016_ = lean_ctor_get_uint8(v_x_2010_, sizeof(void*)*9 + 3);
v_declarationProvider_2017_ = lean_ctor_get_uint8(v_x_2010_, sizeof(void*)*9 + 4);
v_typeDefinitionProvider_2018_ = lean_ctor_get_uint8(v_x_2010_, sizeof(void*)*9 + 5);
v_referencesProvider_2019_ = lean_ctor_get_uint8(v_x_2010_, sizeof(void*)*9 + 6);
v_callHierarchyProvider_2020_ = lean_ctor_get_uint8(v_x_2010_, sizeof(void*)*9 + 7);
v_renameProvider_x3f_2021_ = lean_ctor_get(v_x_2010_, 2);
lean_inc(v_renameProvider_x3f_2021_);
v_workspaceSymbolProvider_2022_ = lean_ctor_get_uint8(v_x_2010_, sizeof(void*)*9 + 8);
v_foldingRangeProvider_2023_ = lean_ctor_get_uint8(v_x_2010_, sizeof(void*)*9 + 9);
v_semanticTokensProvider_x3f_2024_ = lean_ctor_get(v_x_2010_, 3);
lean_inc(v_semanticTokensProvider_x3f_2024_);
v_codeActionProvider_x3f_2025_ = lean_ctor_get(v_x_2010_, 4);
lean_inc(v_codeActionProvider_x3f_2025_);
v_inlayHintProvider_x3f_2026_ = lean_ctor_get(v_x_2010_, 5);
lean_inc(v_inlayHintProvider_x3f_2026_);
v_signatureHelpProvider_x3f_2027_ = lean_ctor_get(v_x_2010_, 6);
lean_inc(v_signatureHelpProvider_x3f_2027_);
v_colorProvider_x3f_2028_ = lean_ctor_get(v_x_2010_, 7);
lean_inc(v_colorProvider_x3f_2028_);
v_experimental_x3f_2029_ = lean_ctor_get(v_x_2010_, 8);
lean_inc(v_experimental_x3f_2029_);
lean_dec_ref(v_x_2010_);
v___x_2030_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0));
v___x_2031_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__0(v___x_2030_, v_textDocumentSync_x3f_2011_);
lean_dec(v_textDocumentSync_x3f_2011_);
v___x_2032_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1));
v___x_2033_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__1(v___x_2032_, v_completionProvider_x3f_2012_);
v___x_2034_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2));
v___x_2035_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2035_, 0, v_hoverProvider_2013_);
v___x_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2034_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = lean_box(0);
v___x_2038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3));
v___x_2040_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2040_, 0, v_documentHighlightProvider_2014_);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v___x_2037_);
v___x_2043_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4));
v___x_2044_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2044_, 0, v_documentSymbolProvider_2015_);
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2043_);
lean_ctor_set(v___x_2045_, 1, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
lean_ctor_set(v___x_2046_, 1, v___x_2037_);
v___x_2047_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5));
v___x_2048_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2048_, 0, v_definitionProvider_2016_);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2047_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
v___x_2050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
lean_ctor_set(v___x_2050_, 1, v___x_2037_);
v___x_2051_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6));
v___x_2052_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2052_, 0, v_declarationProvider_2017_);
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2051_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
lean_ctor_set(v___x_2054_, 1, v___x_2037_);
v___x_2055_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7));
v___x_2056_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2056_, 0, v_typeDefinitionProvider_2018_);
v___x_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2055_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v___x_2037_);
v___x_2059_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8));
v___x_2060_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2060_, 0, v_referencesProvider_2019_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2059_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
lean_ctor_set(v___x_2062_, 1, v___x_2037_);
v___x_2063_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9));
v___x_2064_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2064_, 0, v_callHierarchyProvider_2020_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2063_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v___x_2037_);
v___x_2067_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10));
v___x_2068_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__2(v___x_2067_, v_renameProvider_x3f_2021_);
lean_dec(v_renameProvider_x3f_2021_);
v___x_2069_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11));
v___x_2070_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2070_, 0, v_workspaceSymbolProvider_2022_);
v___x_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2069_);
lean_ctor_set(v___x_2071_, 1, v___x_2070_);
v___x_2072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
lean_ctor_set(v___x_2072_, 1, v___x_2037_);
v___x_2073_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12));
v___x_2074_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2074_, 0, v_foldingRangeProvider_2023_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
lean_ctor_set(v___x_2076_, 1, v___x_2037_);
v___x_2077_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13));
v___x_2078_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__3(v___x_2077_, v_semanticTokensProvider_x3f_2024_);
v___x_2079_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14));
v___x_2080_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__4(v___x_2079_, v_codeActionProvider_x3f_2025_);
v___x_2081_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15));
v___x_2082_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__5(v___x_2081_, v_inlayHintProvider_x3f_2026_);
lean_dec(v_inlayHintProvider_x3f_2026_);
v___x_2083_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16));
v___x_2084_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__6(v___x_2083_, v_signatureHelpProvider_x3f_2027_);
v___x_2085_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17));
v___x_2086_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__7(v___x_2085_, v_colorProvider_x3f_2028_);
lean_dec(v_colorProvider_x3f_2028_);
v___x_2087_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18));
v___x_2088_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonServerCapabilities_toJson_spec__8(v___x_2087_, v_experimental_x3f_2029_);
v___x_2089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
lean_ctor_set(v___x_2089_, 1, v___x_2037_);
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2086_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
v___x_2091_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2084_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2082_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2080_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2078_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2076_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2072_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2068_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2066_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2062_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2058_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2054_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2050_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2046_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2042_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2038_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2033_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2031_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = ((lean_object*)(l_Lean_Lsp_instToJsonCompletionItemCapabilities_toJson___closed__1));
v___x_2109_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCompletionItemCapabilities_toJson_spec__1(v___x_2107_, v___x_2108_);
v___x_2110_ = l_Lean_Json_mkObj(v___x_2109_);
lean_dec(v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10(lean_object* v_x_2115_){
_start:
{
if (lean_obj_tag(v_x_2115_) == 0)
{
lean_object* v___x_2116_; 
v___x_2116_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10___closed__0));
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_Lsp_instFromJsonInlayHintOptions_fromJson(v_x_2115_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2134_; 
v_a_2126_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2128_ = v___x_2117_;
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2117_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2134_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v_a_2126_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2130_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(lean_object* v_j_2135_, lean_object* v_k_2136_){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = l_Lean_Json_getObjValD(v_j_2135_, v_k_2136_);
v___x_2138_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5_spec__10(v___x_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5___boxed(lean_object* v_j_2139_, lean_object* v_k_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(v_j_2139_, v_k_2140_);
lean_dec_ref(v_k_2140_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8(lean_object* v_x_2144_){
_start:
{
if (lean_obj_tag(v_x_2144_) == 0)
{
lean_object* v___x_2145_; 
v___x_2145_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8___closed__0));
return v___x_2145_;
}
else
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Lsp_instFromJsonCodeActionOptions_fromJson(v_x_2144_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
v_a_2147_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2146_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2146_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2163_; 
v_a_2155_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2157_ = v___x_2146_;
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2146_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2163_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2159_, 0, v_a_2155_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2159_);
v___x_2161_ = v___x_2157_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(lean_object* v_j_2164_, lean_object* v_k_2165_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = l_Lean_Json_getObjValD(v_j_2164_, v_k_2165_);
v___x_2167_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4_spec__8(v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4___boxed(lean_object* v_j_2168_, lean_object* v_k_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(v_j_2168_, v_k_2169_);
lean_dec_ref(v_k_2169_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16(lean_object* v_x_2173_){
_start:
{
if (lean_obj_tag(v_x_2173_) == 0)
{
lean_object* v___x_2174_; 
v___x_2174_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16___closed__0));
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_Lsp_instFromJsonLeanServerCapabilities_fromJson(v_x_2173_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2192_; 
v_a_2184_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2186_ = v___x_2175_;
v_isShared_2187_ = v_isSharedCheck_2192_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2175_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2192_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_a_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2188_);
v___x_2190_ = v___x_2186_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(lean_object* v_j_2193_, lean_object* v_k_2194_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2195_ = l_Lean_Json_getObjValD(v_j_2193_, v_k_2194_);
v___x_2196_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8_spec__16(v___x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8___boxed(lean_object* v_j_2197_, lean_object* v_k_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(v_j_2197_, v_k_2198_);
lean_dec_ref(v_k_2198_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12(lean_object* v_x_2202_){
_start:
{
if (lean_obj_tag(v_x_2202_) == 0)
{
lean_object* v___x_2203_; 
v___x_2203_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12___closed__0));
return v___x_2203_;
}
else
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_Lsp_instFromJsonSignatureHelpOptions_fromJson(v_x_2202_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2221_; 
v_a_2213_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2215_ = v___x_2204_;
v_isShared_2216_ = v_isSharedCheck_2221_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2204_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2221_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_a_2213_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v___x_2217_);
v___x_2219_ = v___x_2215_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(lean_object* v_j_2222_, lean_object* v_k_2223_){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = l_Lean_Json_getObjValD(v_j_2222_, v_k_2223_);
v___x_2225_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6_spec__12(v___x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6___boxed(lean_object* v_j_2226_, lean_object* v_k_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(v_j_2226_, v_k_2227_);
lean_dec_ref(v_k_2227_);
return v_res_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0(lean_object* v_x_2231_){
_start:
{
if (lean_obj_tag(v_x_2231_) == 0)
{
lean_object* v___x_2232_; 
v___x_2232_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_2232_;
}
else
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(v_x_2231_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2250_; 
v_a_2242_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2250_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2250_ == 0)
{
v___x_2244_ = v___x_2233_;
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2233_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2250_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2246_, 0, v_a_2242_);
if (v_isShared_2245_ == 0)
{
lean_ctor_set(v___x_2244_, 0, v___x_2246_);
v___x_2248_ = v___x_2244_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(lean_object* v_j_2251_, lean_object* v_k_2252_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = l_Lean_Json_getObjValD(v_j_2251_, v_k_2252_);
v___x_2254_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0_spec__0(v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0___boxed(lean_object* v_j_2255_, lean_object* v_k_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(v_j_2255_, v_k_2256_);
lean_dec_ref(v_k_2256_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2(lean_object* v_x_2260_){
_start:
{
if (lean_obj_tag(v_x_2260_) == 0)
{
lean_object* v___x_2261_; 
v___x_2261_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2___closed__0));
return v___x_2261_;
}
else
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Lsp_instFromJsonCompletionOptions_fromJson(v_x_2260_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2262_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_dec(v___x_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
else
{
lean_object* v_a_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2279_; 
v_a_2271_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2273_ = v___x_2262_;
v_isShared_2274_ = v_isSharedCheck_2279_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_a_2271_);
lean_dec(v___x_2262_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2279_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v___x_2275_; lean_object* v___x_2277_; 
v___x_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2275_, 0, v_a_2271_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2275_);
v___x_2277_ = v___x_2273_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(lean_object* v_j_2280_, lean_object* v_k_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2282_ = l_Lean_Json_getObjValD(v_j_2280_, v_k_2281_);
v___x_2283_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1_spec__2(v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1___boxed(lean_object* v_j_2284_, lean_object* v_k_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(v_j_2284_, v_k_2285_);
lean_dec_ref(v_k_2285_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7_spec__14(lean_object* v_x_2287_){
_start:
{
if (lean_obj_tag(v_x_2287_) == 0)
{
lean_object* v___x_2288_; 
v___x_2288_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_2288_;
}
else
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Lsp_instFromJsonDocumentColorOptions_fromJson(v_x_2287_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2306_; 
v_a_2298_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2300_ = v___x_2289_;
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2289_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v_a_2298_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2302_);
v___x_2304_ = v___x_2300_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(lean_object* v_j_2307_, lean_object* v_k_2308_){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = l_Lean_Json_getObjValD(v_j_2307_, v_k_2308_);
v___x_2310_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7_spec__14(v___x_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7___boxed(lean_object* v_j_2311_, lean_object* v_k_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(v_j_2311_, v_k_2312_);
lean_dec_ref(v_k_2312_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6(lean_object* v_x_2316_){
_start:
{
if (lean_obj_tag(v_x_2316_) == 0)
{
lean_object* v___x_2317_; 
v___x_2317_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6___closed__0));
return v___x_2317_;
}
else
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_Lsp_instFromJsonSemanticTokensOptions_fromJson(v_x_2316_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2318_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2318_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2335_; 
v_a_2327_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2329_ = v___x_2318_;
v_isShared_2330_ = v_isSharedCheck_2335_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2318_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2335_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_a_2327_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2331_);
v___x_2333_ = v___x_2329_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(lean_object* v_j_2336_, lean_object* v_k_2337_){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = l_Lean_Json_getObjValD(v_j_2336_, v_k_2337_);
v___x_2339_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3_spec__6(v___x_2338_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3___boxed(lean_object* v_j_2340_, lean_object* v_k_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(v_j_2340_, v_k_2341_);
lean_dec_ref(v_k_2341_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2_spec__4(lean_object* v_x_2343_){
_start:
{
if (lean_obj_tag(v_x_2343_) == 0)
{
lean_object* v___x_2344_; 
v___x_2344_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson_spec__0_spec__0___closed__0));
return v___x_2344_;
}
else
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Lsp_instFromJsonRenameOptions_fromJson(v_x_2343_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2362_; 
v_a_2354_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2356_ = v___x_2345_;
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2345_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v_a_2354_);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2358_);
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(lean_object* v_j_2363_, lean_object* v_k_2364_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = l_Lean_Json_getObjValD(v_j_2363_, v_k_2364_);
v___x_2366_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2_spec__4(v___x_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2___boxed(lean_object* v_j_2367_, lean_object* v_k_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(v_j_2367_, v_k_2368_);
lean_dec_ref(v_k_2368_);
return v_res_2369_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2(void){
_start:
{
uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = 1;
v___x_2376_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__1));
v___x_2377_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2376_, v___x_2375_);
return v___x_2377_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__5));
v___x_2379_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__2);
v___x_2380_ = lean_string_append(v___x_2379_, v___x_2378_);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6(void){
_start:
{
uint8_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = 1;
v___x_2385_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__5));
v___x_2386_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2385_, v___x_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__6);
v___x_2388_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2389_ = lean_string_append(v___x_2388_, v___x_2387_);
return v___x_2389_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2390_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2391_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__7);
v___x_2392_ = lean_string_append(v___x_2391_, v___x_2390_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11(void){
_start:
{
uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2396_ = 1;
v___x_2397_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__10));
v___x_2398_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2397_, v___x_2396_);
return v___x_2398_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2399_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__11);
v___x_2400_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2401_ = lean_string_append(v___x_2400_, v___x_2399_);
return v___x_2401_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2403_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__12);
v___x_2404_ = lean_string_append(v___x_2403_, v___x_2402_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15(void){
_start:
{
uint8_t v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2407_ = 1;
v___x_2408_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__14));
v___x_2409_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2408_, v___x_2407_);
return v___x_2409_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__15);
v___x_2411_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2412_ = lean_string_append(v___x_2411_, v___x_2410_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2414_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__16);
v___x_2415_ = lean_string_append(v___x_2414_, v___x_2413_);
return v___x_2415_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19(void){
_start:
{
uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2418_ = 1;
v___x_2419_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__18));
v___x_2420_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2419_, v___x_2418_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2421_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__19);
v___x_2422_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2423_ = lean_string_append(v___x_2422_, v___x_2421_);
return v___x_2423_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2424_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2425_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__20);
v___x_2426_ = lean_string_append(v___x_2425_, v___x_2424_);
return v___x_2426_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23(void){
_start:
{
uint8_t v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = 1;
v___x_2430_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__22));
v___x_2431_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2430_, v___x_2429_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24(void){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2432_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__23);
v___x_2433_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2434_ = lean_string_append(v___x_2433_, v___x_2432_);
return v___x_2434_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25(void){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2435_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2436_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__24);
v___x_2437_ = lean_string_append(v___x_2436_, v___x_2435_);
return v___x_2437_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27(void){
_start:
{
uint8_t v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = 1;
v___x_2441_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__26));
v___x_2442_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2441_, v___x_2440_);
return v___x_2442_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2443_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__27);
v___x_2444_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2445_ = lean_string_append(v___x_2444_, v___x_2443_);
return v___x_2445_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2447_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__28);
v___x_2448_ = lean_string_append(v___x_2447_, v___x_2446_);
return v___x_2448_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31(void){
_start:
{
uint8_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = 1;
v___x_2452_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__30));
v___x_2453_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2452_, v___x_2451_);
return v___x_2453_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2454_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__31);
v___x_2455_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2456_ = lean_string_append(v___x_2455_, v___x_2454_);
return v___x_2456_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2458_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__32);
v___x_2459_ = lean_string_append(v___x_2458_, v___x_2457_);
return v___x_2459_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35(void){
_start:
{
uint8_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = 1;
v___x_2463_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__34));
v___x_2464_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2463_, v___x_2462_);
return v___x_2464_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__35);
v___x_2466_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2467_ = lean_string_append(v___x_2466_, v___x_2465_);
return v___x_2467_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2469_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__36);
v___x_2470_ = lean_string_append(v___x_2469_, v___x_2468_);
return v___x_2470_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39(void){
_start:
{
uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2473_ = 1;
v___x_2474_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__38));
v___x_2475_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2474_, v___x_2473_);
return v___x_2475_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__39);
v___x_2477_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2478_ = lean_string_append(v___x_2477_, v___x_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2480_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__40);
v___x_2481_ = lean_string_append(v___x_2480_, v___x_2479_);
return v___x_2481_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43(void){
_start:
{
uint8_t v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2484_ = 1;
v___x_2485_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__42));
v___x_2486_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2485_, v___x_2484_);
return v___x_2486_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__43);
v___x_2488_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2489_ = lean_string_append(v___x_2488_, v___x_2487_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2491_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__44);
v___x_2492_ = lean_string_append(v___x_2491_, v___x_2490_);
return v___x_2492_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48(void){
_start:
{
uint8_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = 1;
v___x_2497_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__47));
v___x_2498_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2497_, v___x_2496_);
return v___x_2498_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__48);
v___x_2500_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2501_ = lean_string_append(v___x_2500_, v___x_2499_);
return v___x_2501_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2503_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__49);
v___x_2504_ = lean_string_append(v___x_2503_, v___x_2502_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52(void){
_start:
{
uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = 1;
v___x_2508_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__51));
v___x_2509_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2508_, v___x_2507_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__52);
v___x_2511_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2512_ = lean_string_append(v___x_2511_, v___x_2510_);
return v___x_2512_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54(void){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2514_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__53);
v___x_2515_ = lean_string_append(v___x_2514_, v___x_2513_);
return v___x_2515_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56(void){
_start:
{
uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = 1;
v___x_2519_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__55));
v___x_2520_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2519_, v___x_2518_);
return v___x_2520_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2521_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__56);
v___x_2522_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2523_ = lean_string_append(v___x_2522_, v___x_2521_);
return v___x_2523_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2525_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__57);
v___x_2526_ = lean_string_append(v___x_2525_, v___x_2524_);
return v___x_2526_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61(void){
_start:
{
uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = 1;
v___x_2531_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__60));
v___x_2532_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2531_, v___x_2530_);
return v___x_2532_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__61);
v___x_2534_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2535_ = lean_string_append(v___x_2534_, v___x_2533_);
return v___x_2535_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2537_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__62);
v___x_2538_ = lean_string_append(v___x_2537_, v___x_2536_);
return v___x_2538_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66(void){
_start:
{
uint8_t v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = 1;
v___x_2543_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__65));
v___x_2544_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2543_, v___x_2542_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__66);
v___x_2546_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2547_ = lean_string_append(v___x_2546_, v___x_2545_);
return v___x_2547_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2549_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__67);
v___x_2550_ = lean_string_append(v___x_2549_, v___x_2548_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71(void){
_start:
{
uint8_t v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = 1;
v___x_2555_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__70));
v___x_2556_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2555_, v___x_2554_);
return v___x_2556_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__71);
v___x_2558_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2559_ = lean_string_append(v___x_2558_, v___x_2557_);
return v___x_2559_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2561_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__72);
v___x_2562_ = lean_string_append(v___x_2561_, v___x_2560_);
return v___x_2562_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76(void){
_start:
{
uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = 1;
v___x_2567_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__75));
v___x_2568_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2567_, v___x_2566_);
return v___x_2568_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77(void){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2569_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__76);
v___x_2570_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2571_ = lean_string_append(v___x_2570_, v___x_2569_);
return v___x_2571_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2573_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__77);
v___x_2574_ = lean_string_append(v___x_2573_, v___x_2572_);
return v___x_2574_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81(void){
_start:
{
uint8_t v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = 1;
v___x_2579_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__80));
v___x_2580_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2579_, v___x_2578_);
return v___x_2580_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__81);
v___x_2582_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2583_ = lean_string_append(v___x_2582_, v___x_2581_);
return v___x_2583_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2585_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__82);
v___x_2586_ = lean_string_append(v___x_2585_, v___x_2584_);
return v___x_2586_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86(void){
_start:
{
uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = 1;
v___x_2591_ = ((lean_object*)(l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__85));
v___x_2592_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2591_, v___x_2590_);
return v___x_2592_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__86);
v___x_2594_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__3);
v___x_2595_ = lean_string_append(v___x_2594_, v___x_2593_);
return v___x_2595_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = ((lean_object*)(l_Lean_Lsp_instFromJsonCompletionItemCapabilities_fromJson___closed__11));
v___x_2597_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__87);
v___x_2598_ = lean_string_append(v___x_2597_, v___x_2596_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonServerCapabilities_fromJson(lean_object* v_json_2599_){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__0));
lean_inc(v_json_2599_);
v___x_2601_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__0(v_json_2599_, v___x_2600_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_json_2599_);
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
v___x_2606_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__8);
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
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v_json_2599_);
v_a_2612_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2601_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2601_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set_tag(v___x_2614_, 0);
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_a_2620_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2620_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2621_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__1));
lean_inc(v_json_2599_);
v___x_2622_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__1(v_json_2599_, v___x_2621_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2632_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2627_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__13);
v___x_2628_ = lean_string_append(v___x_2627_, v_a_2623_);
lean_dec(v_a_2623_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2628_);
v___x_2630_ = v___x_2625_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
else
{
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2633_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2622_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2622_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
lean_ctor_set_tag(v___x_2635_, 0);
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v_a_2641_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2622_, 1);
v___x_2642_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__2));
lean_inc(v_json_2599_);
v___x_2643_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2599_, v___x_2642_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2646_ = v___x_2643_;
v_isShared_2647_ = v_isSharedCheck_2653_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___x_2643_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2653_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2648_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__17);
v___x_2649_ = lean_string_append(v___x_2648_, v_a_2644_);
lean_dec(v_a_2644_);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 0, v___x_2649_);
v___x_2651_ = v___x_2646_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
else
{
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2654_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2643_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2643_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
lean_ctor_set_tag(v___x_2656_, 0);
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v_a_2662_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2663_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__3));
lean_inc(v_json_2599_);
v___x_2664_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2599_, v___x_2663_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2674_; 
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2674_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2674_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2669_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__21);
v___x_2670_ = lean_string_append(v___x_2669_, v_a_2665_);
lean_dec(v_a_2665_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2670_);
v___x_2672_ = v___x_2667_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
else
{
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2675_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2664_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2664_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 0);
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v_a_2683_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2684_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__4));
lean_inc(v_json_2599_);
v___x_2685_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2599_, v___x_2684_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2695_; 
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2695_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2695_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2690_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__25);
v___x_2691_ = lean_string_append(v___x_2690_, v_a_2686_);
lean_dec(v_a_2686_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2691_);
v___x_2693_ = v___x_2688_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
else
{
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2696_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2685_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2685_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
lean_ctor_set_tag(v___x_2698_, 0);
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v_a_2704_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2685_, 1);
v___x_2705_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__5));
lean_inc(v_json_2599_);
v___x_2706_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2599_, v___x_2705_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2709_ = v___x_2706_;
v_isShared_2710_ = v_isSharedCheck_2716_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2716_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2711_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__29);
v___x_2712_ = lean_string_append(v___x_2711_, v_a_2707_);
lean_dec(v_a_2707_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2712_);
v___x_2714_ = v___x_2709_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
else
{
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2717_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2706_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2706_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set_tag(v___x_2719_, 0);
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v_a_2725_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2706_, 1);
v___x_2726_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__6));
lean_inc(v_json_2599_);
v___x_2727_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2599_, v___x_2726_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2737_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2737_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2732_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__33);
v___x_2733_ = lean_string_append(v___x_2732_, v_a_2728_);
lean_dec(v_a_2728_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2733_);
v___x_2735_ = v___x_2730_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
else
{
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2738_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2727_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2727_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
lean_ctor_set_tag(v___x_2740_, 0);
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v_a_2746_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2727_, 1);
v___x_2747_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__7));
lean_inc(v_json_2599_);
v___x_2748_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2599_, v___x_2747_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2758_; 
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2758_ == 0)
{
v___x_2751_ = v___x_2748_;
v_isShared_2752_ = v_isSharedCheck_2758_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2758_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2756_; 
v___x_2753_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__37);
v___x_2754_ = lean_string_append(v___x_2753_, v_a_2749_);
lean_dec(v_a_2749_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v___x_2754_);
v___x_2756_ = v___x_2751_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
return v___x_2756_;
}
}
}
else
{
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2759_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2748_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2748_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
lean_ctor_set_tag(v___x_2761_, 0);
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v_a_2767_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2768_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__8));
lean_inc(v_json_2599_);
v___x_2769_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2599_, v___x_2768_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2779_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2779_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2774_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__41);
v___x_2775_ = lean_string_append(v___x_2774_, v_a_2770_);
lean_dec(v_a_2770_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 0, v___x_2775_);
v___x_2777_ = v___x_2772_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
else
{
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2780_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2769_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2769_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set_tag(v___x_2782_, 0);
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_a_2788_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2769_, 1);
v___x_2789_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__9));
lean_inc(v_json_2599_);
v___x_2790_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2599_, v___x_2789_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2800_; 
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2800_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2800_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2795_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__45);
v___x_2796_ = lean_string_append(v___x_2795_, v_a_2791_);
lean_dec(v_a_2791_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2796_);
v___x_2798_ = v___x_2793_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
else
{
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2801_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2790_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2790_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set_tag(v___x_2803_, 0);
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2809_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2790_, 1);
v___x_2810_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__10));
lean_inc(v_json_2599_);
v___x_2811_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__2(v_json_2599_, v___x_2810_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2821_; 
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2814_ = v___x_2811_;
v_isShared_2815_ = v_isSharedCheck_2821_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2811_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2821_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2819_; 
v___x_2816_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__50);
v___x_2817_ = lean_string_append(v___x_2816_, v_a_2812_);
lean_dec(v_a_2812_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v___x_2817_);
v___x_2819_ = v___x_2814_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2817_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
else
{
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2822_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2811_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2811_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
lean_ctor_set_tag(v___x_2824_, 0);
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
else
{
lean_object* v_a_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; 
v_a_2830_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2811_, 1);
v___x_2831_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__11));
lean_inc(v_json_2599_);
v___x_2832_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2599_, v___x_2831_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2835_ = v___x_2832_;
v_isShared_2836_ = v_isSharedCheck_2842_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2842_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2837_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__54);
v___x_2838_ = lean_string_append(v___x_2837_, v_a_2833_);
lean_dec(v_a_2833_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2838_);
v___x_2840_ = v___x_2835_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
else
{
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2843_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2832_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2832_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 0);
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2851_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2852_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__12));
lean_inc(v_json_2599_);
v___x_2853_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonShowDocumentClientCapabilities_fromJson_spec__0(v_json_2599_, v___x_2852_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2854_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2856_ = v___x_2853_;
v_isShared_2857_ = v_isSharedCheck_2863_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2853_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2863_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2858_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__58);
v___x_2859_ = lean_string_append(v___x_2858_, v_a_2854_);
lean_dec(v_a_2854_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2859_);
v___x_2861_ = v___x_2856_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
else
{
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2864_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2853_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2853_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set_tag(v___x_2866_, 0);
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v_a_2872_ = lean_ctor_get(v___x_2853_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2853_, 1);
v___x_2873_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__13));
lean_inc(v_json_2599_);
v___x_2874_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__3(v_json_2599_, v___x_2873_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2884_; 
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_2884_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2884_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2879_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__63);
v___x_2880_ = lean_string_append(v___x_2879_, v_a_2875_);
lean_dec(v_a_2875_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2880_);
v___x_2882_ = v___x_2877_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
else
{
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2885_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2874_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2874_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
lean_ctor_set_tag(v___x_2887_, 0);
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_a_2893_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2894_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__14));
lean_inc(v_json_2599_);
v___x_2895_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__4(v_json_2599_, v___x_2894_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v_a_2893_);
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_2905_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2905_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
v___x_2900_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__68);
v___x_2901_ = lean_string_append(v___x_2900_, v_a_2896_);
lean_dec(v_a_2896_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2901_);
v___x_2903_ = v___x_2898_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
else
{
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_a_2893_);
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2906_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2895_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2895_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set_tag(v___x_2908_, 0);
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v_a_2914_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2895_, 1);
v___x_2915_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__15));
lean_inc(v_json_2599_);
v___x_2916_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__5(v_json_2599_, v___x_2915_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v_a_2914_);
lean_dec(v_a_2893_);
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2919_ = v___x_2916_;
v_isShared_2920_ = v_isSharedCheck_2926_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2916_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2926_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
v___x_2921_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__73);
v___x_2922_ = lean_string_append(v___x_2921_, v_a_2917_);
lean_dec(v_a_2917_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v___x_2922_);
v___x_2924_ = v___x_2919_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
else
{
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v_a_2914_);
lean_dec(v_a_2893_);
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2927_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2916_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2916_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
lean_ctor_set_tag(v___x_2929_, 0);
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v_a_2935_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2916_, 1);
v___x_2936_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__16));
lean_inc(v_json_2599_);
v___x_2937_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__6(v_json_2599_, v___x_2936_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v_a_2935_);
lean_dec(v_a_2914_);
lean_dec(v_a_2893_);
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2940_ = v___x_2937_;
v_isShared_2941_ = v_isSharedCheck_2947_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2937_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2947_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2945_; 
v___x_2942_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__78);
v___x_2943_ = lean_string_append(v___x_2942_, v_a_2938_);
lean_dec(v_a_2938_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v___x_2943_);
v___x_2945_ = v___x_2940_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
else
{
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec(v_a_2935_);
lean_dec(v_a_2914_);
lean_dec(v_a_2893_);
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2948_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2937_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2937_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set_tag(v___x_2950_, 0);
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_a_2956_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2937_, 1);
v___x_2957_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__17));
lean_inc(v_json_2599_);
v___x_2958_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__7(v_json_2599_, v___x_2957_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2968_; 
lean_dec(v_a_2956_);
lean_dec(v_a_2935_);
lean_dec(v_a_2914_);
lean_dec(v_a_2893_);
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2961_ = v___x_2958_;
v_isShared_2962_ = v_isSharedCheck_2968_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2968_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2966_; 
v___x_2963_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__83);
v___x_2964_ = lean_string_append(v___x_2963_, v_a_2959_);
lean_dec(v_a_2959_);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 0, v___x_2964_);
v___x_2966_ = v___x_2961_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
else
{
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec(v_a_2956_);
lean_dec(v_a_2935_);
lean_dec(v_a_2914_);
lean_dec(v_a_2893_);
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
lean_dec(v_json_2599_);
v_a_2969_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2958_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2958_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
lean_ctor_set_tag(v___x_2971_, 0);
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_a_2977_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2958_, 1);
v___x_2978_ = ((lean_object*)(l_Lean_Lsp_instToJsonServerCapabilities_toJson___closed__18));
v___x_2979_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonServerCapabilities_fromJson_spec__8(v_json_2599_, v___x_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2989_; 
lean_dec(v_a_2977_);
lean_dec(v_a_2956_);
lean_dec(v_a_2935_);
lean_dec(v_a_2914_);
lean_dec(v_a_2893_);
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2982_ = v___x_2979_;
v_isShared_2983_ = v_isSharedCheck_2989_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2979_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2989_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2987_; 
v___x_2984_ = lean_obj_once(&l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88, &l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88_once, _init_l_Lean_Lsp_instFromJsonServerCapabilities_fromJson___closed__88);
v___x_2985_ = lean_string_append(v___x_2984_, v_a_2980_);
lean_dec(v_a_2980_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 0, v___x_2985_);
v___x_2987_ = v___x_2982_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v___x_2985_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
else
{
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec(v_a_2977_);
lean_dec(v_a_2956_);
lean_dec(v_a_2935_);
lean_dec(v_a_2914_);
lean_dec(v_a_2893_);
lean_dec(v_a_2872_);
lean_dec(v_a_2851_);
lean_dec(v_a_2830_);
lean_dec(v_a_2809_);
lean_dec(v_a_2788_);
lean_dec(v_a_2767_);
lean_dec(v_a_2746_);
lean_dec(v_a_2725_);
lean_dec(v_a_2704_);
lean_dec(v_a_2683_);
lean_dec(v_a_2662_);
lean_dec(v_a_2641_);
lean_dec(v_a_2620_);
v_a_2990_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2979_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2979_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
lean_ctor_set_tag(v___x_2992_, 0);
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3016_; 
v_a_2998_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3000_ = v___x_2979_;
v_isShared_3001_ = v_isSharedCheck_3016_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2979_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3016_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; uint8_t v___x_3003_; uint8_t v___x_3004_; uint8_t v___x_3005_; uint8_t v___x_3006_; uint8_t v___x_3007_; uint8_t v___x_3008_; uint8_t v___x_3009_; uint8_t v___x_3010_; uint8_t v___x_3011_; uint8_t v___x_3012_; lean_object* v___x_3014_; 
v___x_3002_ = lean_alloc_ctor(0, 9, 10);
lean_ctor_set(v___x_3002_, 0, v_a_2620_);
lean_ctor_set(v___x_3002_, 1, v_a_2641_);
lean_ctor_set(v___x_3002_, 2, v_a_2830_);
lean_ctor_set(v___x_3002_, 3, v_a_2893_);
lean_ctor_set(v___x_3002_, 4, v_a_2914_);
lean_ctor_set(v___x_3002_, 5, v_a_2935_);
lean_ctor_set(v___x_3002_, 6, v_a_2956_);
lean_ctor_set(v___x_3002_, 7, v_a_2977_);
lean_ctor_set(v___x_3002_, 8, v_a_2998_);
v___x_3003_ = lean_unbox(v_a_2662_);
lean_dec(v_a_2662_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*9, v___x_3003_);
v___x_3004_ = lean_unbox(v_a_2683_);
lean_dec(v_a_2683_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*9 + 1, v___x_3004_);
v___x_3005_ = lean_unbox(v_a_2704_);
lean_dec(v_a_2704_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*9 + 2, v___x_3005_);
v___x_3006_ = lean_unbox(v_a_2725_);
lean_dec(v_a_2725_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*9 + 3, v___x_3006_);
v___x_3007_ = lean_unbox(v_a_2746_);
lean_dec(v_a_2746_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*9 + 4, v___x_3007_);
v___x_3008_ = lean_unbox(v_a_2767_);
lean_dec(v_a_2767_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*9 + 5, v___x_3008_);
v___x_3009_ = lean_unbox(v_a_2788_);
lean_dec(v_a_2788_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*9 + 6, v___x_3009_);
v___x_3010_ = lean_unbox(v_a_2809_);
lean_dec(v_a_2809_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*9 + 7, v___x_3010_);
v___x_3011_ = lean_unbox(v_a_2851_);
lean_dec(v_a_2851_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*9 + 8, v___x_3011_);
v___x_3012_ = lean_unbox(v_a_2872_);
lean_dec(v_a_2872_);
lean_ctor_set_uint8(v___x_3002_, sizeof(void*)*9 + 9, v___x_3012_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3002_);
v___x_3014_ = v___x_3000_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3002_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
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

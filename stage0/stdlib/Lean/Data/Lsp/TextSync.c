// Lean compiler output
// Module: Lean.Data.Lsp.TextSync
// Imports: public import Lean.Data.Lsp.Basic
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
lean_object* l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_JsonNumber_fromNat(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_Json_getBool_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonRange_fromJson(lean_object*);
lean_object* l_Lean_Json_getStr_x3f(lean_object*);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Json_getNat_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(lean_object*);
lean_object* l_Lean_Lsp_instToJsonTextDocumentItem_toJson(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "unknown TextDocumentSyncKind"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncKind___closed__0_value;
static lean_once_cell_t l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0;
static lean_once_cell_t l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1;
static lean_once_cell_t l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2;
static lean_once_cell_t l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3;
static lean_once_cell_t l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4;
static lean_once_cell_t l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncKind___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "textDocument"};
static const lean_object* l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0_value;
static const lean_array_object l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDidOpenTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instToJsonDidOpenTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Lsp"};
static const lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "DidOpenTextDocumentParams"};
static const lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(97, 184, 77, 155, 136, 131, 169, 24)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(215, 223, 21, 223, 122, 31, 128, 254)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "expected JSON array, got '"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0_value;
static const lean_string_object l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "documentSelector"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "TextDocumentChangeRegistrationOptions"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(134, 116, 66, 201, 97, 133, 37, 241)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4;
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "documentSelector\?"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__5_value),LEAN_SCALAR_PTR_LITERAL(91, 242, 138, 38, 210, 232, 124, 203)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9;
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "syncKind"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10_value),LEAN_SCALAR_PTR_LITERAL(234, 21, 134, 62, 235, 164, 85, 135)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonRange_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Json_getStr_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1_value;
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__1_value),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__0_value)} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___lam__0(lean_object*);
static const lean_closure_object l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0 = (const lean_object*)&l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson = (const lean_object*)&l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "contentChanges"};
static const lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instToJsonDidChangeTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "DidChangeTextDocumentParams"};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 72, 203, 218, 154, 80, 141, 249)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(119, 65, 175, 11, 18, 214, 36, 239)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDidSaveTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instToJsonDidSaveTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "DidSaveTextDocumentParams"};
static const lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 170, 20, 102, 195, 2, 175, 174)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5;
static const lean_string_object l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "text\?"};
static const lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__6_value),LEAN_SCALAR_PTR_LITERAL(119, 11, 87, 192, 206, 66, 232, 28)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "includeText"};
static const lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonSaveOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonSaveOptions_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonSaveOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonSaveOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonSaveOptions = (const lean_object*)&l_Lean_Lsp_instToJsonSaveOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "SaveOptions"};
static const lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 145, 122, 153, 142, 193, 12, 135)}};
static const lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 230, 220, 117, 153, 35, 49, 211)}};
static const lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonSaveOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonSaveOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonSaveOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonSaveOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonSaveOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonSaveOptions___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidCloseTextDocumentParams_toJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonDidCloseTextDocumentParams_toJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonDidCloseTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instToJsonDidCloseTextDocumentParams___closed__0_value;
static const lean_string_object l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "DidCloseTextDocumentParams"};
static const lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 113, 132, 107, 175, 106, 71, 4)}};
static const lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4;
static lean_once_cell_t l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams = (const lean_object*)&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "openClose"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "change"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "willSave"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "willSaveWaitUntil"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3_value;
static const lean_string_object l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "save"};
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___boxed(lean_object*);
static const lean_closure_object l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions = (const lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions___closed__0_value;
static const lean_ctor_object l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "TextDocumentSyncOptions"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_0),((lean_object*)&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 104, 224, 237, 184, 44, 1, 94)}};
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value_aux_1),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 117, 158, 168, 238, 135, 208, 68)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 9, 47, 109, 206, 249, 195, 126)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1_value),LEAN_SCALAR_PTR_LITERAL(125, 120, 133, 160, 129, 235, 229, 190)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2_value),LEAN_SCALAR_PTR_LITERAL(84, 40, 145, 117, 81, 143, 125, 178)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3_value),LEAN_SCALAR_PTR_LITERAL(122, 131, 138, 36, 151, 11, 76, 221)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19;
static const lean_string_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "save\?"};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20_value;
static const lean_ctor_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__20_value),LEAN_SCALAR_PTR_LITERAL(172, 42, 97, 221, 226, 169, 49, 167)}};
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21_value;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23;
static lean_once_cell_t l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24;
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(lean_object*);
static const lean_closure_object l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0 = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions = (const lean_object*)&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions___closed__0_value;
lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Lsp_TextDocumentSyncKind_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Lsp_TextDocumentSyncKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Lsp_TextDocumentSyncKind_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(lean_object* v_none_24_){
_start:
{
lean_inc(v_none_24_);
return v_none_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg___boxed(lean_object* v_none_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim___redArg(v_none_25_);
lean_dec(v_none_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_none_30_){
_start:
{
lean_inc(v_none_30_);
return v_none_30_;
}
}
LEAN_EXPORT void l_Lean_Lsp_TextDocumentSyncKind_none_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_none_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim(lean_box(0), v_t_28_, lean_box(0), v_none_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_none_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_none_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Lsp_TextDocumentSyncKind_none_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_none_35_);
lean_dec(v_none_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(lean_object* v_full_38_){
_start:
{
lean_inc(v_full_38_);
return v_full_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg___boxed(lean_object* v_full_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim___redArg(v_full_39_);
lean_dec(v_full_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_full_44_){
_start:
{
lean_inc(v_full_44_);
return v_full_44_;
}
}
LEAN_EXPORT void l_Lean_Lsp_TextDocumentSyncKind_full_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_full_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim(lean_box(0), v_t_42_, lean_box(0), v_full_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_full_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_full_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Lsp_TextDocumentSyncKind_full_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_full_49_);
lean_dec(v_full_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(lean_object* v_incremental_52_){
_start:
{
lean_inc(v_incremental_52_);
return v_incremental_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg___boxed(lean_object* v_incremental_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___redArg(v_incremental_53_);
lean_dec(v_incremental_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_incremental_58_){
_start:
{
lean_inc(v_incremental_58_);
return v_incremental_58_;
}
}
LEAN_EXPORT void l_Lean_Lsp_TextDocumentSyncKind_incremental_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_incremental_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(lean_box(0), v_t_56_, lean_box(0), v_incremental_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentSyncKind_incremental_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_incremental_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Lsp_TextDocumentSyncKind_incremental_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_incremental_63_);
lean_dec(v_incremental_63_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0(lean_object* v_j_78_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Json_getNat_x3f(v_j_78_);
if (lean_obj_tag(v___x_81_) == 1)
{
lean_object* v_a_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_a_82_);
lean_dec_ref_known(v___x_81_, 1);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_nat_dec_eq(v_a_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_dec_eq(v_a_82_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(2u);
v___x_88_ = lean_nat_dec_eq(v_a_82_, v___x_87_);
lean_dec(v_a_82_);
if (v___x_88_ == 0)
{
goto v___jp_79_;
}
else
{
lean_object* v___x_89_; 
v___x_89_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2));
return v___x_89_;
}
}
else
{
lean_object* v___x_90_; 
lean_dec(v_a_82_);
v___x_90_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3));
return v___x_90_;
}
}
else
{
lean_object* v___x_91_; 
lean_dec(v_a_82_);
v___x_91_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4));
return v___x_91_;
}
}
else
{
lean_dec_ref(v___x_81_);
goto v___jp_79_;
}
v___jp_79_:
{
lean_object* v___x_80_; 
v___x_80_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1));
return v___x_80_;
}
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = l_Lean_JsonNumber_fromNat(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__0);
v___x_97_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(1u);
v___x_99_ = l_Lean_JsonNumber_fromNat(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__2);
v___x_101_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(2u);
v___x_103_ = l_Lean_JsonNumber_fromNat(v___x_102_);
return v___x_103_;
}
}
static lean_object* _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__4);
v___x_105_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(uint8_t v_x_106_){
_start:
{
switch(v_x_106_)
{
case 0:
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1);
return v___x_107_;
}
case 1:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3);
return v___x_108_;
}
default: 
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5);
return v___x_109_;
}
}
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_106_ = stack[0].m_num;
lean_object* v_res_110_;
v_res_110_ = l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(v_x_106_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___boxed(lean_object* v_x_111_){
_start:
{
uint8_t v_x_81__boxed_112_; lean_object* v_res_113_; 
v_x_81__boxed_112_ = lean_unbox(v_x_111_);
v_res_113_ = l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0(v_x_81__boxed_112_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(lean_object* v_a_116_, lean_object* v_a_117_){
_start:
{
if (lean_obj_tag(v_a_116_) == 0)
{
lean_object* v___x_118_; 
v___x_118_ = lean_array_to_list(v_a_117_);
return v___x_118_;
}
else
{
lean_object* v_head_119_; lean_object* v_tail_120_; lean_object* v___x_121_; 
v_head_119_ = lean_ctor_get(v_a_116_, 0);
lean_inc(v_head_119_);
v_tail_120_ = lean_ctor_get(v_a_116_, 1);
lean_inc(v_tail_120_);
lean_dec_ref_known(v_a_116_, 2);
v___x_121_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_117_, v_head_119_);
v_a_116_ = v_tail_120_;
v_a_117_ = v___x_121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson(lean_object* v_x_126_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_127_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_128_ = l_Lean_Lsp_instToJsonTextDocumentItem_toJson(v_x_126_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = lean_box(0);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_130_);
v___x_133_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_134_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_132_, v___x_133_);
v___x_135_ = l_Lean_Json_mkObj(v___x_134_);
lean_dec(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(lean_object* v_j_138_, lean_object* v_k_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = l_Lean_Json_getObjValD(v_j_138_, v_k_139_);
v___x_141_ = l_Lean_Lsp_instFromJsonTextDocumentItem_fromJson(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_142_, lean_object* v_k_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(v_j_142_, v_k_143_);
lean_dec_ref(v_k_143_);
return v_res_144_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4(void){
_start:
{
uint8_t v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = 1;
v___x_153_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__3));
v___x_154_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_153_, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_157_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__4);
v___x_158_ = lean_string_append(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = 1;
v___x_162_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__7));
v___x_163_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_165_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__6);
v___x_166_ = lean_string_append(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_169_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__9);
v___x_170_ = lean_string_append(v___x_169_, v___x_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson(lean_object* v_json_171_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_173_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson_spec__0(v_json_171_, v___x_172_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_183_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_183_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_183_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_183_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_178_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__11);
v___x_179_ = lean_string_append(v___x_178_, v_a_174_);
lean_dec(v_a_174_);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_179_);
v___x_181_ = v___x_176_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
v_a_184_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_173_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_173_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 0);
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_192_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_173_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_173_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(lean_object* v_j_202_, lean_object* v_k_203_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = l_Lean_Json_getObjValD(v_j_202_, v_k_203_);
v___x_207_ = l_Lean_Json_getNat_x3f(v___x_206_);
if (lean_obj_tag(v___x_207_) == 1)
{
lean_object* v_a_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_nat_dec_eq(v_a_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_dec_eq(v_a_208_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(2u);
v___x_214_ = lean_nat_dec_eq(v_a_208_, v___x_213_);
lean_dec(v_a_208_);
if (v___x_214_ == 0)
{
goto v___jp_204_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__2));
return v___x_215_;
}
}
else
{
lean_object* v___x_216_; 
lean_dec(v_a_208_);
v___x_216_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__3));
return v___x_216_;
}
}
else
{
lean_object* v___x_217_; 
lean_dec(v_a_208_);
v___x_217_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__4));
return v___x_217_;
}
}
else
{
lean_dec_ref(v___x_207_);
goto v___jp_204_;
}
v___jp_204_:
{
lean_object* v___x_205_; 
v___x_205_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncKind___lam__0___closed__1));
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1___boxed(lean_object* v_j_218_, lean_object* v_k_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_j_218_, v_k_219_);
lean_dec_ref(v_k_219_);
return v_res_220_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(size_t v_sz_221_, size_t v_i_222_, lean_object* v_bs_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = lean_usize_dec_lt(v_i_222_, v_sz_221_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v_bs_223_);
return v___x_225_;
}
else
{
lean_object* v_v_226_; lean_object* v___x_227_; 
v_v_226_ = lean_array_uget_borrowed(v_bs_223_, v_i_222_);
lean_inc(v_v_226_);
v___x_227_ = l_Lean_Lsp_instFromJsonDocumentFilter_fromJson(v_v_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec_ref(v_bs_223_);
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_237_; lean_object* v_bs_x27_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v___x_241_; 
v_a_236_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_236_);
lean_dec_ref_known(v___x_227_, 1);
v___x_237_ = lean_unsigned_to_nat(0u);
v_bs_x27_238_ = lean_array_uset(v_bs_223_, v_i_222_, v___x_237_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_add(v_i_222_, v___x_239_);
v___x_241_ = lean_array_uset(v_bs_x27_238_, v_i_222_, v_a_236_);
v_i_222_ = v___x_240_;
v_bs_223_ = v___x_241_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_221_ = stack[0].m_num;
size_t v_i_222_ = stack[1].m_num;
lean_object* v_bs_223_ = stack[2].m_obj;
lean_object* v_res_243_;
v_res_243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_221_, v_i_222_, v_bs_223_);
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_sz_244_, lean_object* v_i_245_, lean_object* v_bs_246_){
_start:
{
size_t v_sz_boxed_247_; size_t v_i_boxed_248_; lean_object* v_res_249_; 
v_sz_boxed_247_ = lean_unbox_usize(v_sz_244_);
lean_dec(v_sz_244_);
v_i_boxed_248_ = lean_unbox_usize(v_i_245_);
lean_dec(v_i_245_);
v_res_249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_boxed_247_, v_i_boxed_248_, v_bs_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(lean_object* v_x_252_){
_start:
{
if (lean_obj_tag(v_x_252_) == 4)
{
lean_object* v_elems_253_; size_t v_sz_254_; size_t v___x_255_; lean_object* v___x_256_; 
v_elems_253_ = lean_ctor_get(v_x_252_, 0);
lean_inc_ref(v_elems_253_);
lean_dec_ref_known(v_x_252_, 1);
v_sz_254_ = lean_array_size(v_elems_253_);
v___x_255_ = ((size_t)0ULL);
v___x_256_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2_spec__3(v_sz_254_, v___x_255_, v_elems_253_);
return v___x_256_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_257_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0));
v___x_258_ = lean_unsigned_to_nat(80u);
v___x_259_ = l_Lean_Json_pretty(v_x_252_, v___x_258_);
v___x_260_ = lean_string_append(v___x_257_, v___x_259_);
lean_dec_ref(v___x_259_);
v___x_261_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1));
v___x_262_ = lean_string_append(v___x_260_, v___x_261_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
lean_object* v___x_267_; 
v___x_267_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_267_;
}
else
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2(v_x_266_);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(lean_object* v_j_286_, lean_object* v_k_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = l_Lean_Json_getObjValD(v_j_286_, v_k_287_);
v___x_289_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0___boxed(lean_object* v_j_290_, lean_object* v_k_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_j_290_, v_k_291_);
lean_dec_ref(v_k_291_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3(void){
_start:
{
uint8_t v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = 1;
v___x_300_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__2));
v___x_301_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_302_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_303_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__3);
v___x_304_ = lean_string_append(v___x_303_, v___x_302_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7(void){
_start:
{
uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = 1;
v___x_309_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__6));
v___x_310_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__7);
v___x_312_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4);
v___x_313_ = lean_string_append(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_315_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__8);
v___x_316_ = lean_string_append(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12(void){
_start:
{
uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = 1;
v___x_321_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__11));
v___x_322_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__12);
v___x_324_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__4);
v___x_325_ = lean_string_append(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_327_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__13);
v___x_328_ = lean_string_append(v___x_327_, v___x_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson(lean_object* v_json_329_){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__0));
lean_inc(v_json_329_);
v___x_331_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0(v_json_329_, v___x_330_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_341_; 
lean_dec(v_json_329_);
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_341_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_341_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_341_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__9);
v___x_337_ = lean_string_append(v___x_336_, v_a_332_);
lean_dec(v_a_332_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_337_);
v___x_339_ = v___x_334_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
else
{
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_json_329_);
v_a_342_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_331_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_331_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 0);
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_a_350_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_331_, 1);
v___x_351_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__10));
v___x_352_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_329_, v___x_351_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_a_350_);
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_362_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_362_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_362_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_357_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson___closed__14);
v___x_358_ = lean_string_append(v___x_357_, v_a_353_);
lean_dec(v_a_353_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_358_);
v___x_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec(v_a_350_);
v_a_363_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_352_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_352_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set_tag(v___x_365_, 0);
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_380_; 
v_a_371_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_380_ == 0)
{
v___x_373_ = v___x_352_;
v_isShared_374_ = v_isSharedCheck_380_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_352_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_380_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_378_; 
v___x_375_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_375_, 0, v_a_350_);
v___x_376_ = lean_unbox(v_a_371_);
lean_dec(v_a_371_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*1, v___x_376_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_378_ = v___x_373_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_375_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___impl(lean_object* v_x_383_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = lean_obj_tag_nat(v_x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___impl___boxed(lean_object* v_x_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorIdx___impl(v_x_385_);
lean_dec_ref(v_x_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(lean_object* v_t_387_, lean_object* v_k_388_){
_start:
{
if (lean_obj_tag(v_t_387_) == 0)
{
lean_object* v_range_389_; lean_object* v_text_390_; lean_object* v___x_391_; 
v_range_389_ = lean_ctor_get(v_t_387_, 0);
lean_inc_ref(v_range_389_);
v_text_390_ = lean_ctor_get(v_t_387_, 1);
lean_inc_ref(v_text_390_);
lean_dec_ref_known(v_t_387_, 2);
v___x_391_ = lean_apply_2(v_k_388_, v_range_389_, v_text_390_);
return v___x_391_;
}
else
{
lean_object* v_text_392_; lean_object* v___x_393_; 
v_text_392_ = lean_ctor_get(v_t_387_, 0);
lean_inc_ref(v_text_392_);
lean_dec_ref_known(v_t_387_, 1);
v___x_393_ = lean_apply_1(v_k_388_, v_text_392_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(lean_object* v_motive_394_, lean_object* v_ctorIdx_395_, lean_object* v_t_396_, lean_object* v_h_397_, lean_object* v_k_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_396_, v_k_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___boxed(lean_object* v_motive_400_, lean_object* v_ctorIdx_401_, lean_object* v_t_402_, lean_object* v_h_403_, lean_object* v_k_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim(v_motive_400_, v_ctorIdx_401_, v_t_402_, v_h_403_, v_k_404_);
lean_dec(v_ctorIdx_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim___redArg(lean_object* v_t_406_, lean_object* v_rangeChange_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_406_, v_rangeChange_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_rangeChange_elim(lean_object* v_motive_409_, lean_object* v_t_410_, lean_object* v_h_411_, lean_object* v_rangeChange_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_410_, v_rangeChange_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim___redArg(lean_object* v_t_414_, lean_object* v_fullChange_415_){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_414_, v_fullChange_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_fullChange_elim(lean_object* v_motive_417_, lean_object* v_t_418_, lean_object* v_h_419_, lean_object* v_fullChange_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Lsp_TextDocumentContentChangeEvent_ctorElim___redArg(v_t_418_, v_fullChange_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0(lean_object* v___x_424_, lean_object* v___x_425_, lean_object* v_j_426_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
lean_inc(v_j_426_);
v___x_448_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_426_, v___x_425_, v___x_447_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_dec_ref_known(v___x_448_, 1);
goto v___jp_427_;
}
else
{
lean_object* v_a_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v___x_448_, 1);
v___x_450_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
lean_inc_ref(v___x_424_);
lean_inc(v_j_426_);
v___x_451_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_426_, v___x_424_, v___x_450_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_dec_ref_known(v___x_451_, 1);
lean_dec(v_a_449_);
goto v___jp_427_;
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_460_; 
lean_dec(v_j_426_);
lean_dec_ref(v___x_424_);
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_460_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_460_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v_a_449_);
lean_ctor_set(v___x_456_, 1, v_a_452_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
v___jp_427_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_429_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_426_, v___x_424_, v___x_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_446_; 
v_a_438_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_446_ == 0)
{
v___x_440_ = v___x_429_;
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_429_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v_a_438_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_TextDocumentContentChangeEvent_hasToJson___lam__0(lean_object* v_o_467_){
_start:
{
if (lean_obj_tag(v_o_467_) == 0)
{
lean_object* v_range_468_; lean_object* v_text_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_485_; 
v_range_468_ = lean_ctor_get(v_o_467_, 0);
v_text_469_ = lean_ctor_get(v_o_467_, 1);
v_isSharedCheck_485_ = !lean_is_exclusive(v_o_467_);
if (v_isSharedCheck_485_ == 0)
{
v___x_471_ = v_o_467_;
v_isShared_472_ = v_isSharedCheck_485_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_text_469_);
lean_inc(v_range_468_);
lean_dec(v_o_467_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_485_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_473_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
v___x_474_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_468_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_474_);
lean_ctor_set(v___x_471_, 0, v___x_473_);
v___x_476_ = v___x_471_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v___x_474_);
v___x_476_ = v_reuseFailAlloc_484_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_477_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_478_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_478_, 0, v_text_469_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = lean_box(0);
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_479_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
v___x_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_476_);
lean_ctor_set(v___x_482_, 1, v___x_481_);
v___x_483_ = l_Lean_Json_mkObj(v___x_482_);
lean_dec_ref_known(v___x_482_, 2);
return v___x_483_;
}
}
}
else
{
lean_object* v_text_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_498_; 
v_text_486_ = lean_ctor_get(v_o_467_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v_o_467_);
if (v_isSharedCheck_498_ == 0)
{
v___x_488_ = v_o_467_;
v_isShared_489_ = v_isSharedCheck_498_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_text_486_);
lean_dec(v_o_467_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_498_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_492_; 
v___x_490_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
if (v_isShared_489_ == 0)
{
lean_ctor_set_tag(v___x_488_, 3);
v___x_492_ = v___x_488_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_text_486_);
v___x_492_ = v_reuseFailAlloc_497_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_490_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = l_Lean_Json_mkObj(v___x_495_);
lean_dec_ref_known(v___x_495_, 2);
return v___x_496_;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(size_t v_sz_501_, size_t v_i_502_, lean_object* v_bs_503_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = lean_usize_dec_lt(v_i_502_, v_sz_501_);
if (v___x_504_ == 0)
{
return v_bs_503_;
}
else
{
lean_object* v_v_505_; lean_object* v___x_506_; lean_object* v_bs_x27_507_; lean_object* v___y_509_; 
v_v_505_ = lean_array_uget(v_bs_503_, v_i_502_);
v___x_506_ = lean_unsigned_to_nat(0u);
v_bs_x27_507_ = lean_array_uset(v_bs_503_, v_i_502_, v___x_506_);
if (lean_obj_tag(v_v_505_) == 0)
{
lean_object* v_range_514_; lean_object* v_text_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_531_; 
v_range_514_ = lean_ctor_get(v_v_505_, 0);
v_text_515_ = lean_ctor_get(v_v_505_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_v_505_);
if (v_isSharedCheck_531_ == 0)
{
v___x_517_ = v_v_505_;
v_isShared_518_ = v_isSharedCheck_531_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_text_515_);
lean_inc(v_range_514_);
lean_dec(v_v_505_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_531_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_519_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
v___x_520_ = l_Lean_Lsp_instToJsonRange_toJson(v_range_514_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v___x_520_);
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_522_ = v___x_517_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_530_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_523_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_524_, 0, v_text_515_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_box(0);
v___x_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_522_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = l_Lean_Json_mkObj(v___x_528_);
lean_dec_ref_known(v___x_528_, 2);
v___y_509_ = v___x_529_;
goto v___jp_508_;
}
}
}
else
{
lean_object* v_text_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_544_; 
v_text_532_ = lean_ctor_get(v_v_505_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_v_505_);
if (v_isSharedCheck_544_ == 0)
{
v___x_534_ = v_v_505_;
v_isShared_535_ = v_isSharedCheck_544_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_text_532_);
lean_dec(v_v_505_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_544_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_538_; 
v___x_536_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
if (v_isShared_535_ == 0)
{
lean_ctor_set_tag(v___x_534_, 3);
v___x_538_ = v___x_534_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_text_532_);
v___x_538_ = v_reuseFailAlloc_543_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_536_);
lean_ctor_set(v___x_539_, 1, v___x_538_);
v___x_540_ = lean_box(0);
v___x_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = l_Lean_Json_mkObj(v___x_541_);
lean_dec_ref_known(v___x_541_, 2);
v___y_509_ = v___x_542_;
goto v___jp_508_;
}
}
}
v___jp_508_:
{
size_t v___x_510_; size_t v___x_511_; lean_object* v___x_512_; 
v___x_510_ = ((size_t)1ULL);
v___x_511_ = lean_usize_add(v_i_502_, v___x_510_);
v___x_512_ = lean_array_uset(v_bs_x27_507_, v_i_502_, v___y_509_);
v_i_502_ = v___x_511_;
v_bs_503_ = v___x_512_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_501_ = stack[0].m_num;
size_t v_i_502_ = stack[1].m_num;
lean_object* v_bs_503_ = stack[2].m_obj;
lean_object* v_res_545_;
v_res_545_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_501_, v_i_502_, v_bs_503_);
stack->m_obj
 = v_res_545_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0___boxed(lean_object* v_sz_546_, lean_object* v_i_547_, lean_object* v_bs_548_){
_start:
{
size_t v_sz_boxed_549_; size_t v_i_boxed_550_; lean_object* v_res_551_; 
v_sz_boxed_549_ = lean_unbox_usize(v_sz_546_);
lean_dec(v_sz_546_);
v_i_boxed_550_ = lean_unbox_usize(v_i_547_);
lean_dec(v_i_547_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_boxed_549_, v_i_boxed_550_, v_bs_548_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(lean_object* v_a_552_){
_start:
{
size_t v_sz_553_; size_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_sz_553_ = lean_array_size(v_a_552_);
v___x_554_ = ((size_t)0ULL);
v___x_555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0_spec__0(v_sz_553_, v___x_554_, v_a_552_);
v___x_556_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson(lean_object* v_x_558_){
_start:
{
lean_object* v_textDocument_559_; lean_object* v_contentChanges_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_580_; 
v_textDocument_559_ = lean_ctor_get(v_x_558_, 0);
v_contentChanges_560_ = lean_ctor_get(v_x_558_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_580_ == 0)
{
v___x_562_ = v_x_558_;
v_isShared_563_ = v_isSharedCheck_580_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_contentChanges_560_);
lean_inc(v_textDocument_559_);
lean_dec(v_x_558_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_580_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_564_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_565_ = l_Lean_Lsp_instToJsonVersionedTextDocumentIdentifier_toJson(v_textDocument_559_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 1, v___x_565_);
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_567_ = v___x_562_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_564_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v___x_565_);
v___x_567_ = v_reuseFailAlloc_579_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_568_ = lean_box(0);
v___x_569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0));
v___x_571_ = l_Lean_Array_toJson___at___00Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson_spec__0(v_contentChanges_560_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v___x_568_);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
lean_ctor_set(v___x_574_, 1, v___x_568_);
v___x_575_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_569_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_577_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_575_, v___x_576_);
v___x_578_ = l_Lean_Json_mkObj(v___x_577_);
lean_dec(v___x_577_);
return v___x_578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(lean_object* v_j_583_, lean_object* v_k_584_){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = l_Lean_Json_getObjValD(v_j_583_, v_k_584_);
v___x_586_ = l_Lean_Lsp_instFromJsonVersionedTextDocumentIdentifier_fromJson(v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_587_, lean_object* v_k_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_j_587_, v_k_588_);
lean_dec_ref(v_k_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(lean_object* v_j_590_, lean_object* v_k_591_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = l_Lean_Json_getObjValD(v_j_590_, v_k_591_);
v___x_593_ = l_Lean_Lsp_instFromJsonRange_fromJson(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3___boxed(lean_object* v_j_594_, lean_object* v_k_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_j_594_, v_k_595_);
lean_dec_ref(v_k_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(lean_object* v_j_597_, lean_object* v_k_598_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = l_Lean_Json_getObjValD(v_j_597_, v_k_598_);
v___x_600_ = l_Lean_Json_getStr_x3f(v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2___boxed(lean_object* v_j_601_, lean_object* v_k_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_j_601_, v_k_602_);
lean_dec_ref(v_k_602_);
return v_res_603_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(size_t v_sz_604_, size_t v_i_605_, lean_object* v_bs_606_){
_start:
{
uint8_t v___x_607_; 
v___x_607_ = lean_usize_dec_lt(v_i_605_, v_sz_604_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; 
v___x_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_608_, 0, v_bs_606_);
return v___x_608_;
}
else
{
lean_object* v_v_609_; lean_object* v___x_610_; lean_object* v_bs_x27_611_; lean_object* v_a_613_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_v_609_ = lean_array_uget(v_bs_606_, v_i_605_);
v___x_610_ = lean_unsigned_to_nat(0u);
v_bs_x27_611_ = lean_array_uset(v_bs_606_, v_i_605_, v___x_610_);
v___x_631_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__1));
lean_inc(v_v_609_);
v___x_632_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__3(v_v_609_, v___x_631_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_dec_ref_known(v___x_632_, 1);
goto v___jp_618_;
}
else
{
lean_object* v_a_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
lean_inc(v_v_609_);
v___x_635_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_609_, v___x_634_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_dec_ref_known(v___x_635_, 1);
lean_dec(v_a_633_);
goto v___jp_618_;
}
else
{
lean_object* v_a_636_; lean_object* v___x_637_; 
lean_dec(v_v_609_);
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v_a_633_);
lean_ctor_set(v___x_637_, 1, v_a_636_);
v_a_613_ = v___x_637_;
goto v___jp_612_;
}
}
v___jp_612_:
{
size_t v___x_614_; size_t v___x_615_; lean_object* v___x_616_; 
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_605_, v___x_614_);
v___x_616_ = lean_array_uset(v_bs_x27_611_, v_i_605_, v_a_613_);
v_i_605_ = v___x_615_;
v_bs_606_ = v___x_616_;
goto _start;
}
v___jp_618_:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_620_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__2(v_v_609_, v___x_619_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v_bs_x27_611_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_620_, 1);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v_a_629_);
v_a_613_ = v___x_630_;
goto v___jp_612_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_604_ = stack[0].m_num;
size_t v_i_605_ = stack[1].m_num;
lean_object* v_bs_606_ = stack[2].m_obj;
lean_object* v_res_638_;
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_604_, v_i_605_, v_bs_606_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4___boxed(lean_object* v_sz_639_, lean_object* v_i_640_, lean_object* v_bs_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_639_);
lean_dec(v_sz_639_);
v_i_boxed_643_ = lean_unbox_usize(v_i_640_);
lean_dec(v_i_640_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_boxed_642_, v_i_boxed_643_, v_bs_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_645_){
_start:
{
if (lean_obj_tag(v_x_645_) == 4)
{
lean_object* v_elems_646_; size_t v_sz_647_; size_t v___x_648_; lean_object* v___x_649_; 
v_elems_646_ = lean_ctor_get(v_x_645_, 0);
lean_inc_ref(v_elems_646_);
lean_dec_ref_known(v_x_645_, 1);
v_sz_647_ = lean_array_size(v_elems_646_);
v___x_648_ = ((size_t)0ULL);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1_spec__4(v_sz_647_, v___x_648_, v_elems_646_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_650_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__0));
v___x_651_ = lean_unsigned_to_nat(80u);
v___x_652_ = l_Lean_Json_pretty(v_x_645_, v___x_651_);
v___x_653_ = lean_string_append(v___x_650_, v___x_652_);
lean_dec_ref(v___x_652_);
v___x_654_ = ((lean_object*)(l_Lean_Array_fromJson_x3f___at___00Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__0_spec__0_spec__2___closed__1));
v___x_655_ = lean_string_append(v___x_653_, v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(lean_object* v_j_657_, lean_object* v_k_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = l_Lean_Json_getObjValD(v_j_657_, v_k_658_);
v___x_660_ = l_Lean_Array_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1_spec__1(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_661_, lean_object* v_k_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_j_661_, v_k_662_);
lean_dec_ref(v_k_662_);
return v_res_663_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = 1;
v___x_670_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__1));
v___x_671_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_670_, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_673_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__2);
v___x_674_ = lean_string_append(v___x_673_, v___x_672_);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_676_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3);
v___x_677_ = lean_string_append(v___x_676_, v___x_675_);
return v___x_677_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_678_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_679_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__4);
v___x_680_ = lean_string_append(v___x_679_, v___x_678_);
return v___x_680_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7(void){
_start:
{
uint8_t v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = 1;
v___x_684_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__6));
v___x_685_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_684_, v___x_683_);
return v___x_685_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8(void){
_start:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__7);
v___x_687_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__3);
v___x_688_ = lean_string_append(v___x_687_, v___x_686_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_689_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_690_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__8);
v___x_691_ = lean_string_append(v___x_690_, v___x_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson(lean_object* v_json_692_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
lean_inc(v_json_692_);
v___x_694_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__0(v_json_692_, v___x_693_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_json_692_);
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_704_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_704_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_704_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_699_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__5);
v___x_700_ = lean_string_append(v___x_699_, v_a_695_);
lean_dec(v_a_695_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_700_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
else
{
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec(v_json_692_);
v_a_705_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_694_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_694_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set_tag(v___x_707_, 0);
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v_a_713_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_694_, 1);
v___x_714_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidChangeTextDocumentParams_toJson___closed__0));
v___x_715_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson_spec__1(v_json_692_, v___x_714_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_a_713_);
v_a_716_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_725_ == 0)
{
v___x_718_ = v___x_715_;
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_715_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_725_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_720_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidChangeTextDocumentParams_fromJson___closed__9);
v___x_721_ = lean_string_append(v___x_720_, v_a_716_);
lean_dec(v_a_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_721_);
v___x_723_ = v___x_718_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
else
{
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec(v_a_713_);
v_a_726_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_715_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_715_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
lean_ctor_set_tag(v___x_728_, 0);
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_742_; 
v_a_734_ = lean_ctor_get(v___x_715_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_715_);
if (v_isSharedCheck_742_ == 0)
{
v___x_736_ = v___x_715_;
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_715_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_742_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_a_713_);
lean_ctor_set(v___x_738_, 1, v_a_734_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_738_);
v___x_740_ = v___x_736_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(lean_object* v_k_745_, lean_object* v_x_746_){
_start:
{
if (lean_obj_tag(v_x_746_) == 0)
{
lean_object* v___x_747_; 
lean_dec_ref(v_k_745_);
v___x_747_ = lean_box(0);
return v___x_747_;
}
else
{
lean_object* v_val_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_758_; 
v_val_748_ = lean_ctor_get(v_x_746_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v_x_746_);
if (v_isSharedCheck_758_ == 0)
{
v___x_750_ = v_x_746_;
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_val_748_);
lean_dec(v_x_746_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_758_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 3);
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_val_748_);
v___x_753_ = v_reuseFailAlloc_757_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_k_745_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_box(0);
v___x_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
return v___x_756_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson(lean_object* v_x_759_){
_start:
{
lean_object* v_textDocument_760_; lean_object* v_text_x3f_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_779_; 
v_textDocument_760_ = lean_ctor_get(v_x_759_, 0);
v_text_x3f_761_ = lean_ctor_get(v_x_759_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_779_ == 0)
{
v___x_763_ = v_x_759_;
v_isShared_764_ = v_isSharedCheck_779_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_text_x3f_761_);
lean_inc(v_textDocument_760_);
lean_dec(v_x_759_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_779_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_765_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_766_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_textDocument_760_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 1, v___x_766_);
lean_ctor_set(v___x_763_, 0, v___x_765_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_778_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_769_ = lean_box(0);
v___x_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_772_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonDidSaveTextDocumentParams_toJson_spec__0(v___x_771_, v_text_x3f_761_);
v___x_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___x_769_);
v___x_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_770_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_776_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_774_, v___x_775_);
v___x_777_ = l_Lean_Json_mkObj(v___x_776_);
lean_dec(v___x_776_);
return v___x_777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(lean_object* v_j_782_, lean_object* v_k_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = l_Lean_Json_getObjValD(v_j_782_, v_k_783_);
v___x_785_ = l_Lean_Lsp_instFromJsonTextDocumentIdentifier_fromJson(v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0___boxed(lean_object* v_j_786_, lean_object* v_k_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_j_786_, v_k_787_);
lean_dec_ref(v_k_787_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_791_) == 0)
{
lean_object* v___x_792_; 
v___x_792_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1___closed__0));
return v___x_792_;
}
else
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Json_getStr_x3f(v_x_791_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_810_; 
v_a_802_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_810_ == 0)
{
v___x_804_ = v___x_793_;
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_793_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_806_, 0, v_a_802_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(lean_object* v_j_811_, lean_object* v_k_812_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = l_Lean_Json_getObjValD(v_j_811_, v_k_812_);
v___x_814_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1_spec__1(v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1___boxed(lean_object* v_j_815_, lean_object* v_k_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_j_815_, v_k_816_);
lean_dec_ref(v_k_816_);
return v_res_817_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = 1;
v___x_824_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__1));
v___x_825_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_824_, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_827_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__2);
v___x_828_ = lean_string_append(v___x_827_, v___x_826_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_830_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3);
v___x_831_ = lean_string_append(v___x_830_, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_833_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__4);
v___x_834_ = lean_string_append(v___x_833_, v___x_832_);
return v___x_834_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8(void){
_start:
{
uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_838_ = 1;
v___x_839_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__7));
v___x_840_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_839_, v___x_838_);
return v___x_840_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_841_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__8);
v___x_842_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__3);
v___x_843_ = lean_string_append(v___x_842_, v___x_841_);
return v___x_843_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_845_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__9);
v___x_846_ = lean_string_append(v___x_845_, v___x_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson(lean_object* v_json_847_){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
lean_inc(v_json_847_);
v___x_849_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_847_, v___x_848_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_859_; 
lean_dec(v_json_847_);
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_859_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_859_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_859_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_854_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__5);
v___x_855_ = lean_string_append(v___x_854_, v_a_850_);
lean_dec(v_a_850_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_855_);
v___x_857_ = v___x_852_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_json_847_);
v_a_860_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_849_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_849_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set_tag(v___x_862_, 0);
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_a_868_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_849_, 1);
v___x_869_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentContentChangeEvent___lam__0___closed__0));
v___x_870_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__1(v_json_847_, v___x_869_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_880_; 
lean_dec(v_a_868_);
v_a_871_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_880_ == 0)
{
v___x_873_ = v___x_870_;
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_870_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_880_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_875_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10, &l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson___closed__10);
v___x_876_ = lean_string_append(v___x_875_, v_a_871_);
lean_dec(v_a_871_);
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_878_ = v___x_873_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
else
{
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_a_868_);
v_a_881_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_870_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_870_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set_tag(v___x_883_, 0);
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_897_; 
v_a_889_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_897_ == 0)
{
v___x_891_ = v___x_870_;
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_870_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_897_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v_a_868_);
lean_ctor_set(v___x_893_, 1, v_a_889_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_893_);
v___x_895_ = v___x_891_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
}
}
lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson(uint8_t v_x_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_902_ = ((lean_object*)(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0));
v___x_903_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_903_, 0, v_x_901_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_box(0);
v___x_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_905_);
v___x_908_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_909_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_907_, v___x_908_);
v___x_910_ = l_Lean_Json_mkObj(v___x_909_);
lean_dec(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT void l_Lean_Lsp_instToJsonSaveOptions_toJson_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_901_ = stack[0].m_num;
lean_object* v_res_911_;
v_res_911_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v_x_901_);
stack->m_obj
 = v_res_911_;
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonSaveOptions_toJson___boxed(lean_object* v_x_912_){
_start:
{
uint8_t v_x_29__boxed_913_; lean_object* v_res_914_; 
v_x_29__boxed_913_ = lean_unbox(v_x_912_);
v_res_914_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v_x_29__boxed_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(lean_object* v_j_917_, lean_object* v_k_918_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = l_Lean_Json_getObjValD(v_j_917_, v_k_918_);
v___x_920_ = l_Lean_Json_getBool_x3f(v___x_919_);
lean_dec(v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0___boxed(lean_object* v_j_921_, lean_object* v_k_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_j_921_, v_k_922_);
lean_dec_ref(v_k_922_);
return v_res_923_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = 1;
v___x_930_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__1));
v___x_931_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_930_, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_933_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__2);
v___x_934_ = lean_string_append(v___x_933_, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = 1;
v___x_938_ = ((lean_object*)(l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__4));
v___x_939_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_938_, v___x_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__5);
v___x_941_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__3);
v___x_942_ = lean_string_append(v___x_941_, v___x_940_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_944_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__6);
v___x_945_ = lean_string_append(v___x_944_, v___x_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonSaveOptions_fromJson(lean_object* v_json_946_){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_Lsp_instToJsonSaveOptions_toJson___closed__0));
v___x_948_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_946_, v___x_947_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_958_; 
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
v___x_953_ = lean_obj_once(&l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonSaveOptions_fromJson___closed__7);
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
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_948_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_948_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonDidCloseTextDocumentParams_toJson(lean_object* v_x_977_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_978_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_979_ = l_Lean_Lsp_instToJsonTextDocumentIdentifier_toJson(v_x_977_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_981_);
v___x_984_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_985_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_983_, v___x_984_);
v___x_986_ = l_Lean_Json_mkObj(v___x_985_);
lean_dec(v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2(void){
_start:
{
uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = 1;
v___x_995_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__1));
v___x_996_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_995_, v___x_994_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_998_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__2);
v___x_999_ = lean_string_append(v___x_998_, v___x_997_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8, &l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8_once, _init_l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__8);
v___x_1001_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__3);
v___x_1002_ = lean_string_append(v___x_1001_, v___x_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1004_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__4);
v___x_1005_ = lean_string_append(v___x_1004_, v___x_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson(lean_object* v_json_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__0));
v___x_1008_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonDidSaveTextDocumentParams_fromJson_spec__0(v_json_1006_, v___x_1007_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1018_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1018_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1018_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1013_ = lean_obj_once(&l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5, &l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonDidCloseTextDocumentParams_fromJson___closed__5);
v___x_1014_ = lean_string_append(v___x_1013_, v_a_1009_);
lean_dec(v_a_1009_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1014_);
v___x_1016_ = v___x_1011_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
else
{
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
v_a_1019_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1008_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1008_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
lean_ctor_set_tag(v___x_1021_, 0);
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
v_a_1027_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1008_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1008_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(lean_object* v_k_1037_, lean_object* v_x_1038_){
_start:
{
if (lean_obj_tag(v_x_1038_) == 0)
{
lean_object* v___x_1039_; 
lean_dec_ref(v_k_1037_);
v___x_1039_ = lean_box(0);
return v___x_1039_;
}
else
{
lean_object* v_val_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v_val_1040_ = lean_ctor_get(v_x_1038_, 0);
v___x_1041_ = lean_unbox(v_val_1040_);
v___x_1042_ = l_Lean_Lsp_instToJsonSaveOptions_toJson(v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1043_, 0, v_k_1037_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0___boxed(lean_object* v_k_1046_, lean_object* v_x_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(v_k_1046_, v_x_1047_);
lean_dec(v_x_1047_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(lean_object* v_x_1054_){
_start:
{
uint8_t v_openClose_1055_; uint8_t v_change_1056_; uint8_t v_willSave_1057_; uint8_t v_willSaveWaitUntil_1058_; lean_object* v_save_x3f_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___y_1067_; 
v_openClose_1055_ = lean_ctor_get_uint8(v_x_1054_, sizeof(void*)*1);
v_change_1056_ = lean_ctor_get_uint8(v_x_1054_, sizeof(void*)*1 + 1);
v_willSave_1057_ = lean_ctor_get_uint8(v_x_1054_, sizeof(void*)*1 + 2);
v_willSaveWaitUntil_1058_ = lean_ctor_get_uint8(v_x_1054_, sizeof(void*)*1 + 3);
v_save_x3f_1059_ = lean_ctor_get(v_x_1054_, 0);
v___x_1060_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0));
v___x_1061_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1061_, 0, v_openClose_1055_);
v___x_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1));
switch(v_change_1056_)
{
case 0:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__1);
v___y_1067_ = v___x_1088_;
goto v___jp_1066_;
}
case 1:
{
lean_object* v___x_1089_; 
v___x_1089_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__3);
v___y_1067_ = v___x_1089_;
goto v___jp_1066_;
}
default: 
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_obj_once(&l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5, &l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5_once, _init_l_Lean_Lsp_instToJsonTextDocumentSyncKind___lam__0___closed__5);
v___y_1067_ = v___x_1090_;
goto v___jp_1066_;
}
}
v___jp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_inc(v___y_1067_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1065_);
lean_ctor_set(v___x_1068_, 1, v___y_1067_);
v___x_1069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1063_);
v___x_1070_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2));
v___x_1071_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1071_, 0, v_willSave_1057_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1063_);
v___x_1074_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3));
v___x_1075_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_1075_, 0, v_willSaveWaitUntil_1058_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_1063_);
v___x_1078_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4));
v___x_1079_ = l_Lean_Json_opt___at___00Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson_spec__0(v___x_1078_, v_save_x3f_1059_);
v___x_1080_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_1063_);
v___x_1081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1077_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1073_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1069_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1064_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = ((lean_object*)(l_Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson___closed__1));
v___x_1086_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonDidOpenTextDocumentParams_toJson_spec__0(v___x_1084_, v___x_1085_);
v___x_1087_ = l_Lean_Json_mkObj(v___x_1086_);
lean_dec(v___x_1086_);
return v___x_1087_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___boxed(lean_object* v_x_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson(v_x_1091_);
lean_dec_ref(v_x_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(lean_object* v_x_1097_){
_start:
{
if (lean_obj_tag(v_x_1097_) == 0)
{
lean_object* v___x_1098_; 
v___x_1098_ = ((lean_object*)(l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0___closed__0));
return v___x_1098_;
}
else
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Lsp_instFromJsonSaveOptions_fromJson(v_x_1097_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1116_; 
v_a_1108_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1110_ = v___x_1099_;
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1099_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v_a_1108_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1112_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(lean_object* v_j_1117_, lean_object* v_k_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = l_Lean_Json_getObjValD(v_j_1117_, v_k_1118_);
v___x_1120_ = l_Lean_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0_spec__0(v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0___boxed(lean_object* v_j_1121_, lean_object* v_k_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_j_1121_, v_k_1122_);
lean_dec_ref(v_k_1122_);
return v_res_1123_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2(void){
_start:
{
uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = 1;
v___x_1130_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__1));
v___x_1131_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__5));
v___x_1133_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__2);
v___x_1134_ = lean_string_append(v___x_1133_, v___x_1132_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5(void){
_start:
{
uint8_t v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = 1;
v___x_1138_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__4));
v___x_1139_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__5);
v___x_1141_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1142_ = lean_string_append(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1144_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__6);
v___x_1145_ = lean_string_append(v___x_1144_, v___x_1143_);
return v___x_1145_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9(void){
_start:
{
uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = 1;
v___x_1149_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__8));
v___x_1150_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1149_, v___x_1148_);
return v___x_1150_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__9);
v___x_1152_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1153_ = lean_string_append(v___x_1152_, v___x_1151_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1155_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__10);
v___x_1156_ = lean_string_append(v___x_1155_, v___x_1154_);
return v___x_1156_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13(void){
_start:
{
uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1159_ = 1;
v___x_1160_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__12));
v___x_1161_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1160_, v___x_1159_);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__13);
v___x_1163_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1164_ = lean_string_append(v___x_1163_, v___x_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1166_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__14);
v___x_1167_ = lean_string_append(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17(void){
_start:
{
uint8_t v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = 1;
v___x_1171_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__16));
v___x_1172_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1171_, v___x_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__17);
v___x_1174_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1175_ = lean_string_append(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1177_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__18);
v___x_1178_ = lean_string_append(v___x_1177_, v___x_1176_);
return v___x_1178_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22(void){
_start:
{
uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = 1;
v___x_1183_ = ((lean_object*)(l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__21));
v___x_1184_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1183_, v___x_1182_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__22);
v___x_1186_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__3);
v___x_1187_ = lean_string_append(v___x_1186_, v___x_1185_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = ((lean_object*)(l_Lean_Lsp_instFromJsonDidOpenTextDocumentParams_fromJson___closed__10));
v___x_1189_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__23);
v___x_1190_ = lean_string_append(v___x_1189_, v___x_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson(lean_object* v_json_1191_){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__0));
lean_inc(v_json_1191_);
v___x_1193_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1191_, v___x_1192_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_json_1191_);
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1203_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1203_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1198_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__7);
v___x_1199_ = lean_string_append(v___x_1198_, v_a_1194_);
lean_dec(v_a_1194_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1199_);
v___x_1201_ = v___x_1196_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_json_1191_);
v_a_1204_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1193_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1193_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 0);
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_a_1212_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1213_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__1));
lean_inc(v_json_1191_);
v___x_1214_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentChangeRegistrationOptions_fromJson_spec__1(v_json_1191_, v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1212_);
lean_dec(v_json_1191_);
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1224_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1224_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1219_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__11);
v___x_1220_ = lean_string_append(v___x_1219_, v_a_1215_);
lean_dec(v_a_1215_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1220_);
v___x_1222_ = v___x_1217_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_a_1212_);
lean_dec(v_json_1191_);
v_a_1225_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1214_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1214_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set_tag(v___x_1227_, 0);
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_a_1233_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1214_, 1);
v___x_1234_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__2));
lean_inc(v_json_1191_);
v___x_1235_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1191_, v___x_1234_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1245_; 
lean_dec(v_a_1233_);
lean_dec(v_a_1212_);
lean_dec(v_json_1191_);
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1245_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1245_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; 
v___x_1240_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__15);
v___x_1241_ = lean_string_append(v___x_1240_, v_a_1236_);
lean_dec(v_a_1236_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1241_);
v___x_1243_ = v___x_1238_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
else
{
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec(v_a_1233_);
lean_dec(v_a_1212_);
lean_dec(v_json_1191_);
v_a_1246_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1235_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1235_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set_tag(v___x_1248_, 0);
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_a_1254_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1235_, 1);
v___x_1255_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__3));
lean_inc(v_json_1191_);
v___x_1256_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonSaveOptions_fromJson_spec__0(v_json_1191_, v___x_1255_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v_a_1254_);
lean_dec(v_a_1233_);
lean_dec(v_a_1212_);
lean_dec(v_json_1191_);
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1266_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1266_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1261_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__19);
v___x_1262_ = lean_string_append(v___x_1261_, v_a_1257_);
lean_dec(v_a_1257_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1262_);
v___x_1264_ = v___x_1259_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1262_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
else
{
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_a_1254_);
lean_dec(v_a_1233_);
lean_dec(v_a_1212_);
lean_dec(v_json_1191_);
v_a_1267_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1256_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1256_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 0);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_a_1275_ = lean_ctor_get(v___x_1256_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1256_, 1);
v___x_1276_ = ((lean_object*)(l_Lean_Lsp_instToJsonTextDocumentSyncOptions_toJson___closed__4));
v___x_1277_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson_spec__0(v_json_1191_, v___x_1276_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1287_; 
lean_dec(v_a_1275_);
lean_dec(v_a_1254_);
lean_dec(v_a_1233_);
lean_dec(v_a_1212_);
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1287_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1282_ = lean_obj_once(&l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24, &l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24_once, _init_l_Lean_Lsp_instFromJsonTextDocumentSyncOptions_fromJson___closed__24);
v___x_1283_ = lean_string_append(v___x_1282_, v_a_1278_);
lean_dec(v_a_1278_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1283_);
v___x_1285_ = v___x_1280_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
else
{
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_a_1275_);
lean_dec(v_a_1254_);
lean_dec(v_a_1233_);
lean_dec(v_a_1212_);
v_a_1288_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1277_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1277_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 0);
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
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
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1308_; 
v_a_1296_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1298_ = v___x_1277_;
v_isShared_1299_ = v_isSharedCheck_1308_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1277_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1308_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; uint8_t v___x_1301_; uint8_t v___x_1302_; uint8_t v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1306_; 
v___x_1300_ = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(v___x_1300_, 0, v_a_1296_);
v___x_1301_ = lean_unbox(v_a_1212_);
lean_dec(v_a_1212_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*1, v___x_1301_);
v___x_1302_ = lean_unbox(v_a_1233_);
lean_dec(v_a_1233_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*1 + 1, v___x_1302_);
v___x_1303_ = lean_unbox(v_a_1254_);
lean_dec(v_a_1254_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*1 + 2, v___x_1303_);
v___x_1304_ = lean_unbox(v_a_1275_);
lean_dec(v_a_1275_);
lean_ctor_set_uint8(v___x_1300_, sizeof(void*)*1 + 3, v___x_1304_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1300_);
v___x_1306_ = v___x_1298_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1300_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
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
lean_object* runtime_initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Lsp_TextSync(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Lsp_TextSync(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Lsp_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Lsp_TextSync(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_TextSync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Lsp_TextSync(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Lsp_TextSync(builtin);
}
#ifdef __cplusplus
}
#endif
